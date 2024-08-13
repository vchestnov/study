(* ::Package:: *)

(* ::Section:: *)
(*tools*)


(* ::Subsection::Closed:: *)
(*Multiply*)


Multiply[xs__] = Times[xs, #]&;



(* ::Subsection::Closed:: *)
(*subjs*)


subjs::usage = "Substitute `vars` using the `j`-notation."
subjs[vars_List] := RightComposition[
    Collect[#, vars, $coeff]&,
    Expand,
    ReplaceAll[$coeff[h_] mon_. :> Times[h, mon // Exponent[#, vars]& // Apply[$j]]],
    Identity
];
subjs[var_] := subjs[{var}];



(* ::Subsection::Closed:: *)
(*stds*)


ClearAll @ stds;
stds::usage = "stds[gb, vars] for a Groebner basis `gb` in vars `vars` compute the standard (aka irreducible) monomials."
Options @ stds = {
    "MonomialOrder" -> DegreeLexicographic,
    Nothing
};
(*
 * Adapted `CanonicalAndDualBases` function from the `MultivariateResidue.m` package
 * released under GPL-3.0 license
 * https://bitbucket.org/kjlarsen/multivariateresidues/
 * https://arxiv.org/abs/1701.01040
 *)
stds[gb_List, vars_List, opts:OptionsPattern[]] := stds[gb, vars, opts] = Module[{leadingexps, maxexp, basis},
    leadingexps = MonomialList[gb, vars, OptionValue["MonomialOrder"]][[All, 1]] // Map[Exponent[#, vars]&];
    maxexp = leadingexps // Flatten // Max;
    basis = leadingexps // RightComposition[
        Map[Function[exp,
            Select[
                Tuples[Range[0, maxexp], {Length[vars]}],
                Thread[Less[#, exp]]& /* Apply[Or]
            ]
        ]],
        Apply[Intersection],
        Map[vars^#& /* Apply[Times]],
        Total,
        MonomialList[#, vars, OptionValue["MonomialOrder"]]&,
        Reverse,
        Identity
    ]
];
stds[args__] := Error[MkString["Wrong arguments: ", {args} // InputForm]];



(* ::Subsection:: *)
(*cmat*)


ClearAll @ cmat;
cmat::usage = "cmat[gb, vars][fun] for a Groebner basis `gb` in vars `vars` compute the companion matrix representation of function `fun`."
cmat[gb_List, vars_List][fun_] := stds[gb, vars] // RightComposition[
    Map[fun],
    Map[PolynomialReduce[#, gb, vars]&],
    Part[#, All, 2]&,
    subjs[vars],
    CoefficientArrays[#, stds[gb, vars] // subjs[vars]]&,
    Switch[Length[#],
        2, # // Last,
        1, SparseArray[{}, # // Last // Length // {#, #}&],
        _, Error["wrong dimension in cmat"]
    ]&,
    Transpose,
    Identity
];
cmat[args__][_] := Error[MkString["Wrong arguments: ", {args} // InputForm]];


(* ::Section:: *)
(*examples*)


(* ::Subsection:: *)
(*univariate*)


gb1   = {(x - 1)^2 - a};
vars1 = {x};


(* there are two irreducible monomials *)
stds[gb1, vars1]


(* `1` is represented by the identity matrix *)
cOne1 = cmat[gb1, vars1][Multiply[1]];
cOne1 // MatrixForm


(* multiplication by `x` is more interesting *)
cx = cmat[gb1, vars1][Multiply[x]];
cx // MatrixForm


(* multiplication by `x^2` is similar *)
cx2 = cmat[gb1, vars1][Multiply[x^2]];
cx2 // MatrixForm


(* the two ways to represent multiplication by `x^2` *)
cx2 - cx . cx // Flatten // Normal // Expand // ContainsOnly[{0}]


(* division is inversion! *)
cInvx = cmat[gb1, vars1][Multiply[x]] // Inverse;
cInvx // MatrixForm


(* algebra still works *)
cx . cInvx - cOne1 // Normal // Simplify // Flatten // ContainsOnly[{0}]

cx . cInvx - cInvx . cx // Normal // Simplify // Flatten // ContainsOnly[{0}]


(* check against polynomial division *)
{
    (* NOTE make sure you understand this line! *)
    stds[gb1, vars1] . cInvx . {1, 0}//Factor,
    PolynomialRemainder[1 / x, gb1[[1]], x]//Factor
} // Expand // Apply[SameQ]


(* ::Subsubsection:: *)
(*caveat*)


(* limit `a -> 0` makes some companion matrices non-invertible *)
cBad = cmat[gb1 // ReplaceAll[a -> 0], vars1][Multiply[x - 1]]

cBad // Det


(* which corresponds to the `1 / a` pole in the original matrix *)
cmat[gb1, vars1][Multiply[x - 1]] // Inverse // Series[#, {a, 0, -1}]& // Normal


(* ::Subsection:: *)
(*2-variate*)


vars2 = {y, z};
gb2   = GroebnerBasis[
    {
        (y - z)^2 - a,
        (z - 1)^2,
        Nothing
    },
    vars2,
    MonomialOrder -> DegreeLexicographic,
    CoefficientDomain -> RationalFunctions
];


(* there are 4 irreducible monomials *)
stds[gb2, vars2]


(* `1` is still the identity matrix *)
cOne2 = cmat[gb2, vars2][Multiply[1]];
cOne2//MatrixForm


(* the two basic companion matrices for multiplication operators *)
cy = cmat[gb2, vars2][Multiply[y]];
cz = cmat[gb2, vars2][Multiply[z]];
cy//MatrixForm
cz//MatrixForm


(* the matrices commute! *)
cy . cz - cz . cy // Flatten // ContainsOnly[{0}]


(* polynomial algebra works the same way *)
cPoly = cmat[gb2, vars2][Multiply[1 + y^2 + z^2]];


cPoly - (cOne2 + cy . cy + cz . cz) // Normal // Simplify // Flatten // ContainsOnly[{0}]


(* division is still inverse *)
cDen = cmat[gb2, vars2][Multiply[y + z]] // Inverse;


(cy + cz) . cDen - cOne2 // Normal // Simplify // Flatten // ContainsOnly[{0}]


(* check against polynomial division *)
PolynomialReduce[
    (* NOTE make sure you understand this line! *)
    (y + z) (stds[gb2, vars2] . cDen . {1, 0, 0, 0}) - 1,
    gb2,
    vars2,
    MonomialOrder -> DegreeLexicographic
] // Last // SameQ[#, 0]&
