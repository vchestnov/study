(* ::Section:: *)
(*Examples of `FiniteFlow` usage*)

Get["FiniteFlow`"]
Get["utils.m"]

(* ::Subsection:: *)
(*FFAlgMatMul and FFAlgLaurent*)

Module[
    {mat1, mat2, dims1, dims2, main, exp, explearn, params, res, expmax, min, max, nvals},
    mat1 = {{1 / (dd + z3), 0, 1}, {0, 1 / dd + 42, z3 dd}} // Together;
    mat2 = {
        {(dd + z3)^2, 0, 1 / dd, 0},
        {0, 1 / dd + 42, z3 dd, z3},
        {0, 0, (dd + 1)^2, 0},
        Nothing
    } // Together;
    {dims1, dims2} = {mat1, mat2} // Map[Dimensions];
    expmax = 3;
    params = {dd, z3};
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "vals1", {"in"}, params, mat1 // Flatten];
    FFAlgRatFunEval[main, "vals2", {"in"}, params, mat2 // Flatten];
    FFAlgMatMul[main, "mult", {"vals1", "vals2"}, dims1[[1]], dims1[[2]], dims2[[2]]];
    FFGraphOutput[main, "mult"];
    FFNewGraph[exp, "in", params[[2;;]]];
    FFAlgLaurent[exp, "laurent", {"in"}, main, expmax];
    FFGraphOutput[exp, "laurent"];
    explearn = FFLaurentLearn[exp];
    {min, max} = zipWith[{Min, Max}, explearn];
    (* nvals = FFGraphEvaluate[exp, {10^2}]; *)
    res = FFReconstructFunction[exp, params[[2;;]], "PrintDebugInfo" -> 1];
    FFLaurentSol[res, dd, explearn] // ArrayReshape[#, {dims1[[1]], dims2[[2]]}]& // MatrixForm
]

Module[
    {params, explearn, nzlearn},
    params = {dd, z3};
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "vals", {"in"}, params, {dd^2 z3 / (1 + dd)}];
    FFGraphOutput[main, "vals"];
    FFNewGraph[exp, "in", params[[2;;]]];
    FFAlgLaurent[exp, "laurent", {"in"}, main, 1];
    FFGraphOutput[exp, "laurent"];
    explearn = FFLaurentLearn[exp];
    FFAlgNonZeroes[exp, "nz", {"laurent"}];
    FFGraphOutput[exp, "nz"];
    nzlearn = FFNonZeroesLearn[exp];
    res = FFReconstructFunction[exp, params[[2;;]], "PrintDebugInfo" -> 1];
    FFLaurentSol[FFNonZeroesSol[res, nzlearn] // Normal, dd, explearn]
]

(* ::Subsection:: *)
(*Outer using FFAlgMatMul*)

Module[{main, mat1, mat2, params, dims1, dims2, ans, sol},
    mat1 = Range[10] // ArrayReshape[#, {2, 5}]&;
    mat2 = Array[a /* ind2sym, {2, 2}];
    ans = Outer[Times, mat1, mat2];
    {dims1, dims2} = {mat1, mat2} // Map[Dimensions];
    params = mat2 // Flatten;
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "mat1", {"in"}, params, mat1 // Flatten];
    FFAlgRatFunEval[main, "mat2", {"in"}, params, mat2 // Flatten];
    FFAlgMatMul[
        main, "mult", {"mat1", "mat2"},
        dims1 // Apply[Times],
        1,
        dims2 // Apply[Times]
    ];
    FFGraphOutput[main, "mult"];
    sol = FFReconstructFunction[main, params] // ArrayReshape[#, Join[dims1, dims2]]&;
    SameQ[ans, sol]
]

(* ::Subsection:: *)
(*FFAlgSparseSolver*)

Module[{main, eqs, vars, params, learn, nsol, sol},
    params = {z, eps};
    vars = {f[1], f[2]};
    eqs = {
        {eps z / (z + 1), z^2 / (eps + z)},
        {1 / eps, z^2 + eps}
    } // RightComposition[
        Dot[#, vars]&,
        Equal[#, {1 / z, eps}]&,
        Thread,
        Identity
    ];
    FFNewGraph[main, "in", params];
    FFAlgSparseSolver[
        main, "eqs", {"in"}, params,
        eqs,
        vars,
        "NeededVars" -> {f[1]}
    ];
    FFSolverSparseOutput[main, "eqs"];
    FFGraphOutput[main, "eqs"];
    learn = FFSparseSolverLearn[main, vars];
    nsol = FFGraphEvaluate[
        main,
        params // Length // RandomInteger[2^{30, 60}, #]&
    ] // TM["nsol"];
    (* FFSparseSolverSol[nsol, learn] *)
    sol = FFReconstructFunction[main, params, "PrintDebugInfo" -> 1]
    (* FFSparseSolverSol[sol, learn] *)
]

Module[{main, eqs, vars, params, learn, nsol, sol},
    params = {z, eps};
    eqs = {
        {1, 0, eps z, 0,     0, 0,   0},
        {0, 1, z^2,   z,     42, 0,   0},
        {0, 0, z,     1,     0, eps, 1 / z},
        {0, 0, 0,     1 / z, 0, 0,   eps^2},
        Nothing
    };
    (* eqs // rowReduce // mS *)
    vars = eqs // Dimensions // Last // Range // Map[f];
    FFNewGraph[main, "in", params];
    FFAlgSparseSolver[
        main, "eqs", {"in"}, params,
        Thread[eqs . vars == 0],
        vars,
        "NeededVars" -> {f[1], f[2]}
    ];
    FFSolverSparseOutput[main, "eqs"];
    FFGraphOutput[main, "eqs"];
    learn = FFSparseSolverLearn[main, vars];
    (* nsol = FFGraphEvaluate[ *)
    (*     main, *)
    (*     params // Length // RandomInteger[2^{30, 60}, #]& *)
    (* ] // TM["nsol"]; *)
    (* (1* FFSparseSolverSol[nsol, learn] *1) *)
    sol = FFReconstructFunction[main, params, "PrintDebugInfo" -> 1];
    FFSparseSolverSol[sol, learn]
    (* Internal`PartitionRagged[sol, learn[[2, 2]] // Map[Length]] *)
    (* Inner[Map[Prepend[#1], #2]&, learn[[1, 2]], learn[[2, 2]], List] *)
]

(* ::Subsection:: *)
(*FFAlgNodeDenseSolver*)

Module[{main, A, b, vars, params, learn, nsol, sol},
    params = {z, eps};
    vars = {f[1], f[2]};
    A = Join[{
        {eps z / (z + 1), z^2 / (eps + z)},
        {0, z^2 + eps}
    }, {1 / z, eps} // List // Transpose, 2];
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "vals", {"in"}, params, A // Flatten];
    FFAlgNodeDenseSolver[main, "solver", {"vals"}, 2, vars];
    FFGraphOutput[main, "solver"];
    learn = FFDenseSolverLearn[main, vars];
    sol = FFReconstructFunction[main, params, "PrintDebugInfo" -> 1];
    FFDenseSolverSol[sol, learn]
    (* nsol = FFGraphEvaluate[ *)
    (*     main, *)
    (*     params // Length // RandomInteger[2^{30, 60}, #]& *)
    (* ] // TM["nsol"] *)
]

(* ::Subsection:: *)
(*FFAlgTake*)

Module[{main, row, data, params, learn, nsol, sol},
    params = {a, b};
    row = {1, a, b};
    data["vals"] = {1, 2, 3};
    (* `MatrixForm` this one below! *)
    data["take"] = Range[0, 2] // Map[PadLeft[data["vals"], 5, 0, #]&] // Reverse // SparseArray;
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "vals", {"in"}, params, row];
    (* Here the last argument is the key *)
    FFAlgTake[main, "take", {"vals"}, data["take"]["NonzeroValues"] // Thread[{1, #}]&];
    FFGraphOutput[main, "take"];
    (* `sol` here will have only the non-zero values *)
    sol = FFReconstructFunction[main, params, "PrintDebugInfo" -> 1];
    (* Reconstruct the full matrix form *)
    data["take"] // RightComposition[
        ArrayRules,
        Most,
        Part[#, All, 1]&,
        Thread[# -> sol]&,
        SparseArray,
        Identity
    ] // MatrixForm
]

(* ::Subsection:: *)
(*FFAlgNodeSparseSolver*)

Module[{main, A, b, vars, params, learn, nsol, sol},
    params = {z, eps};
    vars = {f[1], f[2]};
    A = Join[{
        {eps, z^2 / (eps + z)},
        {0, z^2 + eps}
    }, {1 / z, eps} // List // Transpose, 2];
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "vals", {"in"}, params, A // Flatten // DeleteCases[0]];
    (* FFAlgNodeSparseSolver[main, "solver", {"vals"}, {{1, 2, 3}, {}, {2, 3}}, vars, "NeededVars" -> {f[2]}]; *)
    FFAlgNodeSparseSolver[main, "solver", {"vals"}, {{1, 2, 3}, {}, {2, 3}}, {1, 2}, "NeededVars" -> {2}];
    FFGraphOutput[main, "solver"];
    learn = FFSparseSolverLearn[main, {"hehe", "haha"}];
    sol = FFReconstructFunction[main, params, "PrintDebugInfo" -> 1];
    FFSparseSolverSol[sol, learn]
]

(* ::Subsection:: *)
(*FFAlgTakeAndAdd example*)

Module[{main, params},
    params = {eps, eps1, eps2, eps3};
    FFNewGraph[main, "in", params];
    (* FFAlgRatFunEval[main, "vals", {"in"}, params, {1 / eps + eps, eps^2 - 42, 42 eps} // Together]; *)
    FFAlgRatFunEval[main, "vals", {"in"}, params, {eps1, eps2, eps3} // Together];
    FFAlgRatFunEval[main, "vals2", {"in"}, params, {eps eps1, eps eps2, eps eps3} // Together];
    (* FFGraphOutput[main, "vals"]; *)
    FFAlgTake[main, "take", {"vals"}, {{f[1], f[2], f[3]}} -> {f[3], f[2], f[1]}];
    (* FFGraphOutput[main, "take"]; *)
    FFAlgMul[main, "mult", {"take", "vals"}];
    FFGraphOutput[main, "mult"];
    (* FFAlgAdd[main, "add", {"take", "vals"}]; *)
    (* FFGraphOutput[main, "add"]; *)
    (* FFAlgChain[main, "chain", {"mult", "vals"}]; *)
    (* FFGraphOutput[main, "chain"]; *)
    (* FFAlgTakeAndAdd[main, "takeadd", {"take"}, {{f[1]}, {f[2]}, {f[3]}}]; *)
    (* FFAlgTakeAndAdd[main, "takeadd", {"mult", "vals"}, {{f[1], f[2], f[3]}} -> {f[1], f[2], f[3]}]; *)
    FFAlgTakeAndAdd[main, "takeadd", {"vals", "vals2"}, {
        {{1, 1}, {1, 2}, {1, 3}, {2, 1}},
        {{1, 3}, {2, 2}}
    }];
    FFGraphOutput[main, "takeadd"];
    res = FFReconstructFunction[main, params];
    FFDeleteGraph[main];
    res
]

(* ::Subsection:: *)
(*FFAlgRatFunEval issue*)

Module[{main, params},
    params = {};
    FFNewGraph[main, "in", params];
    (* (1* This crashes `Mathematica` *1) *)
    (* FFAlgRatFunEval[main, "vals", {"in"}, params, {42}] *)
    FFAlgRatNumEval[main, "vals", {42}];
    FFGraphOutput[main, "vals"];
    res = FFReconstructNumeric[main]
]

Module[{main, params, test},
    FFNewGraph[main, "in", Range[1]];
    FFAlgRatFunEval[main, "slice", {"in"}, {freeparam}, {42, freeparam^2}];
    FFAlgRatFunEval[main, "system", {"slice"}, {x, y}, {x + y}];
    FFGraphOutput[main, "system"];
    FFReconstructFunction[main, {whatever}]
]

(* ::Subsection:: *)
(*Derivative using `FFAlgLaurent`*)

fun = (a + 42 + z)^5 / (z^2 (z + 1)^3);
dfun = Module[{main, params, shift, exp, learn},
    params = {h, z, a};
    FFNewGraph[main, "in", params[[2;;]]];
    FFAlgRatFunEval[main, "vals", {"in"}, params[[2;;]], {fun}];
    FFGraphOutput[main, "vals"];
    (* FFReconstructFunction[main, params[[;;2]]] *)
    FFNewGraph[shift, "in", params];
    FFAlgRatFunEval[shift, "shift z", {"in"}, params, {z + h, a}];
    FFAlgSimpleSubgraph[shift, "vals", {"shift z"}, main];
    FFGraphOutput[shift, "vals"];
    (* FFReconstructFunction[shift, params]; *)
    FFNewGraph[exp, "in", params[[2;;]]];
    FFAlgLaurent[exp, "laurent", {"in"}, shift, 1];
    FFGraphOutput[exp, "laurent"];
    learn = FFLaurentLearn[exp];
    FFReconstructFunction[exp, params[[2;;]]] // Last
];
dfun - D[fun, z] // Simplify // SameQ[#, 0]&

(* ::Subsection:: *)
(*Numerical slices using FFAlgRatFunEval (unfinished)*)

FFNewGraph[main, "in", Range[1]];
FFAlgRatFunEval[main, "slice", {"in"}, {freeparam}, {42, freeparam^2}];
FFAlgRatFunEval[main, "system", {"slice"}, {x, y}, {x + y}];
FFGraphOutput[main, "system"];
FFReconstructFunction[main, {whatever}]

(* ::Subsection:: *)
(*FFAlgMul*)

Module[
    {main, params, list, val},
    params = {x, y, z};
    list = {(x^2 + y) / (x + y), y / (x + y^2)};
    val = z;
    FFNewGraph[main, "in", params];
    FFAlgRatFunEval[main, "list", {"in"}, params, list];
    FFAlgRatFunEval[main, "val", {"in"}, params, {val}];
    FFAlgTake[main, "take", {"val"}, {{1, 1}, {1, 1}}];
    FFAlgMul[main, "mul", {"list", "take"}];
    FFGraphOutput[main, "mul"];
    FFReconstructFunction[main, params]
]
