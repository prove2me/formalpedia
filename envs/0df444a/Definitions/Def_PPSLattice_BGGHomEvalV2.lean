-- Prove2me | Definitions.Def_PPSLattice_BGGHomEvalV2
-- name    : PPSLattice_BGGHomEvalV2
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:27.774088+00:00
-- url     : https://prove2.me/theorems/a5e09e08-9a44-4340-bff7-2b89ddcd3d28
-- title:
--   Prefix-consistent BGG+ homomorphic evaluation for NAND circuits
-- statement:
--   This module repairs the wire traversal in the explicit BGG+ evaluator. At each NAND gate, the public matrices $\mathbf B_w$, evaluation matrices $\mathbf H_w$, and Boolean wire values $x_w$ are updated together from the same prefix. Thus the recurrence uses $\mathbf G^{-1}(\mathbf B_b)$ for the value of $\mathbf B_b$ before the gate, including the zero-value convention for unavailable forward references. The public recurrence is
--   $$\mathbf B_{\mathrm{out}}=\mathbf G-\mathbf B_a\mathbf G^{-1}(\mathbf B_b),$$
--   and the evaluation recurrence is
--   $$\mathbf H_{\mathrm{out}}=-\mathbf H_a\mathbf G^{-1}(\mathbf B_b)-x_a\mathbf H_b.$$
--   Input wires use consecutive matrix blocks and block selectors. `evalF` and `evalFX` select the designated output wire, with the same $n=0$ convention as before.
--
--   The earlier evaluator computed its public prefixes correctly but accidentally read $\mathbf B_b$ from the final public list in the evaluation traversal. This definition makes the intended GSW13/BGG+14 recurrence explicit and consistent for every straight-line program accepted by `RestrictedDec.Circuit.eval`.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, Homomorphic Computation, pp.16–17; standard GSW13/BGG+14 NAND evaluation. Repair of Definitions.Def_PPSLattice_BGGHomEval after the finite counterexample q=3,n=ell=1,m=2,B=[0,1],x=[false],gates=[(0,1)],outs=[1].

import Mathlib
import Definitions.Def_PPSLattice_HomEval
import Definitions.Def_PPSLattice_BGGHomEval
set_option autoImplicit false

namespace PPSLattice

/-- The three wire lists maintained simultaneously by the BGG+ traversal. -/
structure BGGFoldState (q n m ell : ℕ) where
  wireMatrices : List (Matrix (Fin n) (Fin m) (ZMod q))
  evalMatrices : List (Matrix (Fin (ell * m)) (Fin m) (ZMod q))
  wireValues : List Bool

/-- Evaluation matrices for all wires, computed in lockstep with the public matrices and Boolean values. The public matrix used by a NAND gate is read from the *prefix* before that gate, exactly as in `bggWireMatrices` and `RestrictedDec.Circuit.eval`. -/
def bggWireEvalMatricesV2 (q n m ell : ℕ) (B : Matrix (Fin n) (Fin (ell * m)) (ZMod q))
    (f : RestrictedDec.Circuit) (x : List Bool) : List (Matrix (Fin (ell * m)) (Fin m) (ZMod q)) :=
  (f.gates.foldl (fun st g =>
    { wireMatrices := st.wireMatrices ++
        [gadget q n m - (st.wireMatrices.getD g.1 0) * gadgetInv q n m (st.wireMatrices.getD g.2 0)]
      evalMatrices := st.evalMatrices ++
        [- (st.evalMatrices.getD g.1 0) * gadgetInv q n m (st.wireMatrices.getD g.2 0) -
          bggBit (q := q) (st.wireValues.getD g.1 false) • (st.evalMatrices.getD g.2 0)]
      wireValues := st.wireValues ++ [!(st.wireValues.getD g.1 false && st.wireValues.getD g.2 false)] })
    ({ wireMatrices := List.ofFn (fun k : Fin ell => bggInputBlock q n m ell B k.val)
       evalMatrices := List.ofFn (fun k : Fin ell => bggSelector q ell m k.val)
       wireValues := x } : BGGFoldState q n m ell)).evalMatrices

/-- The prefix-consistent explicit BGG+ evaluation algorithms. -/
def bggHomEvalV2 : HomEval where
  evalF q n m ell B f :=
    (bggWireMatrices q n m ell B f).getD (f.outs.headD 0) 0
  evalFX q n m ell B f x :=
    if n = 0 then 0 else
      (bggWireEvalMatricesV2 q n m ell B f x).getD (f.outs.headD 0) 0

end PPSLattice


