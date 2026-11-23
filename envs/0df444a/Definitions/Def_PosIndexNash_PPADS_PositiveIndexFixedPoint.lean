-- Prove2me | Definitions.Def_PosIndexNash_PPADS_PositiveIndexFixedPoint
-- name    : PosIndexNash_PPADS_PositiveIndexFixedPoint
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:48:48.784293+00:00
-- url     : https://prove2.me/theorems/d736635a-190b-409b-9e44-01429ee2c0e1
-- title:
--   Promise search problem of a positive-index fixed point of a rational Linear-FIXP circuit
-- statement:
--   **Positive-Index Fixed Point** is the intermediate promise search problem obtained from Theorem 4.2. An instance is a binary-coded rational max-affine circuit computing a self-map of $[0,1]^d$ whose fixed points are all regular and circuit-strict. An answer is a rational vector $q\in\mathbb Q^d$ such that $\Phi(q)=q$, $q\in[0,1]^d$, and
--   $$\operatorname{ind}_{\Phi}(q)=\operatorname{sign}\det(I_d-D\Phi(q))=+1.$$
--   The promise is exactly the regularity and strictness package used by the normal-form construction in §5.1; rationality of the answer enables exact binary decoding.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879, pp. 13–14, Definition 4.1 and Theorem 4.2; p. 34, exact rational decoder

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_encCircuit
import Definitions.Def_PosIndexNash_PPADS_LinCircuit
import Definitions.Def_PosIndexNash_PPADS_FixedPointIndex

namespace PosIndexNash.PPADS

/-- The circuit promise supplied by Theorem 4.2: the circuit computes a self-map of the unit
cube, and every fixed point on that cube is regular and strict. -/
def FixedPointCircuitValid (C : LinCircuit) : Prop :=
  C.WF ∧ C.dIn = C.outs.length ∧
    (∀ x : Fin C.dIn → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      ∀ i, 0 ≤ C.toMap C.dIn x i ∧ C.toMap C.dIn x i ≤ 1) ∧
    (∀ p : Fin C.dIn → ℝ,
      (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ C.toMap C.dIn p = p →
      IsRegularFixedPoint (C.toMap C.dIn) p ∧ C.StrictAt p)

/-- Positive-index exact fixed points of promised rational Linear-FIXP circuits. An answer is a
rational vector, binary-encoded, whose real cast is a fixed point of index `+1`. -/
def PositiveIndexFixedPoint : TetrisHard.Rows.SearchProblem where
  valid s := ∃ C : LinCircuit, FixedPointCircuitValid C ∧ s = C.enc
  answer s t := ∃ (C : LinCircuit) (q : Fin C.dIn → ℚ),
    FixedPointCircuitValid C ∧ s = C.enc ∧
    t = CardinalMatching.encRatVec C.dIn q ∧
    ((∀ i, 0 ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 1) ∧
      C.toMap C.dIn (fun i => (q i : ℝ)) = (fun i => (q i : ℝ))) ∧
    fixedPointIndex (C.toMap C.dIn) (fun i => (q i : ℝ)) = 1

end PosIndexNash.PPADS


