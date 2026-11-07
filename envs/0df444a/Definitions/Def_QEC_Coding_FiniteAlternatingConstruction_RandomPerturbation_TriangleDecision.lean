-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:10:26.035218+00:00
-- url     : https://prove2.me/theorems/1bc64d73-d6b1-47f5-a546-be52bb1d14c1
-- title:
--   Triangle Decision
-- statement:
--   Definitions and structural lemmas for Triangle Decision, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/TriangleDecision.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
noncomputable def planePoint (a : Fin 3 → Space) (z : Space) : Space :=
  a 0+planeU (a 1-a 0) (a 2-a 0) (z-a 0) • (a 1-a 0)+
    planeV (a 1-a 0) (a 2-a 0) (z-a 0) • (a 2-a 0)
def planeFeasible (a : Fin 3 → Space) (z : Space) : Prop :=
  gramDet (a 1-a 0) (a 2-a 0) ≠ 0 ∧
    0 ≤ planeU (a 1-a 0) (a 2-a 0) (z-a 0) ∧
    0 ≤ planeV (a 1-a 0) (a 2-a 0) (z-a 0) ∧
    planeU (a 1-a 0) (a 2-a 0) (z-a 0)+
      planeV (a 1-a 0) (a 2-a 0) (z-a 0) ≤ 1
def triangleBallTest (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : Prop :=
  (∃ i, dist z (a i) ≤ ρ) ∨
    (∃ i j : Fin 3, i < j ∧ dist z (segmentPoint (a i) (a j) z) ≤ ρ) ∨
    (planeFeasible a z ∧ dist z (planePoint a z) ≤ ρ)
end QEC.Coding.BDL26RandomPerturbation


