-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:05.676575+00:00
-- url     : https://prove2.me/theorems/122d4f92-af26-43d9-9510-4e85a5efc878
-- title:
--   St Branch Lift
-- statement:
--   Definitions and structural lemmas for St Branch Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchLift.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchAwayFromRim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def BranchLift.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : NormalModel J)
    (γ : GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    ∃ Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = zeroSetIn M.ideal ∩ O
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


