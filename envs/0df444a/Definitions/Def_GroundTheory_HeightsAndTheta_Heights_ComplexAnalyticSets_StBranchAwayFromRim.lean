-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchAwayFromRim
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchAwayFromRim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:01.224075+00:00
-- url     : https://prove2.me/theorems/038deaa6-0511-4938-b9d6-46484b92483d
-- title:
--   St Branch Away From Rim
-- statement:
--   Definitions and structural lemmas for St Branch Away From Rim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchAwayFromRim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
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
open MvPolynomial Filter Topology
noncomputable section
def BranchAwayFromRim.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u p x : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 x, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {y | GroundTheory.Heights₂.Heights.linEval u y = 0}) →
    ∀ b, ∃ ε > 0, ∃ ρ < (γ b).radius, ∀ τ ∈ Metric.ball 0 (γ b).radius,
      (γ b).toFun τ ∈ Metric.ball x ε → ‖τ‖ ≤ ρ
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


