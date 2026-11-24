-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:43.82371+00:00
-- url     : https://prove2.me/theorems/f9b04a8a-f018-4787-854c-665d50894c02
-- title:
--   St Branch Proper At Point
-- statement:
--   Definitions and structural lemmas for St Branch Proper At Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchProperAtPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
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
def BranchProperAtPoint.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u p x : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 x, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {y | GroundTheory.Heights₂.Heights.linEval u y = 0}) →
    ∀ b, ∀ s ∈ Metric.ball 0 (γ b).radius, (γ b).toFun s = x →
      ∀ P ∈ 𝓝 s, ∃ ε > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius,
        (γ b).toFun τ ∈ Metric.ball x ε → τ ∈ P
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


