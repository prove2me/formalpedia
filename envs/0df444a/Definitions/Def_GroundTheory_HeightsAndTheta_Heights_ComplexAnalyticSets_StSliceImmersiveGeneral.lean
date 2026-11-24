-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:45.161711+00:00
-- url     : https://prove2.me/theorems/dd6b83db-71ae-4958-aeae-6b218952f672
-- title:
--   St Slice Immersive General
-- statement:
--   Definitions and structural lemmas for St Slice Immersive General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceImmersiveGeneral.lean

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
def SliceImmersiveGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    p ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
    (∃ N ∈ 𝓝 p, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N ⊆ (γ b).slice) →
      ∃ V ∈ 𝓝 p, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V ⊆
        closure {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
          ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
            ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0}
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


