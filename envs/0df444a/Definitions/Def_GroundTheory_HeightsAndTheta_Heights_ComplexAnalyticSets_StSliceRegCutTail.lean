-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegCutTail
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegCutTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:16.311206+00:00
-- url     : https://prove2.me/theorems/1aac00f3-8090-47d7-8812-57213fb9e700
-- title:
--   St Slice Reg Cut Tail
-- statement:
--   Definitions and structural lemmas for St Slice Reg Cut Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegCutTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def SliceRegCutTail.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (ε : ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → 0 < ε →
      Tendsto (fun k => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - sliceCut h k x)
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)
end
end GroundTheory.Heights₂.Heights


