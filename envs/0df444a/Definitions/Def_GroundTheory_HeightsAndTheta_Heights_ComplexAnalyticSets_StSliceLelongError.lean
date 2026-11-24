-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:38.694007+00:00
-- url     : https://prove2.me/theorems/5f387ea0-8ac3-46c4-ad8e-864865aeb3d7
-- title:
--   St Slice Lelong Error
-- statement:
--   Definitions and structural lemmas for St Slice Lelong Error, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceLelongError.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
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
open MvPolynomial Filter Topology Matrix
noncomputable section
def SliceLelongError.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      Tendsto (fun k =>
          varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
              (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) -
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
              (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)
end
end GroundTheory.Heights₂.Heights


