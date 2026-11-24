-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:35.450469+00:00
-- url     : https://prove2.me/theorems/a125fcb9-1c0d-4878-9de6-848f51dba4e8
-- title:
--   St Slice Cut Chain
-- statement:
--   Definitions and structural lemmas for St Slice Cut Chain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutChain.lean

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
def SliceCutChain.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ) (k : ℕ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
          (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) -
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
          (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) =
      -((k : ℝ) + 1)⁻¹ *
          varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
            (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) *
              deriv Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)))
            (fun _ x => Real.log (h.dualNorm x)) +
        ((k : ℝ) + 1)⁻¹ ^ 2 *
          (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) *
                deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)))
              (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => (Real.log (h.dualNorm x) - Real.log ‖linEval u x‖) *
                deriv (deriv Real.smoothTransition) (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1)) *
                Real.log (h.dualNorm x))
              (fun _ x => Real.log (h.dualNorm x)))
end
end GroundTheory.Heights₂.Heights


