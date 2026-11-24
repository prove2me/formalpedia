-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:42.438666+00:00
-- url     : https://prove2.me/theorems/7cb36e73-0b5c-458f-b10f-602f678decd3
-- title:
--   St Point Slice Mass
-- statement:
--   Definitions and structural lemmas for St Point Slice Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPointSliceMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial
noncomputable section
def PointSliceMass.Statement : Prop :=
  ∀ (n δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin 1 × Fin n) ℂ) (ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J 1 f → IsMultiHomog δ f → linForm ℓ ∉ J →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) 0 (fun _ => 1)
        (fun _ x => Real.log (h.dualNorm x)) = δ
end
end GroundTheory.Heights₂.Heights


