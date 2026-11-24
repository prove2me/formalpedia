-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:16.780776+00:00
-- url     : https://prove2.me/theorems/4429c8ca-71b8-48d6-8823-f574fd07bab7
-- title:
--   St Slice Ideal
-- statement:
--   Definitions and structural lemmas for St Slice Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
def SliceIdeal.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
    (ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (k + 1) F → linForm ℓ ∉ J →
      (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = (k : ℕ) ∧
        ∀ u : Fin n → ℂ, linForm u ∉ J → linForm u ∉ J ⊔ Ideal.span {linForm ℓ - 1}
end
end GroundTheory.Heights₂.Heights


