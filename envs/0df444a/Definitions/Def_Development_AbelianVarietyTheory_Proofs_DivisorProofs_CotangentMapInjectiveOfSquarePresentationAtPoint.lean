-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:59.080802+00:00
-- url     : https://prove2.me/theorems/d171549b-e148-4226-82b6-e1441833d3ca
-- title:
--   Cotangent Map Injective Of Square Presentation At Point
-- statement:
--   Definitions and structural lemmas for Cotangent Map Injective Of Square Presentation At Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CotangentMapInjectiveOfSquarePresentationAtPoint.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.CotangentSquare
open MvPolynomial
variable {O B σ : Type} [CommRing O] [CommRing B]
def firstOrderKer (η : MvPolynomial σ B →+* O) : Ideal (MvPolynomial σ B) where
  carrier := {F | η F = 0 ∧ ∀ l, η (pderiv l F) = 0}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨by simp [hF, hG], fun l => by simp [hF' l, hG' l]⟩
  zero_mem' := ⟨by simp, fun l => by simp⟩
  smul_mem' := by
    rintro G F ⟨hF, hF'⟩
    exact ⟨by simp [hF], fun l => by simp [pderiv_mul, hF, hF' l]⟩
end GlobalTheory.CotangentSquare


