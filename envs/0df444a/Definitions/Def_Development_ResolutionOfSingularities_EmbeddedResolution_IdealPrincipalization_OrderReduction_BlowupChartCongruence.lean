-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:09:42.221684+00:00
-- url     : https://prove2.me/theorems/211223be-97e8-4b85-a22d-372da4aa74c7
-- title:
--   Blowup Chart Congruence
-- statement:
--   Definitions and structural lemmas for Blowup Chart Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
universe u
section
variable {B A : Type u} [CommRing B] [CommRing A]
def eqModIdealSet (f g : B →+* A) (J : Ideal A) : Set B := {b | f b - g b ∈ J}
theorem one_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) :
    (1 : B) ∈ eqModIdealSet f g J := by
  show f 1 - g 1 ∈ J
  rw [map_one, map_one, sub_self]
  exact J.zero_mem
theorem zero_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) :
    (0 : B) ∈ eqModIdealSet f g J := by
  show f 0 - g 0 ∈ J
  rw [map_zero, map_zero, sub_self]
  exact J.zero_mem
theorem add_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) {x y : B}
    (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J) : x + y ∈ eqModIdealSet f g J := by
  show f (x + y) - g (x + y) ∈ J
  rw [map_add, map_add]
  have hrw : f x + f y - (g x + g y) = (f x - g x) + (f y - g y) := by ring
  rw [hrw]
  exact J.add_mem hx hy
theorem neg_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) {x : B}
    (hx : x ∈ eqModIdealSet f g J) : -x ∈ eqModIdealSet f g J := by
  show f (-x) - g (-x) ∈ J
  rw [map_neg, map_neg]
  have hrw : -f x - -g x = -(f x - g x) := by ring
  rw [hrw]
  exact J.neg_mem hx
theorem mul_mem_eqModIdealSet (f g : B →+* A) (J : Ideal A) {x y : B}
    (hx : x ∈ eqModIdealSet f g J) (hy : y ∈ eqModIdealSet f g J) : x * y ∈ eqModIdealSet f g J := by
  show f (x * y) - g (x * y) ∈ J
  rw [map_mul, map_mul]
  have hrw : f x * f y - g x * g y = f x * (f y - g y) + (f x - g x) * g y := by ring
  rw [hrw]
  exact J.add_mem (J.mul_mem_left _ hy) (J.mul_mem_right _ hx)
def eqModIdealSubring (f g : B →+* A) (J : Ideal A) : Subring B where
  carrier := eqModIdealSet f g J
  one_mem' := one_mem_eqModIdealSet f g J
  zero_mem' := zero_mem_eqModIdealSet f g J
  add_mem' := add_mem_eqModIdealSet f g J
  neg_mem' := neg_mem_eqModIdealSet f g J
  mul_mem' := mul_mem_eqModIdealSet f g J
end
section
variable {R : Type u} [CommRing R]
end
section
variable {R : Type u} [CommRing R]
end
end FunctorialResolution.EmbeddedResolution


