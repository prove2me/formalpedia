-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/641ebb0a-d9f5-5251-a033-95023aae7995

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) :
    (∀ x : Pt f, translation f L x = L.translate (toUnitPt f x)) ∧
    (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, L.translate y = translation f L (ofUnitPt f y)) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

end S_AlgebraicGeometry_RiemannForm_translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt (solution)
