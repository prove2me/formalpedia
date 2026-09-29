-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/02fa8035-f711-5f47-ae19-8e6dbec70e4a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace TransNsmul

theorem nsmul_mul {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (a b : SchemeHomOver t f) :
    L.nsmul t n (L.mul t a b) = L.mul t (L.nsmul t n a) (L.nsmul t n b) := by
  induction n with
  | zero => simp [RelativeGroupLaw.nsmul_zero, L.one_mul]
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, ih]

    rw [L.mul_assoc, ← L.mul_assoc t (L.nsmul t n b) a b, hc.mul_comm t (L.nsmul t n b) a, L.mul_assoc, ← L.mul_assoc]

end TransNsmul

open TransNsmul in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (P : L.AlgPoints hc k) (m : ℕ) (hP : m • P = 0) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul m = L.schemeNsmul m := by
  set x := RelativeGroupLaw.AlgPoints.toPoint P with hxdef
  have hx : L.nsmul _ m x = L.one _ := (RelativeGroupLaw.AlgPoints.nsmul_eq_zero_iff m P).1 hP
  have h1 := L.nsmul_natural f f (translation f L x) (translation_over f L x) m RelativeGroupLaw.idPoint
  have h2 : schemeHomOverComp (translation f L x) (translation_over f L x) RelativeGroupLaw.idPoint =
      L.mul f RelativeGroupLaw.idPoint (constPt f x) := Subtype.ext (Category.comp_id _)
  have hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = f := by
    rw [specMap_algebraMap_self, Category.comp_id]
  have h3 : constPt f x = schemeHomOverComp f hf x := Subtype.ext rfl
  have h4 : L.nsmul f m (constPt f x) = L.one f := by
    rw [h3, ← L.nsmul_natural, hx, L.one_natural]
  have key : schemeHomOverComp (translation f L x) (translation_over f L x) (L.nsmul f m RelativeGroupLaw.idPoint) =
      L.nsmul f m RelativeGroupLaw.idPoint := by
    rw [h1, h2, nsmul_mul L hc, h4, L.mul_one]
  exact congrArg Subtype.val key

end S_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero (solution)
