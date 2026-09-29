-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.schemeNsmul_mul_and_translation_comp_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e0e46052-f7ff-5dcd-9239-ea589be73e68

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace Law4YN

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)

theorem comp_base_eq : f ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = f := by
  rw [specMap_algebraMap_self, Category.comp_id]

theorem constPt_eq (x : Pt f) : constPt f x = GoodReductionJacobian.schemeHomOverComp f (comp_base_eq f) x :=
  Subtype.ext rfl

theorem nsmul_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = @HPow.hPow _ _ _ (@instHPow _ _ (L.pointGroup t).toMonoid.toPow) x n := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl

theorem comp_constPt {g : A ⟶ A} (hg : g ≫ f = f) (x : Pt f) :
    GoodReductionJacobian.schemeHomOverComp g hg (constPt f x) = constPt f x := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, constPt, ← Category.assoc, hg]

end Law4YN

open Law4YN in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (n m : ℕ) (P : L.AlgPoints hc k) :
    L.schemeNsmul (n * m) = L.schemeNsmul m ≫ L.schemeNsmul n ∧
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul m =
      L.schemeNsmul m ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (m • P)) := by
  letI : Group (SchemeHomOver f f) := L.pointGroup f
  have hcomm : ∀ x y : SchemeHomOver f f, x * y = y * x := fun x y => hc.mul_comm f x y
  letI : CommGroup (SchemeHomOver f f) := { (L.pointGroup f) with mul_comm := hcomm }
  have hpow : ∀ (j : ℕ) (x : SchemeHomOver f f), L.nsmul f j x = x ^ j := fun j x => nsmul_eq_pow f L f j x
  constructor
  ·
    have hcomp : L.schemeNsmul m ≫ L.schemeNsmul n =
        (GoodReductionJacobian.schemeHomOverComp (L.schemeNsmul m) (L.schemeNsmul_over m)
          (L.nsmul f n RelativeGroupLaw.idPoint)).1 := by
      rw [GoodReductionJacobian.schemeHomOverComp_coe]; rfl
    rw [hcomp, L.nsmul_natural]
    have hid : GoodReductionJacobian.schemeHomOverComp (L.schemeNsmul m) (L.schemeNsmul_over m)
        (RelativeGroupLaw.idPoint : SchemeHomOver f f) = L.nsmul f m RelativeGroupLaw.idPoint := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id, RelativeGroupLaw.schemeNsmul]
    rw [hid, hpow, hpow, ← pow_mul, mul_comm m n]
    show (L.nsmul f (n * m) RelativeGroupLaw.idPoint).1 = _
    rw [hpow]
  ·
    have hL : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul m =
        (GoodReductionJacobian.schemeHomOverComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P)) (translation_over f L _)
          (L.nsmul f m RelativeGroupLaw.idPoint)).1 := by
      rw [GoodReductionJacobian.schemeHomOverComp_coe]; rfl
    have hR : L.schemeNsmul m ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (m • P)) =
        (GoodReductionJacobian.schemeHomOverComp (L.schemeNsmul m) (L.schemeNsmul_over m)
          (L.mul f RelativeGroupLaw.idPoint (constPt f (RelativeGroupLaw.AlgPoints.toPoint (m • P))))).1 := by
      rw [GoodReductionJacobian.schemeHomOverComp_coe]; rfl
    rw [hL, hR, L.nsmul_natural, L.mul_natural]
    have h1 : GoodReductionJacobian.schemeHomOverComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P)) (translation_over f L _)
        (RelativeGroupLaw.idPoint : SchemeHomOver f f) = L.mul f RelativeGroupLaw.idPoint (constPt f (RelativeGroupLaw.AlgPoints.toPoint P)) := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id, translation]
    have h2 : GoodReductionJacobian.schemeHomOverComp (L.schemeNsmul m) (L.schemeNsmul_over m)
        (RelativeGroupLaw.idPoint : SchemeHomOver f f) = L.nsmul f m RelativeGroupLaw.idPoint := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id, RelativeGroupLaw.schemeNsmul]
    have h3 : constPt f (RelativeGroupLaw.AlgPoints.toPoint (m • P)) = L.nsmul f m (constPt f (RelativeGroupLaw.AlgPoints.toPoint P)) := by
      rw [RelativeGroupLaw.AlgPoints.toPoint_nsmul, constPt_eq, constPt_eq, L.nsmul_natural]
    rw [h1, h2, comp_constPt f (L.schemeNsmul_over m), h3, hpow, hpow, hpow]
    congr 1
    show (RelativeGroupLaw.idPoint * constPt f (RelativeGroupLaw.AlgPoints.toPoint P)) ^ m =
      RelativeGroupLaw.idPoint ^ m * constPt f (RelativeGroupLaw.AlgPoints.toPoint P) ^ m
    exact mul_pow _ _ _

end S_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_schemeNsmul_mul_and_translation_comp_schemeNsmul (solution)
