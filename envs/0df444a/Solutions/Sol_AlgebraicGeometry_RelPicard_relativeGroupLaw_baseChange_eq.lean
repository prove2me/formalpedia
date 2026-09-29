-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.relativeGroupLaw_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/654f5da5-5ea1-5f2e-921e-8f58eb9130e5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian P2MW.S_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativePic0Designation RelativeGroupLaw RelativeGroupLaw.baseChangePointToBase RelativeGroupLaw.baseChangePointOfBase_coe RelativeGroupLaw.baseChange RelativeGroupLaw.baseChange_mul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_assoc one inv one_mul inv_mul_cancel mul baseChangePointToBase baseChangePointOfBase_coe baseChange baseChange_mul"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem ext_of_mul {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G G' : RelativeGroupLaw R f)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), G.mul t x y = G'.mul t x y) :
    G = G' := by
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), G.one t = G'.one t := by
    intro T t
    letI := G.pointGroup t
    have hid : G'.one t * G'.one t = G'.one t := by
      show G.mul t (G'.one t) (G'.one t) = G'.one t
      rw [h]; exact G'.one_mul t _
    have h1 : G'.one t = 1 := by simpa [mul_assoc] using congrArg (· * (G'.one t)⁻¹) hid
    exact h1.symm
  have hinv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      G.inv t x = G'.inv t x := by
    intro T t x
    letI := G.pointGroup t
    have h1 : G'.inv t x * x = 1 := by
      show G.mul t (G'.inv t x) x = G.one t
      rw [h, G'.inv_mul_cancel, hone]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  obtain ⟨m, o, i, _, _, _, _, _⟩ := G
  obtain ⟨m', o', i', _, _, _, _, _⟩ := G'
  have hm : @m = @m' := by
    funext T t x y; exact h t x y
  have ho : @o = @o' := by
    funext T t; exact hone t
  have hi : @i = @i' := by
    funext T t x; exact hinv t x
  subst hm ho hi
  rfl

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h' =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).baseChange (specMap R R') := by
  apply GoodReductionJacobian.RelativeGroupLaw.ext_of_mul
  intro T t' x y
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP t' x y
      (RelativeGroupLaw.baseChangePointToBase (specMap R R') x) (RelativeGroupLaw.baseChangePointToBase (specMap R R') y)
      rfl rfl]
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  · rw [((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t' x y).2]
    exact (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).baseChange (specMap R R')).mul
      t' x y).2.symm

end S_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq (solution)
