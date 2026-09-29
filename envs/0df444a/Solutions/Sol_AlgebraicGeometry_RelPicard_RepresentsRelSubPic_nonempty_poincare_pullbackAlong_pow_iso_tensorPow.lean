-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_pow_iso_tensorPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0a649d8d-7a52-5bdd-8c11-6bf3fee39283

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_pow_iso_tensorPow

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

open scoped CategoryTheory.MonObj

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) (n : ℕ) :
    letI := h.relativeGroupLaw.pointGroup t
    Nonempty ((h.poincare.pullbackAlong (a ^ n)).L ≅ (h.poincare.pullbackAlong a).L.tensorPow n) := by
  letI := h.relativeGroupLaw.pointGroup t

  have hmul : ∀ x y : SchemeHomOver t D.toBase,
      Nonempty ((h.poincare.pullbackAlong (x * y)).L ≅ (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) := by
    intro x y
    letI := h.grpObj
    obtain ⟨e⟩ := h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
    exact ⟨e⟩
  have hone : Nonempty ((h.poincare.pullbackAlong (1 : SchemeHomOver t D.toBase)).L ≅ 𝟙_ _) := by
    letI := h.grpObj
    obtain ⟨e⟩ := h.nonempty_poincare_pullbackAlong_one_iso (Over.mk t)
    exact ⟨e⟩
  induction n with
  | zero =>
    rw [pow_zero]
    exact hone
  | succ n ih =>
    obtain ⟨e1⟩ := hmul (a ^ n) a
    obtain ⟨e2⟩ := ih
    rw [pow_succ]
    exact ⟨e1 ≪≫ (e2 ⊗ᵢ Iso.refl _)⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_pow_iso_tensorPow
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_pow_iso_tensorPow (solution)
