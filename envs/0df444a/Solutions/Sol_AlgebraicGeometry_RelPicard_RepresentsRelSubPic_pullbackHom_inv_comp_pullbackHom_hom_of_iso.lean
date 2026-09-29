-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/40be8222-e57d-5ba7-a4e9-97692d6096e7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

universe u

namespace Sub2

variable {R : Type u} [CommRing R]

theorem classify_congr {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c ε t) (hM : P.P t M) (hM' : P.P t M') (i : Nonempty (M.L ≅ M'.L)) :
    h.classify t M hM = h.classify t M' hM' :=
  h.classify_unique t M' hM' _ ⟨(h.classify_spec t M hM).some ≪≫ i.some⟩

variable {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}

theorem curveChange_comp {C'' : Scheme.{u}} {c'' : C'' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (g : C'' ⟶ C') (hg : g ≫ c' = c'')
    (k : C'' ⟶ C) (hk : k ≫ c = c'') (hgf : g ≫ f = k)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (c := c') (c' := c'') g hg t ≫ curveChange (c := c) (c' := c') f hf t
      = curveChange (c := c) (c' := c'') k hk t := by
  subst hgf
  apply pullback.hom_ext <;>
    simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
      Category.comp_id]

theorem curveChange_id {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange (c := c) (c' := c) (𝟙 C) (Category.id_comp c) t = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [curveChange, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.id_comp]

theorem comp_eq_id (f : C' ⟶ C) (hf : f ≫ c = c') (hεf : ε'.1 ≫ f = ε.1)
    (g : C ⟶ C') (hg : g ≫ c' = c) (hεg : ε.1 ≫ g = ε'.1) (hgf : g ≫ f = 𝟙 C)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (RepresentsRelSubPic.pullbackHom f hf hεf h h').1 ≫ (RepresentsRelSubPic.pullbackHom g hg hεg h' h).1 = 𝟙 D.P := by

  have hid : ε.1 ≫ 𝟙 C = ε.1 := Category.comp_id _
  have e1 : postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h) (RepresentsRelSubPic.pullbackHom f hf hεf h h')
      = RepresentsRelSubPic.pullbackHom (𝟙 C) (Category.id_comp c) hid h h := by
    apply RepresentsRelSubPic.pullbackHom_unique
    intro T t M hM
    have step1 : postComp (postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h)
        (RepresentsRelSubPic.pullbackHom f hf hεf h h')) (h.classify t M hM)
        = postComp (RepresentsRelSubPic.pullbackHom g hg hεg h' h)
          (postComp (RepresentsRelSubPic.pullbackHom f hf hεf h h') (h.classify t M hM)) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [step1, RepresentsRelSubPic.postComp_pullbackHom_classify, RepresentsRelSubPic.postComp_pullbackHom_classify]
    apply classify_congr
    exact ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_comp f hf g hg (𝟙 C) (Category.id_comp c) hgf t)).app M.L⟩
  have e2 : (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase)
      = RepresentsRelSubPic.pullbackHom (𝟙 C) (Category.id_comp c) hid h h := by
    apply RepresentsRelSubPic.pullbackHom_unique
    intro T t M hM
    have : postComp (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase) (h.classify t M hM)
        = h.classify t M hM := Subtype.ext (Category.comp_id _)
    rw [this]
    apply classify_congr
    exact ⟨((Scheme.Modules.pullbackCongr (curveChange_id (c := c) t)).app M.L ≪≫
      (Scheme.Modules.pullbackId _).app M.L).symm⟩
  have := congrArg Subtype.val (e1.trans e2.symm)
  exact this

end Sub2

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    (hε : ε.1 ≫ e.hom = ε'.1) (hε' : ε'.1 ≫ e.inv = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (RepresentsRelSubPic.pullbackHom e.inv he' hε' h h').1 ≫ (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).1 = 𝟙 D.P ∧
    (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).1 ≫ (RepresentsRelSubPic.pullbackHom e.inv he' hε' h h').1 = 𝟙 D'.P :=
  ⟨Sub2.comp_eq_id e.inv he' hε' e.hom he hε e.hom_inv_id h h',
    Sub2.comp_eq_id e.hom he hε e.inv he' hε' e.inv_hom_id h' h⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso (solution)
