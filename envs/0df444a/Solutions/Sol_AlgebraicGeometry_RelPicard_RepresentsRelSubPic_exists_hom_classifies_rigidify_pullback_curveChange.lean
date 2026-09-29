-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c2b8bc86-b9bc-521a-823a-25b260ac07bb

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace P2mGenPull

theorem nonempty_pullback_fst_ofInvertible_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L : (pullback c t).Modules)
    (hL : Scheme.Modules.IsInvertible L) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L) := by
  rw [RigidifiedLineBundle.ofInvertible_L_eq_tensor]

  have hD : Scheme.Modules.IsInvertible (rigCorrection ε t L) := ((hL.pullback _).dual).1
  obtain ⟨u⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hD.pullback s)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := pullback.snd c t) (g := s))).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c')

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L) :=
  M.isInvertible.pullback _

def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  RigidifiedLineBundle.ofInvertible (ε := ε')
    ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L) (hinv f hf t M)

theorem hcongr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi (ε' := ε') f hf t M).L ≅ (Phi (ε' := ε') f hf t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _ ((Scheme.Modules.pullback _).mapIso h.some)

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε' := ε') f hf t M) := by
  intro k _ _ s

  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  have h1 : IsAlgEquivZero (fibreAt c' t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c' t) s)).obj
        ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)) := by
    refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  obtain ⟨e2⟩ := nonempty_pullback_fst_ofInvertible_iso (ε := ε') _ (hinv f hf t M) s
  exact h1.of_iso e2.symm

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε' := ε') f hf t (RigidifiedLineBundle.unit (c := c) (ε := ε) t)).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L) := by
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    (hinv f hf t (RigidifiedLineBundle.unit t))
    (RigidifiedLineBundle.unit (c := c') (ε := ε') t).isInvertible (Scheme.Modules.pullbackUnitIso _)
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c') (ε := ε') t)
  exact ⟨e1 ≪≫ e2⟩

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t) :
    Nonempty ((Phi (ε' := ε') f hf t (M.tensor M')).L ≅
      ((Phi (ε' := ε') f hf t M).tensor (Phi (ε' := ε') f hf t M')).L) := by
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    (hinv f hf t (M.tensor M')) ((hinv f hf t M).tensor (hinv f hf t M'))
    (Scheme.Modules.pullbackTensorObjIso _ _ _)
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε')
    (hinv f hf t M) (hinv f hf t M')
  exact ⟨e1 ≪≫ e2⟩

theorem hnat {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((Phi (ε' := ε') f hf t M).pullbackAlong ψ).L ≅
      (Phi (ε' := ε') f hf t' (M.pullbackAlong ψ)).L) := by
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε') ψ (hinv f hf t M)
  have e2 : (Scheme.Modules.pullback (baseChangeSnd c' ψ)).obj
      ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L) ≅
      (Scheme.Modules.pullback (curveChange f hf t')).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M.L) :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd f hf ψ).symm).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    ((hinv f hf t M).pullback (baseChangeSnd c' ψ)) (hinv f hf t' (M.pullbackAlong ψ)) e2
  exact ⟨e1 ≪≫ e3⟩

end Transform

end P2mGenPull

end

open P2mGenPull in

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    ∃ N : SchemeHomOver D.toBase D'.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      D.zeroSection ≫ N.1 = D'.zeroSection:= by

  obtain ⟨N, hN, -⟩ := RepresentsRelSubPic.existsUnique_hom_of_transform h' h (Phi (ε' := ε') f hf)
    (fun t M M' e => hcongr (ε' := ε') f hf t M M' e) (fun ψ M => hnat (ε' := ε') f hf ψ M)
    (fun t M hM => hcut (ε' := ε') f hf t M hM)

  have hhom := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut c' ε') (P' := algEquivZeroGroupCut c ε) h' h (Phi (ε' := ε') f hf)
    (fun t M hM => hcut (ε' := ε') f hf t M hM) (fun t M M' => htensor (ε' := ε') f hf t M M')
    (fun t => hunit (ε' := ε') f hf t) N hN
  refine ⟨N, ?_, fun t x y => hhom.1 t x y, hhom.2⟩
  intro T t a
  let M : RigidifiedLineBundle c ε t := h.poincare.pullbackAlong a
  have hM : (algEquivZeroCut c ε).P t M := (algEquivZeroCut c ε).pullback_mem _ _ a _ h.poincare_mem
  have ha : a = h.classify t M hM := h.classify_unique _ M hM a ⟨Iso.refl _⟩
  have hNa : postComp N a = h'.classify t (Phi (ε' := ε') f hf t M) (hcut (ε' := ε') f hf t M hM) := by
    conv_lhs => rw [ha]
    exact hN t M hM
  have e : NeronModelInfra.schemeHomOverComp a N = postComp N a := rfl
  rw [e, hNa]
  exact h'.classify_spec _ _ _

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange (solution)
