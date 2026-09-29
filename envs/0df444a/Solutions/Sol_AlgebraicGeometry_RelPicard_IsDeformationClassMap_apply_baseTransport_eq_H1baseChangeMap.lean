-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.IsDeformationClassMap.apply_baseTransport_eq_H1baseChangeMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/41c5cdd9-0716-5011-8790-f8ca4f34aac2

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_RigKerDualNumberBaseTransport
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_exists_isFrameOn_pullback_of_map_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra

namespace T1Sol

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
  (K : Type u) [CommRing K] [Algebra R K] (𝒲 : C.TwoAffineOpenCover)

noncomputable def fεhom :
    Limits.pullback (baseChange R c K) (specMap K (DualNumber K)) ⟶ Limits.pullback c (specMap R (DualNumber K)) :=
  (BaseChange.κ c K (specMap K (DualNumber K))).hom ≫
    RelPicard.baseChangeSnd c (BaseTransport.idOver (RigKerDualNumber.tower_dualNumber K K))

theorem fεhom_fst :
    fεhom c K ≫ pullback.fst c (specMap R (DualNumber K)) =
      pullback.fst (baseChange R c K) (specMap K (DualNumber K)) ≫ pullback.fst c (specMap R K) := by
  rw [fεhom, Category.assoc]
  have h1 : RelPicard.baseChangeSnd c (BaseTransport.idOver (RigKerDualNumber.tower_dualNumber K K)) ≫
      pullback.fst c (specMap R (DualNumber K)) = pullback.fst c _ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [h1, BaseChange.κ_hom_fst]

theorem fεhom_snd :
    fεhom c K ≫ pullback.snd c (specMap R (DualNumber K)) =
      pullback.snd (baseChange R c K) (specMap K (DualNumber K)) := by
  rw [fεhom, Category.assoc]
  have h1 : RelPicard.baseChangeSnd c (BaseTransport.idOver (RigKerDualNumber.tower_dualNumber K K)) ≫
      pullback.snd c (specMap R (DualNumber K)) = pullback.snd c _ := by
    refine (pullback.lift_snd _ _ _).trans ?_
    rw [BaseTransport.idOver_coe, Category.comp_id]
  rw [h1, BaseChange.κ_hom_snd]

noncomputable def fε :
    Scheme.TwoAffineOpenCover.HomOver (RingHom.id (DualNumber K)) (𝒲.pullback c (DualNumber K))
      (pullback.snd c (specMap R (DualNumber K)))
      ((𝒲.pullback c K).pullback (baseChange R c K) (DualNumber K))
      (pullback.snd (baseChange R c K) (specMap K (DualNumber K))) where
  hom := fεhom c K
  comm := by
    rw [fεhom_snd, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  U0_le := by
    rw [Scheme.TwoAffineOpenCover.pullback_U0, Scheme.TwoAffineOpenCover.pullback_U0,
      Scheme.TwoAffineOpenCover.pullback_U0, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, fεhom_fst]
  U1_le := by
    rw [Scheme.TwoAffineOpenCover.pullback_U1, Scheme.TwoAffineOpenCover.pullback_U1,
      Scheme.TwoAffineOpenCover.pullback_U1, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, fεhom_fst]

theorem fε_hom : (fε c K 𝒲).hom = fεhom c K := rfl

theorem thickening_hom {C' : Scheme.{u}} {R' : Type u} [CommRing R'] (c' : C' ⟶ Spec (.of R')) (A : Type u) [CommRing A]
    [Algebra R' A] (𝒱 : C'.TwoAffineOpenCover) :
    (dualNumberThickening A 𝒱 c').hom =
      RelPicard.baseChangeSnd c' (RelPicard.LFP.stageHom R' (IsScalarTower.toAlgHom R' A (DualNumber A))) := rfl

theorem baseChange_hom {C' : Scheme.{u}} {R' : Type u} [CommRing R'] (c' : C' ⟶ Spec (.of R')) (A : Type u) [CommRing A]
    [Algebra R' A] (𝒱 : C'.TwoAffineOpenCover) :
    (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c' A).hom = pullback.fst c' (specMap R' A) := rfl

theorem fε_comm_thickening :
    fεhom c K ≫ (dualNumberThickening K 𝒲 c).hom =
      (dualNumberThickening K (𝒲.pullback c K) (baseChange R c K)).hom ≫
        (Scheme.TwoAffineOpenCover.HomOver.baseChange (𝒲.pullback c K) (baseChange R c K) K).hom := by
  rw [thickening_hom, thickening_hom, baseChange_hom]
  apply pullback.hom_ext
  · rw [Category.assoc, Scheme.TwoAffineOpenCover.baseChangeSnd_fst, fεhom_fst, Category.assoc, ← Category.assoc
      (RelPicard.baseChangeSnd (baseChange R c K) _)]
    rw [show RelPicard.baseChangeSnd (baseChange R c K)
          (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K K (DualNumber K))) ≫
          pullback.fst (baseChange R c K) (specMap K K) = pullback.fst (baseChange R c K) (specMap K (DualNumber K))
        from (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
  · have h1 : RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R K (DualNumber K))) ≫
        pullback.snd c (specMap R K) =
        pullback.snd c _ ≫ (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R K (DualNumber K))).1 :=
      pullback.lift_snd _ _ _
    have h2 : RelPicard.baseChangeSnd (baseChange R c K)
        (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K K (DualNumber K))) ≫
        pullback.snd (baseChange R c K) (specMap K K) =
        pullback.snd (baseChange R c K) _ ≫ (RelPicard.LFP.stageHom K (IsScalarTower.toAlgHom K K (DualNumber K))).1 :=
      pullback.lift_snd _ _ _
    rw [Category.assoc, h1, ← Category.assoc, fεhom_snd, Category.assoc]
    rw [show pullback.fst (baseChange R c K) (specMap K K) ≫ pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K) =
        pullback.snd (baseChange R c K) (specMap K K) ≫ specMap K K from pullback.condition]
    rw [← Category.assoc, h2, Category.assoc]
    congr 1
    rw [RelPicard.LFP.stageHom_val, RelPicard.LFP.stageHom_val]
    change _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

theorem map01_comm_sq
    {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
    {τ₁ : R₁ →+* R₂} {τ₂ : R₂ →+* R₄} {τ₃ : R₁ →+* R₃} {τ₄ : R₃ →+* R₄}
    {X₁ X₂ X₃ X₄ : Scheme.{u}} {𝒱₁ : X₁.TwoAffineOpenCover} {𝒱₂ : X₂.TwoAffineOpenCover}
    {𝒱₃ : X₃.TwoAffineOpenCover} {𝒱₄ : X₄.TwoAffineOpenCover}
    {c₁ : X₁ ⟶ Spec (.of R₁)} {c₂ : X₂ ⟶ Spec (.of R₂)} {c₃ : X₃ ⟶ Spec (.of R₃)} {c₄ : X₄ ⟶ Spec (.of R₄)}
    (tX : Scheme.TwoAffineOpenCover.HomOver τ₁ 𝒱₁ c₁ 𝒱₂ c₂) (fX : Scheme.TwoAffineOpenCover.HomOver τ₂ 𝒱₂ c₂ 𝒱₄ c₄)
    (fK : Scheme.TwoAffineOpenCover.HomOver τ₃ 𝒱₁ c₁ 𝒱₃ c₃) (tY : Scheme.TwoAffineOpenCover.HomOver τ₄ 𝒱₃ c₃ 𝒱₄ c₄)
    (h : fX.hom ≫ tX.hom = tY.hom ≫ fK.hom) (x : (𝒱₁.cover c₁).A01) :
    fX.map01 (tX.map01 x) = tY.map01 (fK.map01 x) := by
  rw [Scheme.TwoAffineOpenCover.HomOver.map01_apply, Scheme.TwoAffineOpenCover.HomOver.map01_apply,
    Scheme.TwoAffineOpenCover.HomOver.map01_apply, Scheme.TwoAffineOpenCover.HomOver.map01_apply,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ {g g' : X₄ ⟶ X₁} (_ : g = g') (e : 𝒱₄.U0 ⊓ 𝒱₄.U1 ≤ g ⁻¹ᵁ (𝒱₁.U0 ⊓ 𝒱₁.U1))
      (e' : 𝒱₄.U0 ⊓ 𝒱₄.U1 ≤ g' ⁻¹ᵁ (𝒱₁.U0 ⊓ 𝒱₁.U1)), g.appLE _ _ e = g'.appLE _ _ e' := by
    rintro g _ rfl _ _; rfl
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) x) (key h _ _)

theorem fεhom_def :
    fεhom c K = (BaseChange.κ c K (specMap K (DualNumber K))).hom ≫
      RelPicard.baseChangeSnd c (BaseTransport.idOver (RigKerDualNumber.tower_dualNumber K K)) := rfl

theorem fε_comm_thickening' :
    (fε c K 𝒲).hom ≫ (dualNumberThickening K 𝒲 c).hom =
      (dualNumberThickening K (𝒲.pullback c K) (baseChange R c K)).hom ≫
        (Scheme.TwoAffineOpenCover.HomOver.baseChange (𝒲.pullback c K) (baseChange R c K) K).hom := by
  rw [fε_hom]; exact fε_comm_thickening c K 𝒲

theorem fε_map01_oneAddEpsMul (f : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01) :
    (fε c K 𝒲).map01 (oneAddEpsMul K 𝒲 c f) =
      oneAddEpsMul K (𝒲.pullback c K) (baseChange R c K)
        ((Scheme.TwoAffineOpenCover.HomOver.baseChange (𝒲.pullback c K) (baseChange R c K) K).map01 f) := by
  have h1 : (fε c K 𝒲).map01 1 = 1 := by
    rw [Scheme.TwoAffineOpenCover.HomOver.map01_apply]
    exact map_one ((fε c K 𝒲).hom.appLE _ _ (fε c K 𝒲).inf_le).hom
  have h2 : ∀ x y : ((𝒲.pullback c (DualNumber K)).cover (pullback.snd c (specMap R (DualNumber K)))).A01,
      (fε c K 𝒲).map01 (x * y) = (fε c K 𝒲).map01 x * (fε c K 𝒲).map01 y := fun x y => by
    rw [Scheme.TwoAffineOpenCover.HomOver.map01_apply, Scheme.TwoAffineOpenCover.HomOver.map01_apply,
      Scheme.TwoAffineOpenCover.HomOver.map01_apply]
    exact map_mul ((fε c K 𝒲).hom.appLE _ _ (fε c K 𝒲).inf_le).hom x y
  have h3 : ∀ r : DualNumber K, (fε c K 𝒲).map01 (algebraMap (DualNumber K) _ r) = algebraMap (DualNumber K) _ r :=
    fun r => by
    rw [Scheme.TwoAffineOpenCover.HomOver.map01_apply]
    exact Scheme.TwoAffineOpenCover.HomOver.appLE_algebraMap (fε c K 𝒲) _ r
  rw [oneAddEpsMul, oneAddEpsMul, map_add, h1, h2, h3,
    map01_comm_sq _ _ _ _ (fε_comm_thickening' c K 𝒲) f]

end T1Sol

open T1Sol in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (K : Type u) [CommRing K] [Algebra R K] (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲}
    {δ' : RigKerDualNumber (baseChange R c K) (sectionBaseChange K ε) K →
      H1StructureSheaf (baseChange R c K) K (𝒲.pullback c K)}
    (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (hδ' : IsDeformationClassMap (baseChange R c K) (sectionBaseChange K ε) K (𝒲.pullback c K) δ')
    (m : RigKerDualNumber c ε K) :
    δ' (RigKerDualNumber.baseTransport K c ε K m) =
      Scheme.TwoAffineOpenCover.H1baseChangeMap (𝒲.pullback c K) (baseChange R c K) K (δ m) := by
  classical
  induction m using Quotient.ind with
  | _ M =>
  rw [RigKerDualNumber.baseTransport_mk]

  obtain ⟨e₀, e₁, f, h₀, h₁, ht⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε K 𝒲 M
  rw [hδ M e₀ e₁ f h₀ h₁ ht, Scheme.TwoAffineOpenCover.H1baseChangeMap_mk]

  obtain ⟨s₀, s₁, hs₀, hs₁, hst⟩ :=
    Scheme.TwoAffineOpenCover.HomOver.exists_isFrameOn_pullback_of_map_eq_smul (fε c K 𝒲) M.1.L e₀ e₁ h₀ h₁ _ ht
  rw [fε_map01_oneAddEpsMul] at hst

  let N := (Scheme.Modules.pullback (fε c K 𝒲).hom).obj M.1.L
  let eM : N ≅ (RigKerDualNumber.baseTransportCarrier K c ε K M).1.L :=
    (Scheme.Modules.pullbackCongr (fε_hom c K 𝒲)).app M.1.L ≪≫
      (Scheme.Modules.pullbackCongr (fεhom_def c K)).app M.1.L ≪≫
      ((Scheme.Modules.pullbackComp (BaseChange.κ c K (specMap K (DualNumber K))).hom
        (RelPicard.baseChangeSnd c (BaseTransport.idOver (RigKerDualNumber.tower_dualNumber K K)))).app M.1.L).symm
  have hs₀' := hs₀.map_iso eM
  have hs₁' := hs₁.map_iso eM
  refine hδ' (RigKerDualNumber.baseTransportCarrier K c ε K M) (eM.hom.app _ s₀) (eM.hom.app _ s₁)
    ((Scheme.TwoAffineOpenCover.HomOver.baseChange (𝒲.pullback c K) (baseChange R c K) K).map01 f) hs₀' hs₁' ?_

  have nat : ∀ {U W : (Limits.pullback (baseChange R c K) (specMap K (DualNumber K))).Opens}
      (i : W ⟶ U) (s : Γ(N, U)),
      (RigKerDualNumber.baseTransportCarrier K c ε K M).1.L.presheaf.map i.op (eM.hom.app U s) =
        eM.hom.app W (N.presheaf.map i.op s) := fun i s => by
    have := (eM.hom.mapPresheaf).naturality i.op
    exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : Γ(N, _) → _)) this) s).symm
  rw [nat, nat, hst, Scheme.Modules.Hom.app_smul]

end S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap (solution)
