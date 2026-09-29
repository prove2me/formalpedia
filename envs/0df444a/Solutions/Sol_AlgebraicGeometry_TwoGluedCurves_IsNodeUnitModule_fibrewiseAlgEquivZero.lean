-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedCurves.IsNodeUnitModule.fibrewiseAlgEquivZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a1d0a062-aafa-5d24-9101-2765584bc01e

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.TwoGluedCurves P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero.AlgebraicGeometry.TwoGluedCurves"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.appTop IsClosedImmersion IsReduced HasRingHomProperty.Spec_iff Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules HasRingHomProperty geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso geometricallyIntegral_of_isAlgClosed"
namespace TwoGluedCurves
p2m_export "AlgebraicGeometry.TwoGluedCurves" "IsNodeUnitModule isNodeUnitModule_one_unit exists_isInvertible_isNodeUnitModule IsNodeUnitModule.nonempty_iso IsNodeUnitModule.pullback_baseChangeSnd"
namespace AlgEquivAux
p2m_open "AlgebraicGeometry.TwoGluedCurves AlgebraicGeometry"

def unitsMonoidHom {ι : Type*} [Fintype ι] {M : Type*} [CommGroup M] (v : ι → M) : Multiplicative (ι → ℤ) →* M where
  toFun w := ∏ j, v j ^ (Multiplicative.toAdd w j)
  map_one' := by simp
  map_mul' a b := by simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem unitsMonoidHom_single {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [CommGroup M] (v : ι → M) (j : ι) :
    unitsMonoidHom v (Multiplicative.ofAdd (Pi.single j 1)) = v j := by
  simp only [unitsMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  have := Scheme.ΓSpecIso_inv_naturality φ
  exact (congrArg (fun f => f.hom r) this).symm

section torus

variable (k' : Type u) [Field k'] (n : ℕ)

abbrev R : Type u := AddMonoidAlgebra k' (Fin n → ℤ)

def coordUnit (j : Fin n) : Γ(Spec (CommRingCat.of (R k' n)), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (R k' n))).inv.hom.toMonoidHom
    ((AddMonoidAlgebra.of k' (Fin n → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single j 1)))

variable {k' n} in

theorem exists_point_of_units (w : Fin n → Γ(Spec (CommRingCat.of k'), ⊤)ˣ) :
    ∃ y : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of (R k' n)),
      y ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (R k' n))) = 𝟙 _ ∧
      ∀ j, Units.map y.appTop.hom.toMonoidHom (coordUnit k' n j) = w j := by
  classical
  let w' : Fin n → k'ˣ := fun j => Units.map (Scheme.ΓSpecIso (CommRingCat.of k')).hom.hom.toMonoidHom (w j)
  let m : Multiplicative (Fin n → ℤ) →* k' := (Units.coeHom _).comp (unitsMonoidHom w')
  let φ : R k' n →ₐ[k'] k' := AddMonoidAlgebra.lift k' k' (Fin n → ℤ) m
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, fun j => ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.toRingHom.comp (algebraMap k' (R k' n)) = RingHom.id k' := by
      ext r; exact φ.commutes r
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · apply Units.ext
    simp only [coordUnit, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, MonoidHom.coe_toHomUnits]
    rw [appTop_ΓSpecIso_inv]
    change (Scheme.ΓSpecIso (CommRingCat.of k')).inv (φ _) = _
    simp only [φ, AddMonoidAlgebra.lift_of, m, MonoidHom.coe_comp, Function.comp_apply, unitsMonoidHom_single,
      Units.coeHom_apply, w', Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    first | rfl | exact Iso.hom_inv_id_apply (C := CommRingCat) _ _

end torus

end AlgebraicGeometry.TwoGluedCurves.AlgEquivAux

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.appTop IsClosedImmersion IsReduced HasRingHomProperty.Spec_iff Scheme.Modules.pullbackCongr Spec.map_id Scheme.Modules HasRingHomProperty geometrically Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso geometricallyIntegral_of_isAlgClosed"
namespace TwoGluedCurves
p2m_export "AlgebraicGeometry.TwoGluedCurves" "IsNodeUnitModule isNodeUnitModule_one_unit exists_isInvertible_isNodeUnitModule IsNodeUnitModule.nonempty_iso IsNodeUnitModule.pullback_baseChangeSnd"
namespace AlgEquivAux
p2m_open "AlgebraicGeometry.TwoGluedCurves AlgebraicGeometry"

theorem square {κ : Type u} [Field κ] {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    {k' : Type u} [Field k'] {T' : Scheme.{u}} (t₁ : Spec (.of k') ⟶ Spec (.of κ)) (h' : T' ⟶ Spec (.of k'))
    (y : Spec (.of k') ⟶ T') (hy : y ≫ h' = 𝟙 _) :
    (pullbackLeftPullbackSndIso x t₁ (𝟙 _)).hom ≫
        baseChangeSnd x (⟨y, by rw [← Category.assoc, hy]⟩ : SchemeHomOver (𝟙 _ ≫ t₁) (h' ≫ t₁)) =
      baseChangeSnd (pullback.snd x t₁) (⟨y, hy⟩ : SchemeHomOver (𝟙 _) h') ≫
        (pullbackLeftPullbackSndIso x t₁ h').hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSnd, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst,
      pullback.lift_fst_assoc]
  · simp only [Category.assoc, baseChangeSnd, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.lift_snd_assoc]

theorem fst_eq {κ : Type u} [Field κ] {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    {k' : Type u} [Field k'] (t₁ : Spec (.of k') ⟶ Spec (.of κ)) :
    pullback.fst (pullback.snd x t₁) (𝟙 _) =
      (pullbackLeftPullbackSndIso x t₁ (𝟙 _)).hom ≫
        baseChangeSnd x (⟨𝟙 _, rfl⟩ : SchemeHomOver (𝟙 _ ≫ t₁) t₁) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeSnd, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [Category.assoc, baseChangeSnd, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd_assoc,
      pullback.condition, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

end AlgebraicGeometry.TwoGluedCurves.AlgEquivAux

end

open AlgebraicGeometry.TwoGluedCurves.AlgEquivAux in

theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    {ι : Type v} [Finite ι]
    (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
    (hinj : Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ))
    (hnode : ∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1)
    (hinter : ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
      ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ))
    (hcr : IsReduced (pullback i₁.1 i₂.1))
    (ε : SchemeHomOver (𝟙 (Spec (.of κ))) x)
    {T : Scheme.{u}} {h : T ⟶ Spec (.of κ)} {u : ι → Γ(T, ⊤)ˣ} (M : RigidifiedLineBundle x ε h)
    (hu : IsNodeUnitModule x i₁ i₂ p₁ p₂ h u M.L) :
    FibrewiseAlgEquivZero M := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι

  have core : ∀ {k' : Type u} [Field k'] [IsAlgClosed k'] (t₁ : Spec (.of k') ⟶ Spec (.of κ))
      (lam : ι → Γ(Spec (.of k'), ⊤)ˣ) (M₁ : (pullback x t₁).Modules) (hM₁ : Scheme.Modules.IsInvertible M₁)
      (hu₁ : IsNodeUnitModule x i₁ i₂ p₁ p₂ t₁ lam M₁), IsAlgEquivZero (pullback.snd x t₁) M₁ := by
    intro k' _ _ t₁ lam M₁ hM₁ hu₁
    obtain ⟨n, ⟨eι⟩⟩ := Finite.exists_equiv_fin ι

    let T' : Scheme.{u} := Spec (CommRingCat.of (R k' n))
    let h' : T' ⟶ Spec (.of k') := Spec.map (CommRingCat.ofHom (algebraMap k' (R k' n)))
    haveI : IsDomain (R k' n) := inferInstance
    haveI : IsIntegral T' := inferInstance
    haveI : LocallyOfFiniteType h' := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show RingHom.FiniteType (algebraMap k' (R k' n))
      rw [RingHom.finiteType_algebraMap]
      haveI : AddMonoid.FG (Fin n → ℤ) := by
        rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance
      infer_instance
    haveI : GeometricallyIntegral h' := geometricallyIntegral_of_isAlgClosed h'

    obtain ⟨Mf, hMfinv, hMf⟩ := exists_isInvertible_isNodeUnitModule κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
      (h' ≫ t₁) (fun j => coordUnit k' n (eι j))
    let e := pullbackLeftPullbackSndIso x t₁ h'
    let e0 := pullbackLeftPullbackSndIso x t₁ (𝟙 _)

    obtain ⟨y0, hy0, hy0u⟩ := exists_point_of_units (k' := k') (n := n) 1
    obtain ⟨yl, hyl, hylu⟩ := exists_point_of_units (k' := k') (n := n) (fun r => lam (eι.symm r))
    refine ⟨T', h', inferInstance, inferInstance, (Scheme.Modules.pullback e.hom).obj Mf, hMfinv.pullback _,
      ⟨y0, hy0⟩, ⟨yl, hyl⟩, ?_, ?_⟩
    ·
      have hN := IsNodeUnitModule.pullback_baseChangeSnd κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMfinv hMf
        (⟨y0, by rw [← Category.assoc, hy0]⟩ : SchemeHomOver (𝟙 _ ≫ t₁) (h' ≫ t₁))
      have hunits : (fun j => Units.map y0.appTop.hom.toMonoidHom (coordUnit k' n (eι j))) = 1 :=
        funext fun j => hy0u (eι j)
      simp only [] at hN
      rw [hunits] at hN
      have hO := isNodeUnitModule_one_unit κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr (𝟙 _ ≫ t₁)
      obtain ⟨f⟩ := IsNodeUnitModule.nonempty_iso hN hO
      refine ⟨((Scheme.Modules.pullbackComp _ _).app Mf) ≪≫ (Scheme.Modules.pullbackCongr
        (square x t₁ h' y0 hy0).symm).app Mf ≪≫ ((Scheme.Modules.pullbackComp _ _).app Mf).symm ≪≫
        (Scheme.Modules.pullback e0.hom).mapIso f ≪≫ Scheme.Modules.pullbackUnitIso _⟩
    ·
      have hN := IsNodeUnitModule.pullback_baseChangeSnd κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMfinv hMf
        (⟨yl, by rw [← Category.assoc, hyl]⟩ : SchemeHomOver (𝟙 _ ≫ t₁) (h' ≫ t₁))
      have hunits : (fun j => Units.map yl.appTop.hom.toMonoidHom (coordUnit k' n (eι j))) = lam :=
        funext fun j => by rw [hylu (eι j), Equiv.symm_apply_apply]
      simp only [] at hN
      rw [hunits] at hN
      have hN₁ := IsNodeUnitModule.pullback_baseChangeSnd κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hM₁ hu₁
        (⟨𝟙 _, rfl⟩ : SchemeHomOver (𝟙 _ ≫ t₁) t₁)
      have hunits₁ : (fun j => Units.map (Scheme.Hom.appTop
          (⟨𝟙 _, rfl⟩ : SchemeHomOver (𝟙 _ ≫ t₁) t₁).1).hom.toMonoidHom (lam j)) = lam := by
        funext j; apply Units.ext
        show (Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k')))).hom (lam j) = lam j
        rw [Scheme.Hom.id_appTop]; rfl
      simp only [] at hN₁
      rw [hunits₁] at hN₁
      obtain ⟨f⟩ := IsNodeUnitModule.nonempty_iso hN hN₁
      refine ⟨((Scheme.Modules.pullbackComp _ _).app Mf) ≪≫ (Scheme.Modules.pullbackCongr
        (square x t₁ h' yl hyl).symm).app Mf ≪≫ ((Scheme.Modules.pullbackComp _ _).app Mf).symm ≪≫
        (Scheme.Modules.pullback e0.hom).mapIso f ≪≫ (Scheme.Modules.pullbackComp _ _).app M₁ ≪≫
        (Scheme.Modules.pullbackCongr (fst_eq x t₁).symm).app M₁⟩

  intro k' _ _ s'
  let ψ : SchemeHomOver (s' ≫ h) h := ⟨s', rfl⟩
  let eA := pullbackLeftPullbackSndIso x h s'
  have hfst : pullback.fst (pullback.snd x h) s' = eA.hom ≫ baseChangeSnd x ψ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeSnd, pullback.lift_fst, Category.comp_id, eA,
        pullbackLeftPullbackSndIso_hom_fst]
    · simp only [Category.assoc, baseChangeSnd, pullback.lift_snd, eA, pullbackLeftPullbackSndIso_hom_snd_assoc,
        pullback.condition]
      rfl
  have hN := IsNodeUnitModule.pullback_baseChangeSnd κ x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr M.isInvertible hu ψ
  have hcore := core (s' ≫ h) _ _ (M.isInvertible.pullback _) hN
  have he : eA.hom ≫ pullback.snd x (s' ≫ h) = fibreAt x h s' := by
    simp only [eA, fibreAt, pullbackLeftPullbackSndIso_hom_snd]
  refine IsAlgEquivZero.of_iso ?_ (hcore.pullback eA.hom he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst.symm).app M.L

end S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero (solution)
