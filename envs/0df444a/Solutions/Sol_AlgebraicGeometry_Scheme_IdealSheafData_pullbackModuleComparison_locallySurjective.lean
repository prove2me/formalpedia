-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.pullbackModuleComparison_locallySurjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bd7b89e6-9402-5d83-a3d6-e00351db1386

import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.IsTensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace Algebra
p2m_export "Algebra" "TensorProduct.rid ofId IsPushout TensorProduct.includeRight algebraMap TensorProduct.lTensor_ker IsPushout.equiv smul_def TensorProduct.includeLeft id TensorProduct.map"
namespace IsPushout
p2m_export "Algebra.IsPushout" "equiv symm"
p2m_open "Algebra.IsPushout Algebra"

theorem lbE_ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  let e : B ⊗[R] C ≃ₐ[B] P := Algebra.IsPushout.equiv R B C P

  have h1 : algebraMap B P = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom := by
    ext b
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]

  let g : R →ₐ[R] C := Algebra.ofId R C
  have h2 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom := by
    ext b
    simp [g]
  have h3 : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom =
      (RingHom.ker (algebraMap R C)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    have := Algebra.TensorProduct.lTensor_ker (A := B) g hC
    simp [g] at this
    exact this
  rw [h2, ← RingHom.comap_ker, h3]

  let r : B ⊗[R] R ≃ₐ[R] B := Algebra.TensorProduct.rid R R B
  have h4 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom =
      (r.toRingEquiv.symm : B →+* B ⊗[R] R) := by
    ext b
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : (algebraMap R B) = (r.toRingEquiv : B ⊗[R] R →+* B).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

end Algebra.IsPushout

namespace CommRingCat
p2m_export "CommRingCat" "hom_comp of carrier Hom adj isPushout_iff_isPushout"
p2m_open "CommRingCat"

theorem lbE_ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have hw : inl.hom.comp f.hom = inr.hom.comp g.hom := by
    simpa only [CommRingCat.hom_comp] using congr(($(h.w)).hom)
  have : IsScalarTower R C P := .of_algebraMap_eq' hw
  have : Algebra.IsPushout R B C P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.IsPushout.lbE_ker_algebraMap_eq_map_ker R B C P hg

end CommRingCat

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.map_appLE Scheme.Opens.topIso_inv Surjective Scheme.Modules.pushforward Scheme.Modules.pullback isPushout_appTop_of_isPullback Scheme.Hom Scheme.Opens.ι_appIso isAffine_of_isAffineHom IsAffine Scheme Scheme.Hom.appTop Scheme.Opens.topIso_hom isAffineOpen_top Scheme.Modules Scheme.Hom.ker_apply Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.resLE_app_top Scheme.Opens.ι_image_top Scheme.IdealSheafData"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Hom.map_appLE Modules.Hom.app_smul Opens.topIso_inv ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Opens.ι_appIso topIso_hom Modules.Hom Hom.appTop Opens.topIso_hom affineOpens isBasis_affineOpens Modules Hom.ker_apply Opens Hom.appLE_map Hom.resLE_app_top Opens.ι_image_top restrict IdealSheafData"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "comap_comp map subscheme subschemeι_app_surjective ideal inclusion subschemeι comap ker_subschemeι_app ideal_comap_of_isOpenImmersion moduleToPushforwardComapModule pullbackModuleComparison module moduleι range_moduleIota_app_and_injective"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}}

theorem lbE_ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have := CommRingCat.lbE_ker_eq_map_ker_of_isPushout H
    (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩)
  rw [← ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩, comap, Scheme.Hom.ker_apply]
  exact this

set_option backward.isDefEq.respectTransparency false in

theorem lbE_ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by

  suffices key : ∀ (U' : X.affineOpens) (V' : Y.affineOpens),
      U' = ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩ →
      V' = ⟨(V : Y.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using V.2⟩ →
      ∀ (e : (V' : Y.Opens) ≤ f ⁻¹ᵁ (U' : X.Opens)),
        (I.comap f).ideal V' = (I.ideal U').map (f.appLE U' V' e).hom from
    key U V (Subtype.ext (U : X.Opens).ι_image_top.symm)
      (Subtype.ext (V : Y.Opens).ι_image_top.symm) hVU
  rintro _ _ rfl rfl e
  have : IsAffine (U : X.Opens) := U.2
  have : IsAffine (V : Y.Opens) := V.2

  have h := lbE_ideal_comap_top (I.comap (U : X.Opens).ι) (f.resLE U V hVU)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_of_isOpenImmersion (I.comap f) (V : Y.Opens).ι,
    ideal_comap_of_isOpenImmersion I (U : X.Opens).ι] at h
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at h
  erw [CommRingCat.hom_id, Ideal.comap_id] at h
  erw [CommRingCat.hom_id, Ideal.comap_id] at h
  convert h using 2
  all_goals try rfl
  congr 1
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, eqToHom_op, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Scheme.Hom.map_appLE Scheme.Opens.topIso_inv Surjective Scheme.Modules.pushforward Scheme.Modules.pullback isPushout_appTop_of_isPullback Scheme.Hom Scheme.Opens.ι_appIso isAffine_of_isAffineHom IsAffine Scheme Scheme.Hom.appTop Scheme.Opens.topIso_hom isAffineOpen_top Scheme.Modules Scheme.Hom.ker_apply Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.resLE_app_top Scheme.Opens.ι_image_top Scheme.IdealSheafData"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Hom.map_appLE Modules.Hom.app_smul Opens.topIso_inv ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Opens.ι_appIso topIso_hom Modules.Hom Hom.appTop Opens.topIso_hom affineOpens isBasis_affineOpens Modules Hom.ker_apply Opens Hom.appLE_map Hom.resLE_app_top Opens.ι_image_top restrict IdealSheafData"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "comap_comp map subscheme subschemeι_app_surjective ideal inclusion subschemeι comap ker_subschemeι_app ideal_comap_of_isOpenImmersion moduleToPushforwardComapModule pullbackModuleComparison module moduleι range_moduleIota_app_and_injective"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

open Opposite TopologicalSpace

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.moduleToPushforwardComapModule_comp_map_moduleι {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    I.moduleToPushforwardComapModule f ≫
        (SheafOfModules.pushforward f.toRingCatSheafHom).map
          (kernel.ι (I.comap f).subschemeι.unitToPushforwardUnit) =
      kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit := by
  rw [moduleToPushforwardComapModule, Category.assoc]
  erw [PreservesKernel.iso_inv_ι (SheafOfModules.pushforward f.toRingCatSheafHom)
    ((I.comap f).subschemeι.unitToPushforwardUnit)]
  exact kernel.lift_ι ((SheafOfModules.pushforward f.toRingCatSheafHom).map
    ((I.comap f).subschemeι.unitToPushforwardUnit)) _ _

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "moduleToPushforwardComapModule_comp_map_moduleι"

private lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.unit_comp_map_pullbackModuleComparison {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).unit.app
        (I.module : SheafOfModules X.ringCatSheaf) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map (I.pullbackModuleComparison f) =
      I.moduleToPushforwardComapModule f := by
  have h : (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
      (I.pullbackModuleComparison f) = I.moduleToPushforwardComapModule f :=
    Equiv.apply_symm_apply _ _
  exact (Adjunction.homEquiv_unit (adj := SheafOfModules.pullbackPushforwardAdjunction
    f.toRingCatSheafHom) (f := I.pullbackModuleComparison f)).symm.trans h

p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "unit_comp_map_pullbackModuleComparison"

theorem lbE_pullbackModuleComparison_locallySurjective {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    ∀ (U : X'.Opens) (s : Γ((I.comap f).module, U)), ∀ x ∈ U,
      ∃ (V : X'.Opens) (i : V ≤ U), x ∈ V ∧
        ((I.comap f).module).presheaf.map (homOfLE i).op s ∈
          Set.range ((I.pullbackModuleComparison f).app V) := by
  intro U s x hx
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hfx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (U ⊓ f ⁻¹ᵁ U₀ : X'.Opens) from ⟨hx, hfx⟩) (U ⊓ f ⁻¹ᵁ U₀).isOpen
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  have hVU₀ : V ≤ f ⁻¹ᵁ U₀ := fun y hy => (hVle hy).2
  refine ⟨V, hVU, hxV, ?_⟩

  let M : X.Modules := I.module
  let N : X'.Modules := (I.comap f).module
  let P : X'.Modules := (Scheme.Modules.pullback f).obj M
  let α : P ⟶ N := I.pullbackModuleComparison f
  let η : M ⟶ (Scheme.Modules.pushforward f).obj P :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).unit.app
      (I.module : SheafOfModules X.ringCatSheaf)
  let β : M ⟶ (Scheme.Modules.pushforward f).obj N := I.moduleToPushforwardComapModule f
  let ι : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) := I.moduleι
  let ι' : N ⟶ (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) := (I.comap f).moduleι
  obtain ⟨hrangeV, hinjV⟩ := (I.comap f).range_moduleIota_app_and_injective ⟨V, hV⟩
  obtain ⟨hrangeU₀, -⟩ := I.range_moduleIota_app_and_injective ⟨U₀, hU₀⟩
  let g : Γ(X, U₀) →+* Γ(X', V) := (f.appLE U₀ V hVU₀).hom

  let T : Ideal Γ(X', V) :=
    { carrier := {z | ∃ t : Γ(P, V), ι'.app V (α.app V t) = z}
      add_mem' := by
        rintro _ _ ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
        exact ⟨t₁ + t₂, by rw [map_add, map_add]; rfl⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero]; rfl⟩
      smul_mem' := by
        rintro c _ ⟨t, rfl⟩
        exact ⟨c • t, by rw [Modules.Hom.app_smul, Modules.Hom.app_smul]; rfl⟩ }

  have hα_nat : ∀ y : Γ(P, f ⁻¹ᵁ U₀),
      α.app V (P.presheaf.map (homOfLE hVU₀).op y) =
        N.presheaf.map (homOfLE hVU₀).op (α.app (f ⁻¹ᵁ U₀) y) := fun y =>
    ConcreteCategory.congr_hom (α.mapPresheaf.naturality (homOfLE hVU₀).op) y
  have hι'_nat : ∀ y : Γ(N, f ⁻¹ᵁ U₀),
      ι'.app V (N.presheaf.map (homOfLE hVU₀).op y) =
        X'.presheaf.map (homOfLE hVU₀).op (ι'.app (f ⁻¹ᵁ U₀) y) := fun y =>
    ConcreteCategory.congr_hom (ι'.mapPresheaf.naturality (homOfLE hVU₀).op) y
  have hηα : ∀ m : Γ(M, U₀), α.app (f ⁻¹ᵁ U₀) (η.app U₀ m) = β.app U₀ m := fun m => by
    have := I.unit_comp_map_pullbackModuleComparison f
    exact congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj N => φ.app U₀ m) this
  have hβι : ∀ m : Γ(M, U₀), ι'.app (f ⁻¹ᵁ U₀) (β.app U₀ m) = f.app U₀ (ι.app U₀ m) := fun m => by
    have := I.moduleToPushforwardComapModule_comp_map_moduleι f
    exact congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) => φ.app U₀ m) this

  have hT : (I.ideal ⟨U₀, hU₀⟩).map g ≤ T := by
    rw [Ideal.map_le_iff_le_comap]
    intro x₀ hx₀
    obtain ⟨m, hm⟩ : x₀ ∈ Set.range (I.moduleι.app U₀) := by rw [hrangeU₀]; exact hx₀
    refine ⟨P.presheaf.map (homOfLE hVU₀).op (η.app U₀ m), ?_⟩
    rw [hα_nat, hι'_nat, hηα, hβι, ← hm]
    rfl

  have hmem : ι'.app V (N.presheaf.map (homOfLE hVU).op s) ∈ (I.ideal ⟨U₀, hU₀⟩).map g := by
    rw [← lbE_ideal_comap_of_le I f ⟨U₀, hU₀⟩ ⟨V, hV⟩ hVU₀]
    have : ι'.app V (N.presheaf.map (homOfLE hVU).op s) ∈ Set.range ((I.comap f).moduleι.app V) :=
      ⟨_, rfl⟩
    rw [hrangeV] at this
    exact this
  obtain ⟨t, ht⟩ := hT hmem
  exact ⟨t, hinjV ht⟩

end AlgebraicGeometry.Scheme.IdealSheafData

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective.AlgebraicGeometry in
theorem solution {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData) :
    ∀ (U : X'.Opens) (s : Γ((I.comap f).module, U)), ∀ x ∈ U,
      ∃ (V : X'.Opens) (i : V ≤ U), x ∈ V ∧
        ((I.comap f).module).presheaf.map (homOfLE i).op s ∈
          Set.range ((I.pullbackModuleComparison f).app V) :=
  AlgebraicGeometry.Scheme.IdealSheafData.lbE_pullbackModuleComparison_locallySurjective f I

end S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective (solution)
