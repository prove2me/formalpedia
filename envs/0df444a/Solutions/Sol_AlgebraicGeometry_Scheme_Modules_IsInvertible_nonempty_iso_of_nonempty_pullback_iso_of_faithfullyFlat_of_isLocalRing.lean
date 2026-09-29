-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b8b85176-75b7-51da-b87e-5cee03f09ce3

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
import Theorems.Thm_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullback_map_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"
open scoped TensorProduct

universe u

namespace BenchV

theorem core
    {S : Type u} [CommRing S] [IsLocalRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (h : Nonempty ((Scheme.Modules.pullback g).obj 𝓜 ≅ 𝟙_ A'.Modules)) :
    Nonempty (𝓜 ≅ 𝟙_ A.Modules) := by
  classical
  obtain ⟨e₀⟩ := h

  letI algA : Algebra S Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
  letI modM : Module S Γ(𝓜, ⊤) := Module.compHom _ (algebraMap S Γ(A, ⊤))
  letI algA' : Algebra S' Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
  letI modM' : Module S' Γ((Scheme.Modules.pullback g).obj 𝓜, ⊤) :=
    Module.compHom _ (algebraMap S' Γ(A', ⊤))
  letI modU' : Module S' Γ(𝟙_ A'.Modules, ⊤) := Module.compHom _ (algebraMap S' Γ(A', ⊤))
  obtain ⟨β, hβ⟩ :=
    Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat S' f f' g hg 𝓜 h𝓜

  let e₀' : Γ((Scheme.Modules.pullback g).obj 𝓜, ⊤) ≃ₗ[S'] Γ(𝟙_ A'.Modules, ⊤) :=
    { toFun := fun x => e₀.hom.app ⊤ x
      map_add' := fun x y => (e₀.hom.app ⊤).hom.map_add x y
      map_smul' := fun s x => by
        change e₀.hom.app ⊤ ((algebraMap S' Γ(A', ⊤) s) • x) = (algebraMap S' Γ(A', ⊤) s) • e₀.hom.app ⊤ x
        exact Scheme.Modules.Hom.app_smul _ _ _
      invFun := fun y => e₀.inv.app ⊤ y
      left_inv := fun x => by
        change (e₀.hom.app ⊤ ≫ e₀.inv.app ⊤) x = x
        rw [← Scheme.Modules.Hom.comp_app, e₀.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        change (e₀.inv.app ⊤ ≫ e₀.hom.app ⊤) y = y
        rw [← Scheme.Modules.Hom.comp_app, e₀.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

  let κ := hg.isoPullback
  have hκ : κ.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) = f' := hg.isoPullback_hom_snd
  have hbij : Function.Bijective (algebraMap S' Γ(A', ⊤)) := by
    have h0 := hH0 S'
    have hfac : ∀ s : S', algebraMap S' Γ(A', ⊤) s =
        κ.hom.appTop.hom ((Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S S')) ⊤).algebraMap s) := by
      intro s
      rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
      change (f'.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom s) = _
      rw [← hκ, Scheme.Hom.comp_appTop]
      change κ.hom.appTop.hom ((pullback.snd f _).appTop.hom _) = _
      have happ : (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).appLE ⊤ ⊤ le_top
          = (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).appTop :=
        Scheme.Hom.appLE_eq_app _
      rw [← happ]
    have hκbij : Function.Bijective κ.hom.appTop.hom := by
      refine Function.bijective_iff_has_inverse.mpr ⟨κ.inv.appTop.hom, fun x => ?_, fun x => ?_⟩
      · change (κ.hom.appTop ≫ κ.inv.appTop).hom x = x
        rw [← Scheme.Hom.comp_appTop, κ.inv_hom_id, Scheme.Hom.id_appTop]; rfl
      · change (κ.inv.appTop ≫ κ.hom.appTop).hom x = x
        rw [← Scheme.Hom.comp_appTop, κ.hom_inv_id, Scheme.Hom.id_appTop]; rfl
    have : (algebraMap S' Γ(A', ⊤) : S' → Γ(A', ⊤)) = κ.hom.appTop.hom ∘ _ := funext hfac
    rw [this]
    exact hκbij.comp h0
  let ρ : S' ≃+* Γ(A', ⊤) := RingEquiv.ofBijective (algebraMap S' Γ(A', ⊤)) hbij

  let u' : Γ(𝟙_ A'.Modules, ⊤) ≃ₗ[S'] S' :=
    { toFun := fun x => ρ.symm (show Γ(A', ⊤) from x)
      map_add' := fun x y => ρ.symm.map_add _ _
      map_smul' := fun s x => by
        change ρ.symm (ρ s * (show Γ(A', ⊤) from x)) = s * ρ.symm _
        rw [map_mul, RingEquiv.symm_apply_apply]
      invFun := fun s => (show Γ(𝟙_ A'.Modules, ⊤) from ρ s)
      left_inv := fun x => ρ.apply_symm_apply _
      right_inv := fun s => ρ.symm_apply_apply _ }

  haveI : Module.Invertible S' (S' ⊗[S] Γ(𝓜, ⊤)) :=
    Module.Invertible.congr ((β.trans e₀').trans u').symm
  haveI hMinv : Module.Invertible S Γ(𝓜, ⊤) :=
    Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat S'
  haveI : Module.Free S Γ(𝓜, ⊤) := inferInstance
  obtain ⟨φ⟩ := (Module.Invertible.free_iff_linearEquiv (R := S) (M := Γ(𝓜, ⊤))).mp ‹_›
  let σ : Γ(𝓜, ⊤) := φ.symm 1
  have hσ : ∀ m : Γ(𝓜, ⊤), ∃ r : S, m = r • σ := fun m =>
    ⟨φ m, by rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]⟩

  have htens : ∀ t : S' ⊗[S] Γ(𝓜, ⊤), ∃ s' : S', t = s' • ((1 : S') ⊗ₜ[S] σ) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [zero_smul]⟩
    | tmul s m =>
        obtain ⟨r, hr⟩ := hσ m
        refine ⟨algebraMap S S' r * s, ?_⟩
        rw [hr, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def,
          smul_eq_mul, mul_one]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [ha, hb, add_smul]⟩

  let sσ : (𝓜 : SheafOfModules A.ringCatSheaf).sections :=
    PresheafOfModules.sectionsMk (M := 𝓜.val)
      (fun U => 𝓜.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op σ)
      (fun U V i => by
        change 𝓜.presheaf.map i (𝓜.presheaf.map _ σ) = 𝓜.presheaf.map _ σ
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        rfl)
  let σ' : 𝟙_ A.Modules ⟶ 𝓜 := (SheafOfModules.unitHomEquiv 𝓜).symm sσ
  have hσ' : σ'.app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤))) = σ := by
    have h1 := SheafOfModules.unitHomEquiv_apply_coe 𝓜 σ' (Opposite.op ⊤)
    rw [show (SheafOfModules.unitHomEquiv 𝓜) σ' = sσ from Equiv.apply_symm_apply _ _] at h1
    have h2 : sσ.val (Opposite.op ⊤) = σ := by
      change 𝓜.presheaf.map _ σ = σ
      rw [show (homOfLE (le_top : (⊤ : A.Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]
      rfl
    exact h1.symm.trans h2

  set adj := Scheme.Modules.pullbackPushforwardAdjunction g with hadj
  have hnat := adj.unit.naturality σ'
  have hnat' : (adj.unit.app 𝓜).app ⊤ (σ'.app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤)))) =
      ((Scheme.Modules.pullback g).map σ').app ⊤
        ((adj.unit.app (𝟙_ A.Modules)).app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤)))) := by
    have := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤)))) hnat
    exact this

  let ι := Scheme.Modules.pullbackTensorUnitObjIso g (Y := A)
  let ψ : 𝟙_ A'.Modules ⟶ 𝟙_ A'.Modules := ι.inv ≫ (Scheme.Modules.pullback g).map σ' ≫ e₀.hom
  let w : Γ(𝟙_ A'.Modules, ⊤) :=
    ι.hom.app ⊤ ((adj.unit.app (𝟙_ A.Modules)).app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤))))
  let a : Γ(A', ⊤) := show Γ(A', ⊤) from ψ.app ⊤ (show Γ(𝟙_ A'.Modules, ⊤) from (1 : Γ(A', ⊤)))

  have hv : e₀' (β ((1 : S') ⊗ₜ[S] σ)) = ψ.app ⊤ w := by
    rw [hβ]
    change e₀.hom.app ⊤ _ = (ι.inv ≫ (Scheme.Modules.pullback g).map σ' ≫ e₀.hom).app ⊤ (ι.hom.app ⊤ _)
    rw [← hσ', hnat']
    simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    congr 2
    change _ = (ι.hom.app ⊤ ≫ ι.inv.app ⊤) _
    rw [← Scheme.Modules.Hom.comp_app, ι.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have key : ∀ x : Γ(A', ⊤),
      (show Γ(𝟙_ A'.Modules, ⊤) from x) = x • (show Γ(𝟙_ A'.Modules, ⊤) from (1 : Γ(A', ⊤))) :=
    fun x => (mul_one x).symm
  have hwa : ψ.app ⊤ w = (show Γ(𝟙_ A'.Modules, ⊤) from ((show Γ(A', ⊤) from w) * a)) := by
    have : w = (show Γ(A', ⊤) from w) • (show Γ(𝟙_ A'.Modules, ⊤) from (1 : Γ(A', ⊤))) := key _
    conv_lhs => rw [this]
    rw [Scheme.Modules.Hom.app_smul]
    rfl
  have ha : IsUnit a := by
    obtain ⟨s', hs'⟩ := htens (((β.trans e₀').trans u').symm 1)
    have h1 : (1 : S') = s' • u' (e₀' (β ((1 : S') ⊗ₜ[S] σ))) := by
      conv_lhs => rw [← ((β.trans e₀').trans u').apply_symm_apply 1]
      rw [hs', map_smul]; rfl
    rw [hv, hwa] at h1
    have h2 : IsUnit ((show Γ(A', ⊤) from w) * a) := by
      have h3 := congrArg ρ h1
      rw [map_one, smul_eq_mul, map_mul] at h3
      change (1 : Γ(A', ⊤)) = ρ s' * ρ (ρ.symm ((show Γ(A', ⊤) from w) * a)) at h3
      rw [RingEquiv.apply_symm_apply] at h3
      exact IsUnit.of_mul_eq_one_right _ h3.symm
    exact isUnit_of_mul_isUnit_right h2

  have hψapp : ∀ (U : A'.Opens) (x : Γ(A', U)),
      ψ.app U (show Γ(𝟙_ A'.Modules, U) from x) =
        (show Γ(𝟙_ A'.Modules, U) from (x * A'.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a)) := by
    intro U x
    have keyU : (show Γ(𝟙_ A'.Modules, U) from x) =
        x • (show Γ(𝟙_ A'.Modules, U) from (1 : Γ(A', U))) := (mul_one x).symm
    conv_lhs => rw [keyU, Scheme.Modules.Hom.app_smul]
    have hone : (𝟙_ A'.Modules).val.map (homOfLE (le_top : U ≤ ⊤)).op
          (show Γ(𝟙_ A'.Modules, ⊤) from (1 : Γ(A', ⊤)))
        = (show Γ(𝟙_ A'.Modules, U) from (1 : Γ(A', U))) :=
      (A'.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.map_one
    have hn := PresheafOfModules.naturality_apply ψ.val (homOfLE (le_top : U ≤ ⊤)).op
      (show Γ(𝟙_ A'.Modules, ⊤) from (1 : Γ(A', ⊤)))
    rw [hone] at hn
    have h1U : ψ.app U (show Γ(𝟙_ A'.Modules, U) from (1 : Γ(A', U))) =
        (show Γ(𝟙_ A'.Modules, U) from A'.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a) := hn
    rw [h1U]
    rfl
  haveI hψ : IsIso ψ := by
    refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U => ?_
    obtain ⟨uU, huU⟩ := ha.map (A'.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
    have hfun : (fun y : Γ(𝟙_ A'.Modules, U) => ψ.app U y) =
        fun y : Γ(A', U) => (show Γ(𝟙_ A'.Modules, U) from (Units.mulRight uU y)) := by
      funext y
      rw [Units.mulRight_apply, huU]
      exact hψapp U y
    exact (show Function.Bijective (fun y : Γ(𝟙_ A'.Modules, U) => ψ.app U y) from
      hfun ▸ (Units.mulRight uU).bijective)
  haveI : IsIso ((Scheme.Modules.pullback g).map σ') := by
    have : (Scheme.Modules.pullback g).map σ' = ι.hom ≫ ψ ≫ e₀.inv := by
      simp only [ψ, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rw [this]; infer_instance
  haveI : IsIso σ' :=
    Scheme.Modules.IsInvertible.isIso_of_isIso_pullback_map_of_faithfullyFlat S' f f' g hg
      (by rw [Scheme.Modules.tensorUnit_eq]; exact Scheme.Modules.isInvertible_unit A) h𝓜 σ' ‹_›
  exact ⟨(asIso σ').symm⟩
theorem main
    {S : Type u} [CommRing S] [IsLocalRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ (Scheme.Modules.pullback g).obj 𝓛')) :
    Nonempty (𝓛 ≅ 𝓛') := by
  obtain ⟨e⟩ := hiso
  obtain ⟨hd', ⟨ed'⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛'
  have h𝓜 : Scheme.Modules.IsInvertible (𝓛 ⊗ Scheme.Modules.dual 𝓛') :=
    Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓛 hd'
  obtain ⟨epd⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 g h𝓛'
  have hp𝓛' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback g).obj 𝓛') :=
    Scheme.Modules.IsInvertible.pullback _ h𝓛'
  obtain ⟨-, ⟨ep'⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hp𝓛'
  have e2 : (Scheme.Modules.pullback g).obj (𝓛 ⊗ Scheme.Modules.dual 𝓛') ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (e ⊗ᵢ epd) ≪≫ ep'
  obtain ⟨e3⟩ := core S' f f' g hg hH0 _ h𝓜 ⟨e2⟩
  exact ⟨(ρ_ 𝓛).symm ≪≫ (Iso.refl 𝓛 ⊗ᵢ (β_ _ _ ≪≫ ed').symm) ≪≫ (α_ _ _ _).symm ≪≫ (e3 ⊗ᵢ Iso.refl 𝓛') ≪≫ λ_ 𝓛'⟩

end BenchV

theorem solution
    {S : Type u} [CommRing S] [IsLocalRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hiso : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ (Scheme.Modules.pullback g).obj 𝓛')) :
    Nonempty (𝓛 ≅ 𝓛') :=
  BenchV.main S' f f' g hg hH0 𝓛 𝓛' h𝓛 h𝓛' hiso

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_faithfullyFlat_of_isLocalRing (solution)
