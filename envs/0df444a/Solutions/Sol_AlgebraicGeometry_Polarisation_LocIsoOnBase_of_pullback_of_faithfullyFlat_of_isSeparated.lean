-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0722396e-1ffb-5585-9d95-34a9ca9116ef

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
import Theorems.Thm_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app
import Theorems.Thm_Module_Invertible_exists_notMem_and_forall_exists_pow_smul_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation"
open scoped TensorProduct

universe u

namespace BenchVE

theorem core
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hloc : ∀ y : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj 𝓜) ≅
        SheafOfModules.unit (↑(f' ⁻¹ᵁ U) : Scheme.{u}).ringCatSheaf)) :
    ∀ p : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj (𝟙_ A.Modules) ≅ (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj 𝓜) := by

  classical

  haveI : QuasiCompact f' := MorphismProperty.of_isPullback hg inferInstance
  haveI : IsSeparated f' := MorphismProperty.of_isPullback hg inferInstance
  set P := (Scheme.Modules.pullback g).obj 𝓜 with hPdef
  have hP : Scheme.Modules.IsInvertible P := Scheme.Modules.IsInvertible.pullback g h𝓜

  letI algA : Algebra S Γ(A, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
  letI modM : Module S Γ(𝓜, ⊤) := Module.compHom _ (algebraMap S Γ(A, ⊤))
  letI algA' : Algebra S' Γ(A', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
  letI modP : Module S' Γ(P, ⊤) := Module.compHom _ (algebraMap S' Γ(A', ⊤))
  letI modU' : Module S' Γ(𝟙_ A'.Modules, ⊤) := Module.compHom _ (algebraMap S' Γ(A', ⊤))

  have hbij : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom := by
    let κ := hg.isoPullback
    have hκ : κ.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) = f' := hg.isoPullback_hom_snd
    have h0 := hH0 S'
    have hfac : ∀ s : S', ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom s =
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
    have : (((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom : S' → Γ(A', ⊤)) = κ.hom.appTop.hom ∘ _ :=
      funext hfac
    rw [this]
    exact hκbij.comp h0

  haveI hPinv : Module.Invertible S' Γ(P, ⊤) :=
    Scheme.Modules.IsInvertible.moduleInvertible_sections_of_forall_exists_nonempty_pullback_preimage_iso_unit
      f' hbij P hP hloc
  obtain ⟨β, hβ⟩ :=
    Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat S' f f' g hg 𝓜 h𝓜
  haveI : Module.Invertible S' (S' ⊗[S] Γ(𝓜, ⊤)) := Module.Invertible.congr β.symm
  haveI hMinv : Module.Invertible S Γ(𝓜, ⊤) :=
    Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat S'

  intro p
  obtain ⟨t, ht, m₀, hgenM⟩ :=
    Module.Invertible.exists_notMem_and_forall_exists_pow_smul_eq_smul (M := Γ(𝓜, ⊤)) p.asIdeal

  let sσ : (𝓜 : SheafOfModules A.ringCatSheaf).sections :=
    PresheafOfModules.sectionsMk (M := 𝓜.val)
      (fun U => 𝓜.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m₀)
      (fun U V i => by
        change 𝓜.presheaf.map i (𝓜.presheaf.map _ m₀) = 𝓜.presheaf.map _ m₀
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        rfl)
  let Θ : 𝟙_ A.Modules ⟶ 𝓜 := (SheafOfModules.unitHomEquiv 𝓜).symm sσ
  have hΘ : Θ.app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤))) = m₀ := by
    have h1 := SheafOfModules.unitHomEquiv_apply_coe 𝓜 Θ (Opposite.op ⊤)
    rw [show (SheafOfModules.unitHomEquiv 𝓜) Θ = sσ from Equiv.apply_symm_apply _ _] at h1
    have h2 : sσ.val (Opposite.op ⊤) = m₀ := by
      change 𝓜.presheaf.map _ m₀ = m₀
      rw [show (homOfLE (le_top : (⊤ : A.Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
        CategoryTheory.Functor.map_id]
      rfl
    exact h1.symm.trans h2

  set adj := Scheme.Modules.pullbackPushforwardAdjunction g with hadj
  have hnat' : (adj.unit.app 𝓜).app ⊤ (Θ.app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤)))) =
      ((Scheme.Modules.pullback g).map Θ).app ⊤
        ((adj.unit.app (𝟙_ A.Modules)).app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤)))) :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤))))
      (adj.unit.naturality Θ)
  let ιg := Scheme.Modules.pullbackTensorUnitObjIso g (Y := A)
  let θ' : 𝟙_ A'.Modules ⟶ P := ιg.inv ≫ (Scheme.Modules.pullback g).map Θ
  let w : Γ(𝟙_ A'.Modules, ⊤) :=
    ιg.hom.app ⊤ ((adj.unit.app (𝟙_ A.Modules)).app ⊤ (show Γ(𝟙_ A.Modules, ⊤) from (1 : Γ(A, ⊤))))
  have hθ'w : θ'.app ⊤ w = (adj.unit.app 𝓜).app ⊤ m₀ := by
    rw [← hΘ, hnat']
    change (ιg.inv ≫ (Scheme.Modules.pullback g).map Θ).app ⊤ (ιg.hom.app ⊤ _) = _
    simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    congr 1
    change (ιg.hom.app ⊤ ≫ ιg.inv.app ⊤) _ = _
    rw [← Scheme.Modules.Hom.comp_app, ιg.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl

  have htens : ∀ z : S' ⊗[S] Γ(𝓜, ⊤), ∃ (n : ℕ) (s' : S'),
      (algebraMap S S' t ^ n) • z = s' • ((1 : S') ⊗ₜ[S] m₀) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by rw [smul_zero, zero_smul]⟩
    | tmul a m =>
        obtain ⟨n, r, hr⟩ := hgenM m
        refine ⟨n, a * algebraMap S S' r, ?_⟩
        have e1 : (algebraMap S S' t ^ n * a) = (t ^ n) • a := by rw [Algebra.smul_def, map_pow]
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, e1,
          TensorProduct.smul_tmul, hr, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    | add x y hx hy =>
        obtain ⟨n₁, s₁, h₁⟩ := hx
        obtain ⟨n₂, s₂, h₂⟩ := hy
        refine ⟨n₁ + n₂, algebraMap S S' t ^ n₂ * s₁ + algebraMap S S' t ^ n₁ * s₂, ?_⟩
        rw [smul_add, add_smul, mul_smul, mul_smul, ← h₁, ← h₂, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add,
          add_comm n₂ n₁]
  have hgen : ∀ m : Γ(P, ⊤), ∃ (n : ℕ) (x : Γ(SheafOfModules.unit A'.ringCatSheaf, ⊤)),
      (((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom (algebraMap S S' t ^ n)) • m =
        Scheme.Modules.Hom.app θ' ⊤ x := by
    intro m
    obtain ⟨n, s', hs'⟩ := htens (β.symm m)
    refine ⟨n, (algebraMap S' Γ(A', ⊤) s') • w, ?_⟩
    rw [Scheme.Modules.Hom.app_smul, hθ'w, ← hβ]
    change (algebraMap S S' t ^ n) • m = s' • β (1 ⊗ₜ[S] m₀)
    rw [← map_smul, ← hs', map_smul, LinearEquiv.apply_symm_apply]

  have hiso' := Scheme.Modules.IsInvertible.isIso_restrict_preimage_basicOpen_of_forall_exists_pow_smul_eq_app
    f' hbij P hP hloc θ' (algebraMap S S' t) hgen

  have hW : g ⁻¹ᵁ (f ⁻¹ᵁ PrimeSpectrum.basicOpen t) = f' ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap S S' t) := by
    rw [← Scheme.Hom.comp_preimage, hg.w, Scheme.Hom.comp_preimage]
    congr 1
  have key : ∀ (W₁ W₂ : A'.Opens), W₁ = W₂ → IsIso ((Scheme.Modules.pullback W₂.ι).map θ') →
      IsIso ((Scheme.Modules.pullback W₁.ι).map θ') := by
    rintro _ _ rfl h; exact h
  have hiso'' : IsIso ((Scheme.Modules.pullback (g ⁻¹ᵁ (f ⁻¹ᵁ PrimeSpectrum.basicOpen t)).ι).map θ') :=
    key _ _ hW hiso'
  have hiso3 : IsIso ((Scheme.Modules.pullback (g ⁻¹ᵁ (f ⁻¹ᵁ PrimeSpectrum.basicOpen t)).ι).map
      ((Scheme.Modules.pullback g).map Θ)) := by
    have : (Scheme.Modules.pullback g).map Θ = ιg.hom ≫ θ' := by
      simp only [θ', Iso.hom_inv_id_assoc]
    rw [this, Functor.map_comp]
    infer_instance

  have hisoΘ := Scheme.Modules.IsInvertible.isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat S' f f' g hg
    (by rw [Scheme.Modules.tensorUnit_eq]; exact Scheme.Modules.isInvertible_unit A) h𝓜 Θ
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen t) hiso3
  refine ⟨PrimeSpectrum.basicOpen t, ht, ⟨?_⟩⟩
  exact @asIso _ _ _ _ _ hisoΘ

theorem main
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hiso : LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓛) ((Scheme.Modules.pullback g).obj 𝓛')) :
    LocIsoOnBase f 𝓛 𝓛' := by

  obtain ⟨hd', ⟨ed'⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 h𝓛'
  have h𝓜 : Scheme.Modules.IsInvertible (𝓛 ⊗ Scheme.Modules.dual 𝓛') :=
    Scheme.Modules.IsInvertible.tensor_monoidalV2 h𝓛 hd'
  obtain ⟨epd⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 g h𝓛'
  have hp𝓛' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback g).obj 𝓛') :=
    Scheme.Modules.IsInvertible.pullback _ h𝓛'

  have hloc : ∀ y : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f' ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback g).obj (𝓛 ⊗ Scheme.Modules.dual 𝓛')) ≅
        SheafOfModules.unit (↑(f' ⁻¹ᵁ U) : Scheme.{u}).ringCatSheaf) := by
    intro y
    obtain ⟨U, hyU, ⟨e⟩⟩ := hiso y
    let ι := (f' ⁻¹ᵁ U).ι
    have hq : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback g).obj 𝓛')) :=
      Scheme.Modules.IsInvertible.pullback _ hp𝓛'
    obtain ⟨epd'⟩ := Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 ι hp𝓛'
    obtain ⟨-, ⟨eq'⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hq
    refine ⟨U, hyU, ⟨?_⟩⟩
    exact (Scheme.Modules.pullback ι).mapIso (Scheme.Modules.pullbackTensorObjIso g _ _ ≪≫ (Iso.refl _ ⊗ᵢ epd)) ≪≫
      Scheme.Modules.pullbackTensorObjIso ι _ _ ≪≫ (e ⊗ᵢ epd') ≪≫ eq'
  intro p
  obtain ⟨U, hpU, ⟨e3⟩⟩ := core S' f f' g hg hH0 _ h𝓜 hloc p
  refine ⟨U, hpU, ⟨?_⟩⟩
  let ι := (f ⁻¹ᵁ U).ι
  let F := Scheme.Modules.pullback ι

  have e𝓛 : 𝓛 ≅ (𝓛 ⊗ Scheme.Modules.dual 𝓛') ⊗ 𝓛' :=
    (ρ_ 𝓛).symm ≪≫ (Iso.refl 𝓛 ⊗ᵢ (β_ _ _ ≪≫ ed').symm) ≪≫ (α_ _ _ _).symm
  exact F.mapIso e𝓛 ≪≫ Scheme.Modules.pullbackTensorObjIso ι _ _ ≪≫ (e3.symm ⊗ᵢ Iso.refl _) ≪≫
    (Scheme.Modules.pullbackTensorObjIso ι _ _).symm ≪≫ F.mapIso (λ_ 𝓛')

end BenchVE

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : A' ⟶ Spec (CommRingCat.of S')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hiso : LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓛) ((Scheme.Modules.pullback g).obj 𝓛')) :
    LocIsoOnBase f 𝓛 𝓛' :=
  BenchVE.main S' f f' g hg hH0 𝓛 𝓛' h𝓛 h𝓛' hiso

end S_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated (solution)
