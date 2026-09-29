-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.unitPullback_comp_sub_unitPullback_id_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f7ecebe0-c93e-59c3-bf9a-e73d91ee388e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_mem_refinement
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comp_sub_unitPullback_id_mem
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Ws23Cech

p2m_open "AlgebraicGeometry AlgebraicGeometry.OModulePresheaf~Hom"

variable {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}

theorem unitPullback_zero (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n 0 = 0 := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj, Pi.zero_apply]
    change _ • (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, _))) = (0 : Γ(X, _))
    rw [map_zero, map_zero, smul_zero]
  · rw [unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj]
    rfl

theorem unitPullback_sub (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z z' : (unit πY).cochain 𝒦 n) :
    unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n (z - z') =
      unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n z - unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam n z' := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [Pi.sub_apply, unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj, Pi.sub_apply]
    have e1 : (h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj) - z' (𝒲.sortIdx 𝒦 lam s hinj)) = (h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z (𝒲.sortIdx 𝒦 lam s hinj)) - (h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (z' (𝒲.sortIdx 𝒦 lam s hinj)) := map_sub _ _ _
    rw [e1, map_sub, smul_sub]
    rfl
  · rw [Pi.sub_apply, unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj,
      unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n _ s hinj]
    exact (sub_zero _).symm

theorem sub_mem_bot_of_sub_mem_bot (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (z z' : (unit πY).cochain 𝒦 0)
    (hzz' : z - z' ∈ (⊥ : Submodule R ((unit πY).cochain 𝒦 0))) :
    unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam 0 z - unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam 0 z'
      ∈ (⊥ : Submodule R' ((unit πX).cochain 𝒲 0)) := by
  rw [← unitPullback_sub]
  rw [Submodule.mem_bot] at hzz' ⊢
  rw [hzz', unitPullback_zero]

theorem sub_mem_range_of_sub_mem_range (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (m : ℕ) (z z' : (unit πY).cochain 𝒦 (m + 1))
    (hzz' : z - z' ∈ LinearMap.range ((unit πY).d 𝒦 m)) :
    unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam (m + 1) z -
        unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam (m + 1) z'
      ∈ LinearMap.range ((unit πX).d 𝒲 m) := by
  rw [← unitPullback_sub]
  obtain ⟨b, hb⟩ := hzz'
  exact ⟨unitPullback (πX := πX) (πY := πY) h 𝒲 𝒦 lam hlam m b, by rw [d_unitPullback, hb]⟩

end Ws23Cech

open Ws23Cech in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX] [CompactSpace X]
    (φ ψ : X ⟶ X) (𝒦 : X.OrderedAffineCover)

    (𝒱₁ : X.OrderedAffineCover) (lam₁ lam₁' : 𝒱₁.ι → 𝒦.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam₁ v)) (hl₁' : ∀ v, 𝒱₁.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₁' v))

    (𝒱₂ : X.OrderedAffineCover) (lam₂ lam₂' : 𝒱₂.ι → 𝒦.ι)
    (hl₂ : ∀ v, 𝒱₂.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam₂ v)) (hl₂' : ∀ v, 𝒱₂.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₂' v))
    (n : ℕ) (z z' z'' : (OModulePresheaf.unit πX).cochain 𝒦 n)
    (hz : (OModulePresheaf.unit πX).d 𝒦 n z = 0) (hz' : (OModulePresheaf.unit πX).d 𝒦 n z' = 0)
    (hz'' : (OModulePresheaf.unit πX).d 𝒦 n z'' = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₁ 𝒦 lam₁ hl₁ n z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₁ 𝒦 lam₁' hl₁' n z'
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₁ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₁ m)))
    (h₂ : OModulePresheaf.unitPullback (πX := πX) φ 𝒱₂ 𝒦 lam₂ hl₂ n z' -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₂ 𝒦 lam₂' hl₂' n z''
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₂ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₂ m)))

    (𝒱₃ : X.OrderedAffineCover) (lam₃ lam₃' : 𝒱₃.ι → 𝒦.ι)
    (hl₃ : ∀ v, 𝒱₃.U v ≤ (φ ≫ ψ) ⁻¹ᵁ 𝒦.U (lam₃ v)) (hl₃' : ∀ v, 𝒱₃.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₃' v)) :
    OModulePresheaf.unitPullback (πX := πX) (φ ≫ ψ) 𝒱₃ 𝒦 lam₃ hl₃ n z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₃ 𝒦 lam₃' hl₃' n z''
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₃ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₃ m)) := by
  classical

  obtain ⟨𝒱, lams, hlams⟩ := Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace (Y := X)
    ![X, X] (fun j => match j with | 0 => φ | 1 => 𝟙 X) (fun j => match j with | 0 => 𝒱₁ | 1 => 𝒱₂)
  let μ : 𝒱.ι → 𝒱₁.ι := lams 0
  let ν : 𝒱.ι → 𝒱₂.ι := lams 1
  have hμ : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒱₁.U (μ v) := hlams 0
  have hν : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒱₂.U (ν v) := hlams 1

  have hφψ : ∀ v, 𝒱.U v ≤ (φ ≫ ψ) ⁻¹ᵁ 𝒦.U (lam₁ (μ v)) := fun v =>
    (hμ v).trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ (hl₁ _))
  have hφ1 : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam₁' (μ v)) := fun v =>
    (hμ v).trans (Scheme.Hom.preimage_mono _ (hl₁' _))
  have hφ2 : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam₂ (ν v)) := fun v => (hν v).trans (hl₂ _)
  have h12 : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₂' (ν v)) := fun v => (hν v).trans (hl₂' _)

  cases n with
  | zero =>
    change _ ∈ (⊥ : Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₁ 0)) at h₁
    change _ ∈ (⊥ : Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₂ 0)) at h₂
    have s2 := sub_mem_bot_of_sub_mem_bot πX πX φ 𝒱 𝒱₁ μ hμ _ _ h₁
    have s6 := sub_mem_bot_of_sub_mem_bot πX πX (𝟙 X) 𝒱 𝒱₂ ν hν _ _ h₂
    have s1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX φ ψ (φ ≫ ψ) rfl 𝒱 𝒱₁ 𝒦 μ lam₁
      (lam₁ ∘ μ) rfl hμ hl₁ hφψ _ z hz
    have s3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX φ (𝟙 X) φ (Category.comp_id φ).symm
      𝒱 𝒱₁ 𝒦 μ lam₁' (lam₁' ∘ μ) rfl hμ hl₁' hφ1 _ z' hz'
    have s4 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero πX πX φ 𝒱 𝒦 (lam₁' ∘ μ) (lam₂ ∘ ν)
      hφ1 hφ2 _ z' hz'
    have s5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX (𝟙 X) φ φ (Category.id_comp φ).symm
      𝒱 𝒱₂ 𝒦 ν lam₂ (lam₂ ∘ ν) rfl hν hl₂ hφ2 _ z' hz'
    have s7 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp (𝟙 X)).symm 𝒱 𝒱₂ 𝒦 ν lam₂' (lam₂' ∘ ν) rfl hν hl₂' h12 _ z'' hz''
    change _ ∈ (⊥ : Submodule R ((OModulePresheaf.unit πX).cochain 𝒱 0)) at s1 s3 s4 s5 s7
    have key : OModulePresheaf.unitPullback (πX := πX) (φ ≫ ψ) 𝒱 𝒦 (lam₁ ∘ μ) hφψ _ z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱 𝒦 (lam₂' ∘ ν) h12 _ z'' ∈ (⊥ : Submodule R ((OModulePresheaf.unit πX).cochain 𝒱 0)) := by
      have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
        (Submodule.sub_mem _ s2 s1) s3) s5) s4) s6) s7
      convert this using 1
      abel
    have fin := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_mem_refinement πX πX (φ ≫ ψ) (𝟙 X) 𝒦 𝒱
      (lam₁ ∘ μ) (lam₂' ∘ ν) hφψ h12 𝒱₃ lam₃ lam₃' hl₃ hl₃' _ z z'' hz hz'' key
    exact fin
  | succ m =>
    change _ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₁ m) at h₁
    change _ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₂ m) at h₂
    have s2 := sub_mem_range_of_sub_mem_range πX πX φ 𝒱 𝒱₁ μ hμ m _ _ h₁
    have s6 := sub_mem_range_of_sub_mem_range πX πX (𝟙 X) 𝒱 𝒱₂ ν hν m _ _ h₂
    have s1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX φ ψ (φ ≫ ψ) rfl 𝒱 𝒱₁ 𝒦 μ lam₁
      (lam₁ ∘ μ) rfl hμ hl₁ hφψ _ z hz
    have s3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX φ (𝟙 X) φ (Category.comp_id φ).symm
      𝒱 𝒱₁ 𝒦 μ lam₁' (lam₁' ∘ μ) rfl hμ hl₁' hφ1 _ z' hz'
    have s4 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero πX πX φ 𝒱 𝒦 (lam₁' ∘ μ) (lam₂ ∘ ν)
      hφ1 hφ2 _ z' hz'
    have s5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX (𝟙 X) φ φ (Category.id_comp φ).symm
      𝒱 𝒱₂ 𝒦 ν lam₂ (lam₂ ∘ ν) rfl hν hl₂ hφ2 _ z' hz'
    have s7 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp (𝟙 X)).symm 𝒱 𝒱₂ 𝒦 ν lam₂' (lam₂' ∘ ν) rfl hν hl₂' h12 _ z'' hz''
    change _ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 m) at s1 s3 s4 s5 s7
    have key : OModulePresheaf.unitPullback (πX := πX) (φ ≫ ψ) 𝒱 𝒦 (lam₁ ∘ μ) hφψ _ z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱 𝒦 (lam₂' ∘ ν) h12 _ z'' ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 m) := by
      have := Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
        (Submodule.sub_mem _ s2 s1) s3) s5) s4) s6) s7
      convert this using 1
      abel
    have fin := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_mem_refinement πX πX (φ ≫ ψ) (𝟙 X) 𝒦 𝒱
      (lam₁ ∘ μ) (lam₂' ∘ ν) hφψ h12 𝒱₃ lam₃ lam₃' hl₃ hl₃' _ z z'' hz hz'' key
    exact fin

end S_AlgebraicGeometry_OModulePresheaf_unitPullback_comp_sub_unitPullback_id_mem
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_comp_sub_unitPullback_id_mem (solution)
