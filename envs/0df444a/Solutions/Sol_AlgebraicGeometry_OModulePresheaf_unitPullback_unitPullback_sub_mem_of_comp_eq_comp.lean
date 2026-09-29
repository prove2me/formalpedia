-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/56255902-e085-5731-bda3-be91ed29cecf

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

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_comp_eq_comp
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
    {R R' : Type u} [CommRing R] [CommRing R'] {P X : Scheme.{u}}
    (πP : P ⟶ Spec (CommRingCat.of R')) [IsSeparated πP] [CompactSpace P]
    (πX : X ⟶ Spec (CommRingCat.of R))
    (q : P ⟶ X) (G : P ⟶ P) (φ : X ⟶ X) (hG : G ≫ q = q ≫ φ)
    (𝒦 : X.OrderedAffineCover) (𝒲 : P.OrderedAffineCover) (lamq : 𝒲.ι → 𝒦.ι)
    (hq : ∀ w, 𝒲.U w ≤ q ⁻¹ᵁ 𝒦.U (lamq w))

    (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
    (hl : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
    (n : ℕ) (z z' : (OModulePresheaf.unit πX).cochain 𝒦 n)
    (hz : (OModulePresheaf.unit πX).d 𝒦 n z = 0) (hz' : (OModulePresheaf.unit πX).d 𝒦 n z' = 0)
    (hzz' : OModulePresheaf.unitPullback (πX := πX) φ 𝒱 𝒦 lam hl n z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱 𝒦 lam' hl' n z'
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 m)))

    (𝒱' : P.OrderedAffineCover) (mu mu' : 𝒱'.ι → 𝒲.ι)
    (hm : ∀ v, 𝒱'.U v ≤ G ⁻¹ᵁ 𝒲.U (mu v)) (hm' : ∀ v, 𝒱'.U v ≤ (𝟙 P) ⁻¹ᵁ 𝒲.U (mu' v)) :
    OModulePresheaf.unitPullback (πX := πP) G 𝒱' 𝒲 mu hm n
        (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq n z) -
        OModulePresheaf.unitPullback (πX := πP) (𝟙 P) 𝒱' 𝒲 mu' hm' n
          (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq n z')
      ∈ (show Submodule R' ((OModulePresheaf.unit πP).cochain 𝒱' n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πP).d 𝒱' m)) := by
  classical

  obtain ⟨𝒱'', lams, hlams⟩ := Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace (Y := P)
    ![X, P, P] (fun j => match j with | 0 => q | 1 => G | 2 => 𝟙 P)
    (fun j => match j with | 0 => 𝒱 | 1 => 𝒲 | 2 => 𝒲)
  let ν : 𝒱''.ι → 𝒱.ι := lams 0
  let κ : 𝒱''.ι → 𝒲.ι := lams 1
  let κ' : 𝒱''.ι → 𝒲.ι := lams 2
  have hν : ∀ v, 𝒱''.U v ≤ q ⁻¹ᵁ 𝒱.U (ν v) := hlams 0
  have hκ : ∀ v, 𝒱''.U v ≤ G ⁻¹ᵁ 𝒲.U (κ v) := hlams 1
  have hκ' : ∀ v, 𝒱''.U v ≤ (𝟙 P) ⁻¹ᵁ 𝒲.U (κ' v) := hlams 2

  have hGq : ∀ v, 𝒱''.U v ≤ (G ≫ q) ⁻¹ᵁ 𝒦.U (lamq (κ v)) := fun v =>
    (hκ v).trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ (hq _))
  have hqφ : ∀ v, 𝒱''.U v ≤ (q ≫ φ) ⁻¹ᵁ 𝒦.U (lam (ν v)) := fun v =>
    (hν v).trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ (hl _))
  have hqφ' : ∀ v, 𝒱''.U v ≤ (G ≫ q) ⁻¹ᵁ 𝒦.U (lam (ν v)) := fun v => by rw [hG]; exact hqφ v
  have hq1 : ∀ v, 𝒱''.U v ≤ (q ≫ 𝟙 X) ⁻¹ᵁ 𝒦.U (lam' (ν v)) := fun v =>
    (hν v).trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ (hl' _))
  have hq2 : ∀ v, 𝒱''.U v ≤ q ⁻¹ᵁ 𝒦.U (lam' (ν v)) := fun v => by simpa using hq1 v
  have hq3 : ∀ v, 𝒱''.U v ≤ q ⁻¹ᵁ 𝒦.U (lamq (κ' v)) := fun v =>
    (hκ' v).trans (Scheme.Hom.preimage_mono _ (hq _))
  have h1q : ∀ v, 𝒱''.U v ≤ (𝟙 P ≫ q) ⁻¹ᵁ 𝒦.U (lamq (κ' v)) := fun v => by rw [Category.id_comp]; exact hq3 v

  have hqz : (OModulePresheaf.unit πP).d 𝒲 n (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq n z) = 0 := by
    rw [OModulePresheaf.d_unitPullback, hz, unitPullback_zero]
  have hqz' : (OModulePresheaf.unit πP).d 𝒲 n (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq n z') = 0 := by
    rw [OModulePresheaf.d_unitPullback, hz', unitPullback_zero]

  cases n with
  | zero =>
    have s1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πP πX G q (G ≫ q) rfl 𝒱'' 𝒲 𝒦 κ lamq
      (lamq ∘ κ) rfl hκ hq hGq _ z hz
    have s2 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero πP πX (G ≫ q) 𝒱'' 𝒦 (lamq ∘ κ) (lam ∘ ν)
      hGq hqφ' _ z hz
    have s3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πX πX q φ (G ≫ q) hG 𝒱'' 𝒱 𝒦 ν lam
      (lam ∘ ν) rfl hν hl hqφ' _ z hz
    change _ ∈ (⊥ : Submodule R ((OModulePresheaf.unit πX).cochain 𝒱 0)) at hzz'
    have s4 := sub_mem_bot_of_sub_mem_bot πP πX q 𝒱'' 𝒱 ν hν _ _ hzz'
    have s5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πX πX q (𝟙 X) q (Category.comp_id q).symm
      𝒱'' 𝒱 𝒦 ν lam' (lam' ∘ ν) rfl hν hl' hq2 _ z' hz'
    have s6 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero πP πX q 𝒱'' 𝒦 (lam' ∘ ν) (lamq ∘ κ')
      hq2 hq3 _ z' hz'
    have s7 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πP πX (𝟙 P) q q (Category.id_comp q).symm
      𝒱'' 𝒲 𝒦 κ' lamq (lamq ∘ κ') rfl hκ' hq hq3 _ z' hz'
    change _ ∈ (⊥ : Submodule R' ((OModulePresheaf.unit πP).cochain 𝒱'' 0)) at s1 s2 s3 s5 s6 s7
    have key : OModulePresheaf.unitPullback (πX := πP) G 𝒱'' 𝒲 κ hκ _
          (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq _ z) -
        OModulePresheaf.unitPullback (πX := πP) (𝟙 P) 𝒱'' 𝒲 κ' hκ' _
          (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq _ z') ∈ (⊥ : Submodule R' ((OModulePresheaf.unit πP).cochain 𝒱'' 0)) := by
      have := Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
        (Submodule.add_mem _ s1 s2) s4) s3) s5) s6) s7
      convert this using 1
      abel
    have fin := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_mem_refinement πP πP G (𝟙 P) 𝒲 𝒱'' κ κ' hκ hκ'
      𝒱' mu mu' hm hm' _ _ _ hqz hqz' key
    exact fin
  | succ m =>
    have s1 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πP πX G q (G ≫ q) rfl 𝒱'' 𝒲 𝒦 κ lamq
      (lamq ∘ κ) rfl hκ hq hGq _ z hz
    have s2 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero πP πX (G ≫ q) 𝒱'' 𝒦 (lamq ∘ κ) (lam ∘ ν)
      hGq hqφ' _ z hz
    have s3 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πX πX q φ (G ≫ q) hG 𝒱'' 𝒱 𝒦 ν lam
      (lam ∘ ν) rfl hν hl hqφ' _ z hz
    change _ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒱 m) at hzz'
    have s4 := sub_mem_range_of_sub_mem_range πP πX q 𝒱'' 𝒱 ν hν m _ _ hzz'
    have s5 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πX πX q (𝟙 X) q (Category.comp_id q).symm
      𝒱'' 𝒱 𝒦 ν lam' (lam' ∘ ν) rfl hν hl' hq2 _ z' hz'
    have s6 := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero πP πX q 𝒱'' 𝒦 (lam' ∘ ν) (lamq ∘ κ')
      hq2 hq3 _ z' hz'
    have s7 := OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πP πP πX (𝟙 P) q q (Category.id_comp q).symm
      𝒱'' 𝒲 𝒦 κ' lamq (lamq ∘ κ') rfl hκ' hq hq3 _ z' hz'
    change _ ∈ LinearMap.range ((OModulePresheaf.unit πP).d 𝒱'' m) at s1 s2 s3 s5 s6 s7
    have key : OModulePresheaf.unitPullback (πX := πP) G 𝒱'' 𝒲 κ hκ _
          (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq _ z) -
        OModulePresheaf.unitPullback (πX := πP) (𝟙 P) 𝒱'' 𝒲 κ' hκ' _
          (OModulePresheaf.unitPullback (πX := πP) q 𝒲 𝒦 lamq hq _ z') ∈ LinearMap.range ((OModulePresheaf.unit πP).d 𝒱'' m) := by
      have := Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
        (Submodule.add_mem _ s1 s2) s4) s3) s5) s6) s7
      convert this using 1
      abel
    have fin := OModulePresheaf.unitPullback_sub_unitPullback_mem_of_mem_refinement πP πP G (𝟙 P) 𝒲 𝒱'' κ κ' hκ hκ'
      𝒱' mu mu' hm hm' _ _ _ hqz hqz' key
    exact fin

end S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_comp_eq_comp
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_comp_eq_comp (solution)
