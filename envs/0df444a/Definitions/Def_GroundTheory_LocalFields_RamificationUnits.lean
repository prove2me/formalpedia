-- Prove2me | Definitions.Def_GroundTheory_LocalFields_RamificationUnits
-- name    : GroundTheory_LocalFields_RamificationUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:52.415189+00:00
-- url     : https://prove2.me/theorems/9e97b53d-9a39-48da-b4bd-ed6c052f23e5
-- title:
--   Ramification Units
-- statement:
--   Definitions and structural lemmas for Ramification Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationUnits.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_antitone
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_natCast_iff
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residue_integerAlgEquiv_of_mem_zero
import Theorems.Thm_GroundTheory_LocalField_teichmuller_pow_card_sub_one
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
section Inertia
theorem integerAlgEquiv_teichmuller {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (ζ : 𝓀[L]ˣ) :
    integerAlgEquiv K L σ (teichmuller L ζ : 𝒪[L]) = teichmuller L ζ := by
  have hres : unitsToResidue L (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])
      (teichmuller L ζ)) = unitsToResidue L (teichmuller L ζ) := by
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L hσ _
  have hpow : Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (teichmuller L ζ) ^
      (Nat.card 𝓀[L] - 1) = 1 := by
    rw [← map_pow, teichmuller_pow_card_sub_one, map_one]
  exact congrArg Units.val (eq_of_pow_card_sub_one hpow (teichmuller_pow_card_sub_one ζ) hres)
theorem sub_mem_of_uniformizer {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {n : ℕ}
    (h : integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ n) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ n := by
  set e := integerAlgEquiv K L σ
  let P : 𝒪[L] → Prop := fun y ↦ e y - y ∈ 𝓂[L] ^ n
  have hadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb ↦ by
    have : e (a + b) - (a + b) = (e a - a) + (e b - b) := by rw [map_add]; ring
    simp only [P, this]
    exact add_mem ha hb
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb ↦ by
    have : e (a * b) - a * b = e a * (e b - b) + (e a - a) * b := by rw [map_mul]; ring
    simp only [P, this]
    exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
  have hpow : ∀ a (k : ℕ), P a → P (a ^ k) := by
    intro a k ha
    induction k with
    | zero => simp [P]
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih ha
  have hfix : ∀ a, e a = a → P a := fun a ha ↦ by simp [P, ha]
  have hideal : ∀ y ∈ 𝓂[L] ^ n, P y := fun y hy ↦
    sub_mem ((integerAlgEquiv_mem_maximalIdeal_pow_iff σ n y).mpr hy) hy
  have happrox : ∀ y : 𝒪[L], ∃ t, e t = t ∧ y - t ∈ 𝓂[L] := by
    intro y
    by_cases hy : residue 𝒪[L] y = 0
    · exact ⟨0, map_zero e, by simpa using (residue_eq_zero_iff y).mp hy⟩
    · refine ⟨teichmuller L (Units.mk0 _ hy), integerAlgEquiv_teichmuller hσ _, ?_⟩
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrArg Units.val (unitsToResidue_teichmuller (K := L) (Units.mk0 _ hy))).symm
  have hstep : ∀ m : ℕ, ∃ r, P r ∧ x - r ∈ 𝓂[L] ^ m := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp [P], by simp⟩
    | succ m ih =>
      obtain ⟨r, hr, hxr⟩ := ih
      obtain ⟨y, hy⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hxr
      obtain ⟨t, ht, hyt⟩ := happrox y
      obtain ⟨z, hz⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hyt
      refine ⟨r + ϖ ^ m * t, hadd _ _ hr (hmul _ _ (hpow _ _ h) (hfix _ ht)), ?_⟩
      rw [mem_maximalIdeal_pow_iff hϖ]
      exact ⟨z, by rw [pow_succ]; linear_combination hy + ϖ ^ m * hz⟩
  obtain ⟨r, hr, hxr⟩ := hstep n
  have : x = r + (x - r) := by ring
  rw [this]
  exact hadd _ _ hr (hideal _ hxr)
theorem mem_lowerRamificationGroup_iff_uniformizer {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) :=
  ⟨fun h ↦ mem_lowerRamificationGroup_natCast_iff.mp h ϖ,
    fun h ↦ mem_lowerRamificationGroup_natCast_iff.mpr (sub_mem_of_uniformizer hσ hϖ h)⟩
end Inertia
section Ratio
theorem irreducible_integerAlgEquiv (σ : L ≃ₐ[K] L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Irreducible (integerAlgEquiv K L σ ϖ) :=
  (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ
def uniformizerRatio {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (σ : L ≃ₐ[K] L) : 𝒪[L]ˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
theorem mul_uniformizerRatio (σ : L ≃ₐ[K] L) :
    ϖ * uniformizerRatio hϖ σ = integerAlgEquiv K L σ ϖ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose_spec
theorem uniformizerRatio_eq_iff (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    uniformizerRatio hϖ σ = u ↔ ϖ * u = integerAlgEquiv K L σ ϖ := by
  refine ⟨fun h ↦ h ▸ mul_uniformizerRatio hϖ σ, fun h ↦ Units.ext ?_⟩
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans h.symm)
@[simp]
theorem uniformizerRatio_one : uniformizerRatio hϖ (1 : L ≃ₐ[K] L) = 1 := by
  rw [uniformizerRatio_eq_iff, map_one, AlgEquiv.one_apply, Units.val_one, mul_one]
theorem uniformizerRatio_mul (σ τ : L ≃ₐ[K] L) :
    uniformizerRatio hϖ (σ * τ) = uniformizerRatio hϖ σ *
      Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (uniformizerRatio hϖ τ) := by
  rw [uniformizerRatio_eq_iff, map_mul, AlgEquiv.mul_apply, ← mul_uniformizerRatio hϖ τ, map_mul,
    ← mul_uniformizerRatio hϖ σ, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, mul_assoc]
theorem mem_lowerRamificationGroup_iff_uniformizerRatio {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ uniformizerRatio hϖ σ ∈ unitFiltration L n := by
  rw [mem_lowerRamificationGroup_iff_uniformizer hσ hϖ, mem_unitFiltration,
    ← mul_uniformizerRatio hϖ σ, mem_maximalIdeal_pow_iff hϖ, mem_maximalIdeal_pow_iff hϖ,
    show ϖ * (uniformizerRatio hϖ σ : 𝒪[L]) - ϖ = ϖ * ((uniformizerRatio hϖ σ : 𝒪[L]) - 1) by ring,
    pow_succ', mul_dvd_mul_iff_left hϖ.ne_zero]
theorem uniformizerRatio_mem {n : ℕ} (σ : lowerRamificationGroup K L n) :
    uniformizerRatio hϖ (σ : L ≃ₐ[K] L) ∈ unitFiltration L n :=
  (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ
    (lowerRamificationGroup_antitone K L (by omega) σ.2) n).mp σ.2
omit hϖ in

theorem map_mul_inv_mem {n : ℕ} {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L n)
    (u : 𝒪[L]ˣ) :
    Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ ∈ unitFiltration L (n + 1) := by
  rw [mem_unitFiltration]
  have h : ((Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 =
      (integerAlgEquiv K L σ u - u) * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) := by
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, sub_mul, Units.mul_inv]
  rw [h]
  exact Ideal.mul_mem_right _ _ (mem_lowerRamificationGroup_natCast_iff.mp hσ (u : 𝒪[L]))
omit hϖ in

abbrev unitFiltrationSucc (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) : Subgroup (unitFiltration L n) :=
  (unitFiltration L (n + 1)).subgroupOf (unitFiltration L n)
def ramificationToUnits (n : ℕ) :
    lowerRamificationGroup K L n →* unitFiltration L n ⧸ unitFiltrationSucc L n where
  toFun σ := QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩
  map_one' := by
    have : (⟨uniformizerRatio hϖ ((1 : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
      uniformizerRatio_mem hϖ 1⟩ : unitFiltration L n) = 1 := Subtype.ext (uniformizerRatio_one hϖ)
    rw [this, QuotientGroup.mk_one]
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := map_mul_inv_mem σ.2 (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))
    have key : (((⟨uniformizerRatio hϖ ((σ * τ : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
        uniformizerRatio_mem hϖ (σ * τ)⟩ : unitFiltration L n)⁻¹ *
        (⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ *
          ⟨uniformizerRatio hϖ (τ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ τ⟩) : unitFiltration L n) : 𝒪[L]ˣ) =
        (Units.map (integerAlgEquiv K L (σ : L ≃ₐ[K] L) : 𝒪[L] →* 𝒪[L])
          (uniformizerRatio hϖ (τ : L ≃ₐ[K] L)) * (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, uniformizerRatio_mul]
      group
      exact mul_comm _ _
    rw [key]
    exact inv_mem h
theorem ramificationToUnits_apply (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationToUnits hϖ n σ =
      QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ :=
  rfl
theorem ker_ramificationToUnits (n : ℕ) :
    (ramificationToUnits hϖ n).ker =
      (lowerRamificationGroup K L (n + 1 : ℕ)).subgroupOf (lowerRamificationGroup K L n) := by
  ext σ
  have hσ0 : (σ : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 :=
    lowerRamificationGroup_antitone K L (by omega) σ.2
  rw [MonoidHom.mem_ker, ramificationToUnits_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_lowerRamificationGroup_iff_uniformizerRatio hϖ hσ0]
def ramificationQuotientToUnits (n : ℕ) :
    lowerRamificationGroup K L n ⧸
        (lowerRamificationGroup K L (n + 1 : ℕ)).subgroupOf (lowerRamificationGroup K L n) →*
      unitFiltration L n ⧸ unitFiltrationSucc L n :=
  (QuotientGroup.kerLift (ramificationToUnits hϖ n)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_ramificationToUnits hϖ n).symm).toMonoidHom
end Ratio
end GroundTheory.LocalField


