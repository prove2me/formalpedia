-- Prove2me | solution 1 for AddUN.measure_sUnion_null_of_localised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:02.445575+00:00
-- url     : https://prove2.me/submissions/d87865ee-6f25-41b6-aa02-22ab00ca7e8e

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation
public import Theorems.Thm_AddUN_exists_clopens_limsup
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (h : ℕ → ℕ)
    {𝒢 : Set (Set (ℕ → Bool))} (h𝒢 : ∀ G ∈ 𝒢, μ G = 0)
    (hloc : ∀ F : Set (ℕ → ℕ), #F ≤ #𝒢 → ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ h n) ∧
      ∀ f ∈ F, ∀ᶠ n in atTop, f n ∈ S n) :
    μ (⋃₀ 𝒢) = 0 := by
  obtain ⟨O, hO⟩ := exists_surjective_nat (Clopens (ℕ → Bool))
  let ε : ℕ → ℝ≥0∞ := fun n ↦ 2⁻¹ ^ n * ((h n : ℝ≥0∞) + 1)⁻¹
  have hε : ∀ n, ε n ≠ 0 := fun n ↦ by simp [ε]
  choose C hCε hCG using fun G : 𝒢 ↦ exists_clopens_limsup μ (h𝒢 G G.2) hε
  obtain ⟨S, hS, hSF⟩ := hloc (range fun G : 𝒢 ↦ fun n ↦ Function.surjInv hO (C G n)) mk_range_le
  classical
  -- The slalom gives a null set that contains every member of `𝒢`.
  let D : ℕ → Set (ℕ → Bool) := fun n ↦
    ⋃ k ∈ S n, if μ (O k) ≤ ε n then (O k : Set (ℕ → Bool)) else ∅
  have hD : ∀ n, μ (D n) ≤ 2⁻¹ ^ n := fun n ↦ by
    have h1 : μ (D n) ≤ ∑ k ∈ S n, ε n := by
      refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
      split_ifs with hk
      · exact hk
      · simp
    refine h1.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_left_comm]
    refine mul_le_of_le_one_right zero_le ?_
    rw [← div_eq_mul_inv]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact (Nat.cast_le.2 (hS n)).trans le_self_add
  have hnull : μ (limsup D atTop) = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hD))
    rw [ENNReal.tsum_geometric]
    simp
  refine measure_mono_null (fun x hx ↦ ?_) hnull
  obtain ⟨G, hG, hxG⟩ := hx
  have hloc' : ∀ᶠ n in atTop, Function.surjInv hO (C ⟨G, hG⟩ n) ∈ S n :=
    hSF _ ⟨⟨G, hG⟩, rfl⟩
  rw [mem_limsup_iff_frequently_mem]
  refine ((hCG ⟨G, hG⟩ x hxG).and_eventually hloc').mono fun n hn ↦ ?_
  have hOk : O (Function.surjInv hO (C ⟨G, hG⟩ n)) = C ⟨G, hG⟩ n := Function.surjInv_eq hO _
  refine mem_biUnion hn.2 ?_
  rw [hOk, if_pos (hCε ⟨G, hG⟩ n)]
  exact hn.1
end AddUN
