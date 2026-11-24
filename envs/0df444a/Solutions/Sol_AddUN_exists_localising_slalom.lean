-- Prove2me | solution 1 for AddUN.exists_localising_slalom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:43:19.489949+00:00
-- url     : https://prove2.me/submissions/7eac5b81-065d-4eeb-9d33-e71d6dbec3a8

module
public import Definitions.Def_AddUN_Coding
public import Definitions.Def_AddUN_Additivity
public import Theorems.Thm_AddUN_Coding_card_markerBlock
public import Theorems.Thm_AddUN_Coding_lt_mu
public import Theorems.Thm_AddUN_Coding_stage_coord
public import Theorems.Thm_AddUN_exists_slalom_decode
public import Theorems.Thm_IdealInvariant_sUnion_mem_of_lt_add
public import Theorems.Thm_MeasureTheory_Determined_mono
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_mono
public import Theorems.Thm_MeasureTheory_cantorMeasure_cylinderOn
public import Theorems.Thm_MeasureTheory_exists_isCompact_disjoint_of_null
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] AddUN.Coding.stage_coord
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
open Coding
namespace AddUN
theorem _root_.solution {F : Set (ℕ → ℕ)} (hF : #F < add 𝒩) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card ≤ 2 ^ (3 * mu n + n)) ∧
      ∀ f ∈ F, ∀ᶠ n in atTop, f n ∈ S n := by
  -- The points with infinitely many markers along `f` form a null set.
  let N : (ℕ → ℕ) → Set (ℕ → Bool) := fun f ↦ {w | ∃ᶠ n in atTop, w ∈ marker n (f n)}
  have hN : ∀ f, cantorMeasure (N f) = 0 := fun f ↦ by
    have hsum : ∑' n, cantorMeasure (marker n (f n)) ≠ ⊤ := by
      have hle : ∀ n, cantorMeasure (marker n (f n)) ≤ 2⁻¹ ^ n := fun n ↦ by
        rw [marker, cantorMeasure_cylinderOn, card_markerBlock]
        exact pow_le_pow_of_le_one zero_le (by simp) (lt_mu n).le
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [ENNReal.tsum_geometric]
      simp
    refine measure_mono_null (fun w hw ↦ ?_) (measure_limsup_atTop_eq_zero hsum)
    rw [mem_limsup_iff_frequently_mem]
    exact hw
  have hnull : ⋃₀ (N '' F) ∈ 𝒩 :=
    sUnion_mem_of_lt_add (by rintro _ ⟨f, -, rfl⟩; exact hN f) (mk_image_le.trans_lt hF)
  obtain ⟨K, hK, hKpos, hKN⟩ := exists_isCompact_disjoint_of_null hnull
  obtain ⟨S, hS, hSf⟩ := exists_slalom_decode hK hKpos fun _ ↦ false
  refine ⟨S, hS, fun f hf ↦ by_contra fun hev ↦ ?_⟩
  obtain ⟨w, hwK, hw⟩ := hSf f (not_eventually.1 hev)
  refine disjoint_left.1 hKN hwK ⟨N f, mem_image_of_mem N hf, ?_⟩
  -- The bit `0` of the code is `false`, so `w` has infinitely many markers along `f`.
  have h0 : decode f w 0 = false := congrFun hw 0
  unfold decode at h0
  rw [decide_eq_false_iff_not] at h0
  exact (not_eventually.1 h0).mono fun n hn ↦ by
    by_contra hmark
    exact hn fun h ↦ absurd h.2 hmark
end AddUN
