-- Prove2me | Definitions.Def_AddUN_Uniformity
-- name    : AddUN_Uniformity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:23:51.209266+00:00
-- url     : https://prove2.me/theorems/3e6b1f21-62d3-483a-a517-7c95c8254b4e
-- title:
--   Uniformity
-- statement:
--   Definitions and structural lemmas for Uniformity, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Uniformity.lean

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Theorems.Thm_MeasureTheory_Determined_inter
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip


set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
namespace MeasureTheory
theorem exists_measurableSet_subset_measure_eq_half {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {B : Set X} (hB : MeasurableSet B) : ∃ B' ⊆ B, MeasurableSet B' ∧ μ B' = μ B / 2 := by
  by_cases h0 : μ B = 0
  · exact ⟨∅, empty_subset _, .empty, by simp [h0]⟩
  have hψ : Measurable (embeddingReal X) := measurable_embeddingReal X
  have hψi : Function.Injective (embeddingReal X) := (measurableEmbedding_embeddingReal X).injective
  set ψ := embeddingReal X
  let G : ℝ → ℝ≥0∞ := fun t ↦ μ (B ∩ ψ ⁻¹' Iic t)
  have hGm : Monotone G := fun a b hab ↦
    measure_mono (inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.2 hab)))
  have hmeas : ∀ t, MeasurableSet (B ∩ ψ ⁻¹' Iic t) := fun t ↦ hB.inter (hψ measurableSet_Iic)
  have hpos : 0 < μ B / 2 := ENNReal.div_pos h0 (by simp)
  have hlt : μ B / 2 < μ B := ENNReal.half_lt_self h0 (measure_ne_top _ _)
  -- `G` is small far to the left and large far to the right.
  have hbot : Tendsto (fun n : ℕ ↦ G (-(n : ℝ))) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (-(n : ℝ))) (fun n ↦ (hmeas _).nullMeasurableSet)
      (fun m n hmn ↦ inter_subset_inter_right _
        (preimage_mono (Iic_subset_Iic.2 (neg_le_neg (Nat.cast_le.2 hmn)))))
      ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ n : ℕ, B ∩ ψ ⁻¹' Iic (-(n : ℝ)) = ∅ := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false,
        iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-ψ x)
      exact ⟨n, fun h ↦ by linarith [h.2]⟩
    rwa [hempty, measure_empty] at hlim
  obtain ⟨n₀, hn₀⟩ := (hbot.eventually_lt_const hpos).exists
  have htop : Tendsto (fun n : ℕ ↦ G (n : ℝ)) atTop (𝓝 (μ B)) := by
    have hlim := tendsto_measure_iUnion_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (n : ℝ)) (fun m n hmn ↦ inter_subset_inter_right _
        (preimage_mono (Iic_subset_Iic.2 (Nat.cast_le.2 hmn))))
    have hU : ⋃ n : ℕ, B ∩ ψ ⁻¹' Iic (n : ℝ) = B := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_Iic, exists_and_left,
        and_iff_left_iff_imp]
      exact fun _ ↦ exists_nat_ge (ψ x)
    rwa [hU] at hlim
  obtain ⟨n₁, hn₁⟩ := (htop.eventually_const_lt hlt).exists
  -- Cut at the supremum of the points where `G` is at most half the measure of `B`.
  let S : Set ℝ := {t | G t ≤ μ B / 2}
  have hSne : S.Nonempty := ⟨-(n₀ : ℝ), hn₀.le⟩
  have hSbdd : BddAbove S :=
    ⟨n₁, fun t ht ↦ le_of_not_gt fun hgt ↦ (hn₁.trans_le (hGm hgt.le)).not_ge ht⟩
  have hinv : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
  have ha : μ B / 2 ≤ G (sSup S) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (sSup S + 1 / ((n : ℝ) + 1)))
      (fun n ↦ (hmeas _).nullMeasurableSet)
      (fun m n hmn ↦ inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.2
        (add_le_add_right (Nat.one_div_le_one_div hmn) _))))
      ⟨0, measure_ne_top _ _⟩
    have hI : ⋂ n : ℕ, B ∩ ψ ⁻¹' Iic (sSup S + 1 / ((n : ℝ) + 1)) = B ∩ ψ ⁻¹' Iic (sSup S) := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_preimage, mem_Iic]
      constructor
      · intro h
        refine ⟨(h 0).1, le_of_not_gt fun hgt ↦ ?_⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
        linarith [(h n).2]
      · exact fun h n ↦ ⟨h.1, h.2.trans (by linarith [hinv n])⟩
    rw [hI] at hlim
    refine ge_of_tendsto' hlim fun n ↦ ?_
    have hnot : sSup S + 1 / ((n : ℝ) + 1) ∉ S := fun hmem ↦ by
      linarith [le_csSup hSbdd hmem, hinv n]
    exact (not_le.1 hnot).le
  have hb : μ (B ∩ ψ ⁻¹' Iio (sSup S)) ≤ μ B / 2 := by
    have hlim := tendsto_measure_iUnion_atTop (μ := μ)
      (s := fun n : ℕ ↦ B ∩ ψ ⁻¹' Iic (sSup S - 1 / ((n : ℝ) + 1)))
      (fun m n hmn ↦ inter_subset_inter_right _ (preimage_mono (Iic_subset_Iic.2
        (sub_le_sub_left (Nat.one_div_le_one_div hmn) _))))
    have hU : ⋃ n : ℕ, B ∩ ψ ⁻¹' Iic (sSup S - 1 / ((n : ℝ) + 1)) = B ∩ ψ ⁻¹' Iio (sSup S) := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨h1, by linarith [hinv n]⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
        exact ⟨n, h1, by linarith⟩
    rw [hU] at hlim
    refine le_of_tendsto' hlim fun n ↦ ?_
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_lt_csSup hSne
      (show sSup S - 1 / ((n : ℝ) + 1) < sSup S by linarith [hinv n])
    exact (hGm hslt.le).trans hs
  have hc : G (sSup S) ≤ μ B / 2 := by
    have hsub : B ∩ ψ ⁻¹' Iic (sSup S) ⊆ B ∩ ψ ⁻¹' Iio (sSup S) ∪ ψ ⁻¹' {sSup S} := by
      rintro x ⟨hxB, hx⟩
      rcases lt_or_eq_of_le (show ψ x ≤ sSup S from hx) with h | h
      · exact Or.inl ⟨hxB, h⟩
      · exact Or.inr h
    have hsing : μ (ψ ⁻¹' {sSup S}) = 0 :=
      Set.Subsingleton.measure_zero (subsingleton_singleton.preimage hψi) μ
    calc G (sSup S) ≤ μ (B ∩ ψ ⁻¹' Iio (sSup S) ∪ ψ ⁻¹' {sSup S}) := measure_mono hsub
      _ ≤ μ (B ∩ ψ ⁻¹' Iio (sSup S)) + μ (ψ ⁻¹' {sSup S}) := measure_union_le _ _
      _ ≤ μ B / 2 := by rw [hsing, add_zero]; exact hb
  exact ⟨B ∩ ψ ⁻¹' Iic (sSup S), inter_subset_left, hmeas _, le_antisymm hc ha⟩
section Split
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]
open Classical in
/-- A measurable subset of `B` of half the measure of `B`, when `B` is measurable. -/
noncomputable def half (B : Set (ℕ → Bool)) : Set (ℕ → Bool) :=
  if hB : MeasurableSet B then (exists_measurableSet_subset_measure_eq_half μ hB).choose else ∅
noncomputable def cell : List Bool → Set (ℕ → Bool)
  | [] => univ
  | b :: s => if b then half μ (cell s) else cell s \ half μ (cell s)
open Classical in
/-- The choices that lead to the cell of level `n` that contains `x`, the last one first. -/
noncomputable def pre (x : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => decide (x ∈ half μ (cell μ (pre x n))) :: pre x n
open Classical in
/-- The map that sends `x` to its sequence of choices in the halving tree. -/
noncomputable def split (x : ℕ → Bool) (n : ℕ) : Bool :=
  decide (x ∈ half μ (cell μ (pre μ x n)))
def revPrefix (v : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => v n :: revPrefix v n
end Split
end MeasureTheory
namespace AddUN
end AddUN


