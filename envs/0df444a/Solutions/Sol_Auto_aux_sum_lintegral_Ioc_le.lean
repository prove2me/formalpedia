-- Prove2me | solution 1 for Auto.aux_sum_lintegral_Ioc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:12.749716+00:00
-- url     : https://prove2.me/submissions/b0214c12-8b91-4c3a-a010-9adfedee94c2

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {μ : Measure ℝ}
    (t : Fin (J + 1) → ℝ) (ht : Monotone t) (f : ℝ → ℝ≥0∞)
    {α β : ℝ} (hα : α ≤ t 0) (hβ : t (Fin.last J) ≤ β) :
    (∑ j : Fin J, ∫⁻ x in Set.Ioc (t j.castSucc) (t j.succ), f x ∂μ) ≤
      ∫⁻ x in Set.Icc α β, f x ∂μ := by
  let s : Fin J → Set ℝ := fun j ↦ Set.Ioc (t j.castSucc) (t j.succ)
  have hs_meas (j : Fin J) : MeasurableSet (s j) := measurableSet_Ioc
  have hs_disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J))) s := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact Ioc_disjoint_Ioc_of_le (ht (Fin.succ_le_castSucc_iff.mpr hijlt))
    · exact (Ioc_disjoint_Ioc_of_le
        (ht (Fin.succ_le_castSucc_iff.mpr hjilt))).symm
  have hsum : (∑ j : Fin J, ∫⁻ x in s j, f x ∂μ) =
      ∫⁻ x in ⋃ j ∈ (Finset.univ : Finset (Fin J)), s j, f x ∂μ := by
    symm
    simpa using (lintegral_biUnion_finset hs_disjoint (fun j _ ↦ hs_meas j) f)
  rw [hsum]
  apply lintegral_mono_set
  intro x hx
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨j, hj, hx⟩
  have hfirst : (0 : Fin (J + 1)) ≤ j.castSucc := Fin.zero_le _
  have hleft : α < x := (hα.trans (ht hfirst)).trans_lt hx.1
  have hjle : j.succ ≤ Fin.last J := Fin.le_last _
  have hright : x ≤ β := hx.2.trans ((ht hjle).trans hβ)
  exact ⟨hleft.le, hright⟩
end Auto
