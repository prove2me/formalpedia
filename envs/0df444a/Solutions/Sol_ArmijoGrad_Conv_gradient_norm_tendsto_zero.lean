-- Prove2me | solution 1 for ArmijoGrad.Conv.gradient_norm_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:34:37.860528+00:00
-- url     : https://prove2.me/submissions/45dec16e-a798-4792-be34-d51f5770b301

import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology


namespace ArmijoGrad.Conv

theorem gntz_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 < δ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x0)
    (hseq : ∀ k, x (k + 1) ∈ sdSet f (x k) δ) :
    Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0) := by
  obtain ⟨lb, hlb⟩ := hbdd
  have hstep : ∀ k, f (x (k+1)) ≤ f (x k) - δ * ‖gradient f (x k)‖ ^ 2 := by
    intro k
    obtain ⟨t, -, -, h⟩ := hseq k
    linarith
  have hsum : ∀ N, ∑ k ∈ Finset.range N, ‖gradient f (x k)‖ ^ 2 ≤ (f (x 0) - lb) / δ := by
    intro N
    have : δ * ∑ k ∈ Finset.range N, ‖gradient f (x k)‖ ^ 2 ≤ f (x 0) - f (x N) := by
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, mul_add]; linarith [hstep N]
    have hl : lb ≤ f (x N) := hlb ⟨x N, rfl⟩
    rw [le_div_iff₀ hδ]; linarith
  have hs : Summable (fun k => ‖gradient f (x k)‖ ^ 2) :=
    summable_of_sum_range_le (fun k => by positivity) hsum
  have h2 := hs.tendsto_atTop_zero
  have h3 := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- fencing lemma -/
theorem fence_core (φ : ℝ → ℝ) (c t : ℝ) (hφ : ContinuousOn φ (Set.Icc 0 t)) (h0 : φ 0 ≤ c)
    (hd : ∀ u ∈ Set.Ico 0 t, φ u = c → ∃ d < 0, HasDerivAt φ d u) :
    ∀ u ∈ Set.Icc 0 t, φ u ≤ c := by
  intro u hu
  by_cases ht : 0 ≤ t
  swap
  · exact absurd (hu.1.trans hu.2) ht
  change u ∈ {x | φ x ≤ c}
  revert u
  change Set.Icc 0 t ⊆ { x | φ x ≤ c }
  set s := { x | φ x ≤ c } ∩ Set.Icc 0 t
  have : IsClosed s := by
    simp only [s, Set.inter_comm]
    exact hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  apply this.Icc_subset_of_forall_exists_gt h0
  rintro x ⟨hxB : φ x ≤ c, xab⟩ y hy
  rcases hxB.lt_or_eq with hxB | hxB
  · refine Filter.nonempty_of_mem (Filter.inter_mem ?_ (Ioc_mem_nhdsGT hy))
    have : ∀ᶠ z in 𝓝[Set.Icc 0 t] x, φ z < c :=
      hφ x (Set.Ico_subset_Icc_self xab) (IsOpen.mem_nhds isOpen_Iio hxB)
    have : ∀ᶠ z in 𝓝[>] x, φ z < c := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
    exact this.mono fun y => le_of_lt
  · obtain ⟨d, hd0, hdd⟩ := hd x xab hxB
    have HB : ∀ᶠ z in 𝓝[>] x, slope φ x z < 0 :=
      (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1 hdd.hasDerivWithinAt
        (Iio_mem_nhds hd0)
    have HB2 : ∀ᶠ z in 𝓝[>] x, z ∈ Set.Ioc x y := Ioc_mem_nhdsGT hy
    obtain ⟨z, hz1, hz2⟩ := (HB.and HB2).exists
    refine ⟨z, ?_, hz2⟩
    have hzx : 0 < z - x := sub_pos.2 hz2.1
    rw [slope_def_field, div_neg_iff] at hz1
    change φ z ≤ c
    rcases hz1 with h | h <;> linarith [h.1, h.2]

end ArmijoGrad.Conv

open ArmijoGrad.Conv


theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 < δ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x0)
    (hseq : ∀ k, x (k + 1) ∈ sdSet f (x k) δ) :
    Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0) := by
  exact gntz_core f hbdd x0 δ hδ x hx0 hseq
