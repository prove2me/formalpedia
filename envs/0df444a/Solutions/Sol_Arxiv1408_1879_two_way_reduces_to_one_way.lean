-- Prove2me | solution 1 for Arxiv1408_1879.two_way_reduces_to_one_way
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:41:04.661145+00:00
-- url     : https://prove2.me/submissions/48b236fa-60b1-4ead-9331-cc5ab55c6662

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic
set_option autoImplicit false

open MeasureTheory Filter Topology
namespace Arxiv1408_1879

lemma tw_split (f : ℝ → ℂ) (x : ℝ) (hx : 0 ≤ x) (h0 : IntervalIntegrable f volume 0 x)
    (hi : ImproperIntegrable f x) :
    ImproperIntegrable f 0 ∧ improperIntegral f 0 = (∫ t in (0 : ℝ)..x, f t) + improperIntegral f x := by
  obtain ⟨hint, I, hI⟩ := hi
  have hlim : Tendsto (fun T => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 ((∫ t in (0 : ℝ)..x, f t) + I)) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds.add hI)
    filter_upwards [eventually_ge_atTop x] with T hT
    exact intervalIntegral.integral_add_adjacent_intervals h0 (hint T hT)
  refine ⟨⟨fun T hT => ?_, _, hlim⟩, ?_⟩
  · rcases le_total T x with h | h
    · exact h0.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc.2 (Or.inl ⟨hT, h⟩)))
    · exact h0.trans (hint T h)
  · unfold improperIntegral
    rw [hlim.limUnder_eq, hI.limUnder_eq]

theorem two_way_reduces_to_one_way (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) :
    (∀ x z x' z' : ℝ, x' < x → greenTwoWay k x z x' z' = greenOneWay k x z x' z') ∧
    (∀ x z x' z' : ℝ, x ≤ x' → greenOneWay k x z x' z' = 0) ∧
    (∀ x z : ℝ, 0 ≤ x →
      leftOp k h f x z = ∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x') ∧
    (∀ x z : ℝ, 0 ≤ x →
      IntervalIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') volume 0 x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') x →
      twoWayField k h f x z =
        (∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x') + rightOp k h f x z) := by
  refine ⟨fun x z x' z' h => by simp [greenTwoWay, greenOneWay, h],
    fun x z x' z' h => by simp [greenOneWay, not_lt.2 h], fun x z hx => ?_, fun x z hx h0 hi => ?_⟩
  · unfold leftOp
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(Set.countable_singleton x).ae_notMem volume] with y hy hyI
    rw [Set.uIoc_of_le hx] at hyI
    have : y < x := lt_of_le_of_ne hyI.2 (by simpa using hy)
    simp [greenTwoWay, greenOneWay, this]
  · have hL : leftOp k h f x z = ∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x' := by
      unfold leftOp
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [(Set.countable_singleton x).ae_notMem volume] with y hy hyI
      rw [Set.uIoc_of_le hx] at hyI
      have : y < x := lt_of_le_of_ne hyI.2 (by simpa using hy)
      simp [greenTwoWay, greenOneWay, this]
    rw [← hL]
    exact (tw_split _ x hx h0 hi).2

end Arxiv1408_1879
open Arxiv1408_1879 in
theorem solution (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) :
    (∀ x z x' z' : ℝ, x' < x → greenTwoWay k x z x' z' = greenOneWay k x z x' z') ∧
    (∀ x z x' z' : ℝ, x ≤ x' → greenOneWay k x z x' z' = 0) ∧
    (∀ x z : ℝ, 0 ≤ x →
      leftOp k h f x z = ∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x') ∧
    (∀ x z : ℝ, 0 ≤ x →
      IntervalIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') volume 0 x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') x →
      twoWayField k h f x z =
        (∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x') + rightOp k h f x z) := by
  exact two_way_reduces_to_one_way ..
