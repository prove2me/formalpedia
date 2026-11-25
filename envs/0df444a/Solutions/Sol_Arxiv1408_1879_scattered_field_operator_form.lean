-- Prove2me | solution 1 for Arxiv1408_1879.scattered_field_operator_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:41:15.525397+00:00
-- url     : https://prove2.me/submissions/193ef68d-e467-4f66-8663-933f545a6e0e

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

theorem scattered_field_operator_form (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (x z : ℝ) (hx : 0 ≤ x) :
    (IntervalIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') volume 0 x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') 0 ∧
        twoWayField k h f x z = leftOp k h f x z + rightOp k h f x z) ∧
    (∀ g : ℝ → ℂ, (∀ x' ∈ Set.Icc 0 x, g x' = f x') → leftOp k h g x z = leftOp k h f x z) ∧
    (∀ g : ℝ → ℂ, (∀ x' ∈ Set.Ici x, g x' = f x') → rightOp k h g x z = rightOp k h f x z) := by
  refine ⟨fun h0 hi => tw_split _ x hx h0 hi, fun g hg => ?_, fun g hg => ?_⟩
  · unfold leftOp
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hx] at hy
    simp [hg y hy]
  · unfold rightOp improperIntegral limUnder
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [eventually_ge_atTop x] with T hT
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hT] at hy
    simp [hg y hy.1]

end Arxiv1408_1879
open Arxiv1408_1879 in
theorem solution (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (x z : ℝ) (hx : 0 ≤ x) :
    (IntervalIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') volume 0 x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') 0 ∧
        twoWayField k h f x z = leftOp k h f x z + rightOp k h f x z) ∧
    (∀ g : ℝ → ℂ, (∀ x' ∈ Set.Icc 0 x, g x' = f x') → leftOp k h g x z = leftOp k h f x z) ∧
    (∀ g : ℝ → ℂ, (∀ x' ∈ Set.Ici x, g x' = f x') → rightOp k h g x z = rightOp k h f x z) := by
  exact scattered_field_operator_form k h f x z hx
