-- Prove2me | Definitions.Def_WeightedMajority_Shifting_Supplement_LazySampling
-- name    : WeightedMajority_Shifting_Supplement_LazySampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:55:45.197307+00:00
-- url     : https://prove2.me/theorems/6e342a77-3bf9-46fd-8504-c11fef82b500
-- title:
--   Lazy resampling with independent weighted-uniform choices
-- statement:
--   For a finite ordered pool with arbitrary positive initial weights, the published WMR weights are updated on every trial at $\beta=0$. Pool predictions are binary, so a mistaken member's weight becomes zero and a correct member's weight is unchanged. The master predicts with a selected member. Initially and immediately after a master mistake it selects afresh; after a correct prediction it retains the preceding member.
--
--   For a fresh uniform number $r^j$, selected member $k$ satisfies
--
--   $$\frac{\sum_{i<k}w_i^j}{s^j}<r^j\le\frac{\sum_{i\le k}w_i^j}{s^j},\qquad s^j=\sum_iw_i^j.$$
--
--   The coins have the uniform law on $[0,1]$ and are jointly independent of each other and of the entire external sequence. Unused coins may be drawn in advance. At $r^j=0$, a null event, selection is arbitrary. The pre-trial total is positive almost surely whenever a prediction is requested; the final total may be zero. This is the domain on which the source's normalized sampling is defined, and it does not require a consistent pool member. The relation contains no conditional-expectation conclusion.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, pp. 257–258, Theorem A.1 implementation; p. 233, update (5.1)

import Definitions.Def_WeightedMajority_Shifting_Supplement_StrongIndependence

open MeasureTheory ProbabilityTheory

namespace WeightedMajority.Shifting.Supplement

/-- Resample initially and immediately after a master mistake. -/
def resamples {Ω : Type*} (lam ρ : ℕ → Ω → ℝ) : ℕ → Ω → Prop
  | 0, _ => True
  | j + 1, ω => lam j ω ≠ ρ j ω

/-- Lower and upper cumulative weights for the ordered finite pool. -/
noncomputable def cumulative {Ω : Type*} {n : ℕ} (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ)
    (ρ : ℕ → Ω → ℝ) (j k : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, if i.val < k then WeightedMajority.Randomized.weight w1 F x ρ j i ω else 0

/-- The Appendix's lazy implementation of WMR. All pool weights update on every trial;
only the member choice is lazy. Random numbers for unused trials can be drawn in advance.
Their joint independence includes the entire external sequence as one block. No conditional
mean or independence conclusion is assumed here. Sampling is required only at positive
pre-trial total weight; the terminal total after the last update may be zero. -/
structure IsLazyWMRRun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (t : ℕ) (w1 : Fin n → ℝ) (F : ℕ → Fin n → ℝ → ℝ → ℝ)
    (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (r : ℕ → Ω → ℝ) (selected : ℕ → Ω → Fin n) : Prop where
  model : WeightedMajority.Randomized.IsWMRModel t 0 w1 F x ρ lam
  binary_pool : ∀ j < t, ∀ i ω, x j i ω = 0 ∨ x j i ω = 1
  pretrial_positive : ∀ j < t, ∀ᵐ ω ∂P,
    0 < WeightedMajority.Randomized.totalWeight w1 F x ρ j ω
  selected_measurable : ∀ j < t, Measurable (selected j)
  coins_measurable : ∀ j < t, Measurable (r j)
  coins_uniform : ∀ j < t, P.map (r j) = volume.restrict (Set.Icc (0 : ℝ) 1)
  independent : iIndep (fun q : Option (Fin t) => match q with
    | none => external t x ρ
    | some j => MeasurableSpace.comap (r j.val) inferInstance) P
  prediction : ∀ j < t, ∀ᵐ ω ∂P, lam j ω = x j (selected j ω) ω
  fresh_choice : ∀ j < t, ∀ᵐ ω ∂P, resamples lam ρ j ω → 0 < r j ω →
    cumulative w1 F x ρ j (selected j ω).val ω /
        WeightedMajority.Randomized.totalWeight w1 F x ρ j ω < r j ω ∧
    r j ω ≤ cumulative w1 F x ρ j ((selected j ω).val + 1) ω /
        WeightedMajority.Randomized.totalWeight w1 F x ρ j ω
  retain_choice : ∀ j, j + 1 < t → ∀ᵐ ω ∂P,
    lam j ω = ρ j ω → selected (j + 1) ω = selected j ω

end WeightedMajority.Shifting.Supplement


