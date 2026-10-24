-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
-- name    : KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:04:39.774834+00:00
-- url     : https://prove2.me/theorems/b391615e-bd2d-4ed7-b891-75926f587f5a
-- title:
--   Finite-sum ENNReal mean inequalities
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `ENNReal.lintegral_Lp_finsum_le` bounds the $L^p$ seminorm of a finite sum of nonnegative measurable `ENNReal` functions by the sum of their seminorms for $p≥1$, and `ENNReal.rpow_finsetSum_le_finsetSum_rpow` bounds a finite sum raised to an exponent $0<p≤1$ by the sum of the individual powers.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/MeanInequalities.lean#L24-L52 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.MeanInequalities`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_MeanInequalities`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/MeanInequalities.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ENNReal
namespace ENNReal
lemma lintegral_Lp_finsum_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    {ι : Type*} {f : ι → α → ENNReal} {I : Finset ι}
    (hf : ∀ i ∈ I, AEMeasurable (f i) μ) (hp : 1 ≤ p) :
    (∫⁻ (a : α), (∑ i ∈ I, f i) a ^ p ∂μ) ^ (1 / p) ≤
      ∑ i ∈ I, (∫⁻ (a : α), f i a ^ p ∂μ) ^ (1 / p) := by
  classical
  induction I using Finset.induction with
  | empty => simpa using Or.inl (by bound)
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    refine (ENNReal.lintegral_Lp_add_le (hf i (by simp))
      (I.aemeasurable_sum (fun j hj => hf j (by simp [hj]))) hp).trans ?_
    gcongr
    exact ih (fun j hj => hf j (by simp [hj]))
lemma rpow_finsetSum_le_finsetSum_rpow {p : ℝ} {ι : Type*} {I : Finset ι} {f : ι → ℝ≥0∞}
    (hp : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ I, f i) ^ p ≤ ∑ i ∈ I, f i ^ p := by
  classical
  induction I using Finset.induction with
  | empty => simpa using by bound
  | insert i I hi ih => simpa [Finset.sum_insert hi] using
      (ENNReal.rpow_add_le_add_rpow _ _ (le_of_lt hp) hp1).trans (by gcongr)
end ENNReal


