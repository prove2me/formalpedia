-- Prove2me | Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws
-- name    : AssadiSemiStreaming_Greedy_WalkLaws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:38:37.271206+00:00
-- url     : https://prove2.me/theorems/7720c26f-2392-4396-a006-48a0f7c6df53
-- title:
--   Absorption-maximum probabilities and the symmetric starting weights
-- statement:
--   Use the published fair absorbed chain on {0,…,2m}. The joint probability of absorption at zero and maximum j is a sum over all possible first absorption times t≥0. Each summand enumerates every length-t trajectory, weights it by the published product of transition probabilities, and selects paths starting at s, first hitting zero at their last position, avoiding 2m, and having maximum exactly j including the starting position. The countable sum takes nonnegative extended-real values, so divergence is never silently assigned zero. This defines the full infinite-time event without a horizon cutoff. Define γ_m=2m(m+1)/(3m+1) and μ(i)=γ_m 2(2m+1)/((2m−i)(2m−i+1)(2m−i+2)) for 1≤i≤m, and zero otherwise. The formulas are rational, with canonical real casts for probability weights. Mixtures sum these weights times the corresponding laws over all states. Zero absorption uses the published first-passage sum. Normalization of μ is a conclusion of Lemma 5.1, not an assumption used to define the mixture.
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), §2, printed p. 3 / PDF 5; Lemma 5.1 and Eq. (9), printed p. 13 / PDF 15; Appendix C, printed p. 42 / PDF 44

import Mathlib
import Definitions.Def_mm_classical
open scoped ENNReal

namespace AssadiSemiStreaming.Greedy

/-- First absorption at zero after t transitions, with maximum exactly j.
The starting state counts toward the maximum. -/
noncomputable def firstZeroMaxMass (m : ℕ) (s : Fin (2 * m + 1)) (j t : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑ w : Fin (t + 1) → Fin (2 * m + 1),
    if w 0 = s ∧ w (Fin.last t) = 0 ∧
      (∀ i : Fin (t + 1), i ≠ Fin.last t → w i ≠ 0) ∧
      (∀ i, (w i).val < 2 * m) ∧
      (Finset.univ.sup (fun i => (w i).val)) = j
    then ENNReal.ofReal (MarkovMixing.pathWeight (MarkovMixing.gamblersChain (2 * m)) w)
    else 0

/-- Countably many disjoint first-absorption events, with no finite cutoff. -/
noncomputable def zeroMaxProb (m : ℕ) (s : Fin (2 * m + 1)) (j : ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ, firstZeroMaxMass m s j t

noncomputable def gamma (m : ℕ) : ℚ := (2 * m * (m + 1) : ℚ) / (3 * m + 1)

noncomputable def mu (m i : ℕ) : ℚ :=
  if 1 ≤ i ∧ i ≤ m then
    gamma m * (2 * (2 * m + 1)) /
      (((2 * m : ℚ) - i) * ((2 * m : ℚ) - i + 1) * ((2 * m : ℚ) - i + 2))
  else 0

noncomputable def mixtureMaxProb (m j : ℕ) : ℝ≥0∞ :=
  ∑ s : Fin (2 * m + 1), ENNReal.ofReal (mu m s.val : ℝ) * zeroMaxProb m s j

/-- Mixture of the published first-passage law, with normalization a theorem. -/
noncomputable def mixtureZeroProb (m : ℕ) : ℝ :=
  ∑ s : Fin (2 * m + 1), (mu m s.val : ℝ) *
    MarkovMixing.hitBeforeProb (MarkovMixing.gamblersChain (2 * m)) s 0 (Fin.last (2 * m))

end AssadiSemiStreaming.Greedy


