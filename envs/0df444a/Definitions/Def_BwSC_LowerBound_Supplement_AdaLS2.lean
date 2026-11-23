-- Prove2me | Definitions.Def_BwSC_LowerBound_Supplement_AdaLS2
-- name    : BwSC_LowerBound_Supplement_AdaLS2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:43:29.135827+00:00
-- url     : https://prove2.me/theorems/67bbf712-2aaa-4cd3-8faf-4a9bf65d4a47
-- title:
--   Algorithm 6 (cross-reference corrected) — full AdaLS2 with the replacement epoch grids
-- statement:
--   AdaLS2 uses the same full adaptive logic, initial uniform partition, confidence decisions, elimination and final commitment as AdaLS. Its only change is the pair of grids, for $q=q(S,K)$ and $r=r(S,K)$:
--   $$t^{(1)}_0=t^{(2)}_0=0,\quad t^{(1)}_j=\left\lfloor(K-r)^{1-j/(q+1)}T^{j/(q+1)}\right\rfloor,\quad t^{(2)}_j=\left\lfloor K^{1-j/(q+2)}T^{j/(q+2)}\right\rfloor.$$
--   The respective ranges are $1\le j\le q+1$ and $1\le j\le q+2$.
--
--   This definition shares the operational replay with AdaLS, so no adaptive or elimination step is omitted when the schedules change.
--
--   **Formalization Note** Algorithm 6's instruction “Lines 1 to 18 of Algorithm 2” is read as all its actual Lines 1–16: Algorithm 2 ends at Line 16. It inherits the disclosed one-arm, zero-budget, no-sample and horizon completions. The new second grid uses $q+2$, independently of Theorem 6's printed $q+1$ second rate.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, p. 38, Algorithm 6; p. 18, Algorithm 2

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_AdaLS

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.Supplement

/-- Algorithm 6, p. 38, first grid. -/
noncomputable def gapGridOne (S K T j : ℕ) : ℕ :=
  if j = 0 then 0 else
    ⌊((K : ℝ) - (rIdx S K : ℝ)) ^ (1 - (j : ℝ) / ((qIdx S K : ℝ) + 1)) *
      (T : ℝ) ^ ((j : ℝ) / ((qIdx S K : ℝ) + 1))⌋₊

/-- Algorithm 6, p. 38, second grid (q+2, not q+1). -/
noncomputable def gapGridTwo (S K T j : ℕ) : ℕ :=
  if j = 0 then 0 else
    ⌊(K : ℝ) ^ (1 - (j : ℝ) / ((qIdx S K : ℝ) + 2)) *
      (T : ℝ) ^ ((j : ℝ) / ((qIdx S K : ℝ) + 2))⌋₊

/-- Full AdaLS2: the same random partition and all actual Lines 1–16 of
Algorithm 2, with exactly Algorithm 6's replacement grids. -/
def IsAdaLS2 {K : ℕ} (hK : 0 < K) (S T : ℕ) (π : BanditPolicy K) : Prop :=
  IsReplayPolicy hK S T (gapGridOne S K T) (gapGridTwo S K T) π

end BwSC.LowerBound.Supplement


