-- Prove2me | Definitions.Def_ListReplicableBias_LowerBound_Supplement_Estimation
-- name    : ListReplicableBias_LowerBound_Supplement_Estimation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:22:29.087212+00:00
-- url     : https://prove2.me/theorems/d4350497-0b28-432a-881b-ccd7564fe372
-- title:
--   Definition 3.1 — coin-bias estimators
-- statement:
--   Let $d,N\in\mathbb N$, $\varepsilon,\delta>0$, and let $A$ be an $N$-toss sampling algorithm on $d$ coins (the published model of §3.2). $A$ solves the $(d,\varepsilon,\delta)$-CoinBiasEstimationProblem if for every bias vector $p\in[0,1]^d$ its output $\hat p$ satisfies
--   $$\Pr_p\big(\|\hat p-p\|_\infty\le\varepsilon\big)\ge1-\delta .$$
--   The probability is over the coin tosses and the algorithm's internal randomness.
--
--   This is the accuracy notion behind the classical $\Omega(d/\varepsilon^2)$ estimation lower bound (Lemma 3.2), which the $k$-list lower bound uses for very large $k$.
--
--   **Formalization Note** The failure output $\bot$ (`none`) never counts as an accurate estimate. Probabilities are `outputProb`, the published transcript-law probability of an output event.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Definition 3.1, PDF p. 3

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Sampling

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Definition 3.1, PDF p. 3: an algorithm solves the (d, ε, δ)-coin-bias
estimation problem if for every bias vector in the unit cube its output lies
within sup-norm distance ε of the bias vector with probability at least 1 − δ.
The failure output `none` counts as a miss. -/
def IsBiasEstimator {d N : ℕ} (A : SamplingAlgorithm d N) (ε δ : ℝ) : Prop :=
  ∀ p ∈ cube d 0 1,
    1 - δ ≤ outputProb A p (some '' {y : Fin d → ℝ | ‖y - p‖ ≤ ε})

end ListReplicableBias.LowerBound.Supplement


