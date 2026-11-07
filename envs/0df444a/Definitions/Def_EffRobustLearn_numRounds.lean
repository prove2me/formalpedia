-- Prove2me | Definitions.Def_EffRobustLearn_numRounds
-- name    : EffRobustLearn_numRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:49.84378+00:00
-- url     : https://prove2.me/theorems/3662551b-2855-4a9d-b6f5-5399c06925c2
-- title:
--   The parameters of Algorithm 1
-- statement:
--   Algorithm 1 uses $T=\lceil(300/\varepsilon)^4\rceil$ rounds, majority parameter $k=\lceil64/\varepsilon^2\rceil$, step sizes $\gamma_t=\min(1,2/\sqrt t)$, learning rate $\alpha=1/(2T^{3/4})$, and the weight bound $b=3(|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|)T^{1/4}/\min(|\bar S_{\mathrm{inp}}|,|S_{\mathrm{ref}}|)$ of Lemma 3.8's proof.
--
--   **Formalization Note** Rounds are 1-based, as in the paper.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 1, lines 4, 6, 8, p.14 (PDF p.15); proof of Lemma 3.8, p.16 (PDF p.17)

import Mathlib

namespace EffRobustLearn

/-- The number of rounds of Algorithm 1, line 4, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.14: `T = ⌈(300/ε)⁴⌉`. -/
noncomputable def numRounds (ε : ℝ) : ℕ := ⌈(300 / ε) ^ 4⌉₊

/-- The majority parameter of Algorithm 1, line 6, p.14: `k = ⌈64/ε²⌉`. -/
noncomputable def majParam (ε : ℝ) : ℕ := ⌈64 / ε ^ 2⌉₊

/-- The step size of Algorithm 1, line 4, p.14: `γ_t = min(1, 2/√t)`. Rounds are 1-based, `t = 1, …, T`. -/
noncomputable def stepSize (t : ℕ) : ℝ := min 1 (2 / Real.sqrt t)

/-- The learning rate of Algorithm 1, line 8, p.14: `α = 1/(2T^{3/4})`. -/
noncomputable def alphaStep (T : ℕ) : ℝ := 1 / (2 * (T : ℝ) ^ (3 / 4 : ℝ))

/-- The weight bound passed to Fact 3.2 in Lemma 3.8, p.16: `b = 3(|S̄inp| + |Sref|) T^{1/4} / min(|S̄inp|, |Sref|)`. -/
noncomputable def weightBound (n m T : ℕ) : ℝ :=
  3 * ((n : ℝ) + m) * (T : ℝ) ^ (1 / 4 : ℝ) / min (n : ℝ) m

end EffRobustLearn


