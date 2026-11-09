-- Prove2me | Definitions.Def_NAMatchEst_bernDist
-- name    : NAMatchEst_bernDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:36.614822+00:00
-- url     : https://prove2.me/theorems/3ec82b27-0d68-4856-af3c-aba1fad23455
-- title:
--   Law of a Bernoulli vertex sample
-- statement:
--   The law of a **Bernoulli vertex sample** with inclusion probability $p$: every vertex is included independently with probability $p$, so a subset $S\subseteq V$ (given by its indicator) has probability
--
--   $$
--   \prod_{v\in S}p\prod_{v\notin S}(1-p).
--   $$
--
--   It is the product (the public `RandomQueryXOR.piDist`) over the vertices of a coin with success probability $p$, a finite probability distribution (`WildeQIT.FinDist`) on the indicator vectors $V\to\{0,1\}$. The paper's uniform samples with replacement use the public uniform distribution `ShallowShadows.ShadowNorm.uniformDist` on the functions $\{1,\dots,s\}\to V$.
--
--   **Formalization Note** The probability is clamped to $[0,1]$, so that the law is a probability distribution for every real $p$. Under the paper's standing assumption $cL/\sqrt\alpha\le 1$ (§3.2, p.19) all its inclusion probabilities lie in $[0,1]$ and the clamp does nothing.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, p.24 (PDF 28) and §3.8, p.28 (PDF 32)

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_uniformOn

namespace NAMatchEst

/-- The law of a **Bernoulli vertex sample**: every vertex is included independently with
probability `p`. It is the product (`RandomQueryXOR.piDist`) over the vertices of the coin on
`Bool` with `P(true) = p`, so the subset given by the indicator `S` has probability
`∏_v p^{S v} (1 − p)^{1 − S v}`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, p.24 (PDF 28): "Include every vertex independently in each of S^L and S^R with the
respective probabilities." and §3.8, p.28 (PDF 32) ("two Bernoulli vertex samples S^L, S^R").

**Formalization Note** A distribution in the sense of the public `WildeQIT.FinDist`. The coin
probability is clamped to `[0, 1]` (`max 0 (min p 1)`) so that the law is a probability
distribution for every real `p`. The source's probabilities lie in `[0, 1]` under its standing
assumption `cL/√α ⩽ 1` (§3.2, p.19), where the clamp does nothing. -/
noncomputable def bernDist {n : ℕ} (p : ℝ) : WildeQIT.FinDist (Fin n → Bool) :=
  RandomQueryXOR.piDist fun _ : Fin n =>
    { prob := fun b => if b then max 0 (min p 1) else 1 - max 0 (min p 1)
      nonneg := fun b => by
        have : max 0 (min p 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
        cases b
        · simp only [Bool.false_eq_true, if_false]; linarith
        · simp only [if_true]; exact le_max_left _ _
      sum_eq_one := by simp }

end NAMatchEst


