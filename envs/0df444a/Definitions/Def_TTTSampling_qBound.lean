-- Prove2me | Definitions.Def_TTTSampling_qBound
-- name    : TTTSampling_qBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:15.217065+00:00
-- url     : https://prove2.me/theorems/d90dc047-2ac6-4ff4-aece-1975efb751e0
-- title:
--   The query bound $n|\Sigma|R^{12}\sqrt{\log|\mathcal F|}\log\frac1\delta\log\frac{R\log|\mathcal F|}{\delta}$
-- statement:
--   For $n,s,m\in\mathbb N$ and reals $R,\delta$, the **query bound** of Theorem 3.2 is
--
--   $$
--   q(n,s,R,m,\delta)=n\cdot s\cdot R^{12}\cdot\sqrt{\log m}\cdot\log\frac1\delta\cdot\log\frac{R\log m}{\delta},
--   $$
--
--   with natural logarithms; it is used with $s=|\Sigma|$ and $m=|\mathcal F|$.
--
--   **Formalization Note** At $m=1$ the bound is $0$ (Lean's $\log 0=0$), the exact-sampling case in which no query is needed; the paper's expression is $0\cdot\log 0$ there.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, p.18 (PDF p.20); Lemma 3.15, p.30 (PDF p.32)

import Mathlib

namespace TTTSampling

/-- The **query bound** of Theorem 3.2,
`n · |Σ| · R¹² · √(log |ℱ|) · log(1/δ) · log(R log |ℱ| / δ)`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, printed
p.18 (PDF p.20), and Lemma 3.15, p.30 (PDF p.32). Arguments: `n` the length, `s = |Σ|`, `R` the
accuracy parameter, `m = |ℱ|`, `δ` the accuracy.

**Formalization Note** Natural logarithms (`Real.log`), as the `O(·)` absorbs the base. At
`m = 1` Lean's `Real.log 1 = 0` makes the bound `0`, the exact-sampling case where no query is
needed (the paper's expression is `0 · log 0` there). -/
noncomputable def qBound (n s : ℕ) (R : ℝ) (m : ℕ) (δ : ℝ) : ℝ :=
  n * s * R ^ 12 * Real.sqrt (Real.log m) * Real.log (1 / δ) * Real.log (R * Real.log m / δ)

end TTTSampling


