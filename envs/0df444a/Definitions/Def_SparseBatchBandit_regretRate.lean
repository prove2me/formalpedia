-- Prove2me | Definitions.Def_SparseBatchBandit_regretRate
-- name    : SparseBatchBandit_regretRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:18.98685+00:00
-- url     : https://prove2.me/theorems/c540cfb5-0894-4b14-949a-878901631b8c
-- title:
--   The rate of Theorem 2
-- statement:
--   The rate of Theorem 2, without its constant:
--
--   $$
--   \frac{M^{3/2}\sqrt{\log K\,\log(KT)\,\log(dT)}}{\gamma\rho}\cdot\sqrt{Ts_0}\,\Big(\frac{T}{s_0}\Big)^{\frac{1}{2(2^M-1)}}.
--   $$
--
--   **Formalization Note** $2^M-1$ is computed in the reals and the exponents are real powers.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Theorem 2, p.16

import Mathlib

namespace SparseBatchBandit

/-- The rate of Theorem 2, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.16 (PDF 16):
`M^{3/2} √(log K log(KT) log(dT)) / (γρ) · √(Ts₀) · (T/s₀)^{1/(2(2^M−1))}`, without the constant.

**Formalization Note.** `2^M − 1` is computed in `ℝ`; the powers are real powers. -/
noncomputable def regretRate (T d K M s₀ : ℕ) (γ ρ : ℝ) : ℝ :=
  (M : ℝ) ^ ((3 : ℝ) / 2) *
    Real.sqrt (Real.log K * Real.log ((K : ℝ) * T) * Real.log ((d : ℝ) * T)) / (γ * ρ) *
    Real.sqrt ((T : ℝ) * s₀) * ((T : ℝ) / s₀) ^ ((1 : ℝ) / (2 * ((2 : ℝ) ^ M - 1)))

end SparseBatchBandit


