-- Prove2me | Definitions.Def_RecoveringBandits_gamma
-- name    : RecoveringBandits_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:29.449677+00:00
-- url     : https://prove2.me/theorems/857adeea-8ebf-4573-9438-b7154db3eb91
-- title:
--   The ratio $\gamma_K=\max_a \frac{a}{a+1}\cdot\frac{K}{K+a}$
-- statement:
--   For a positive integer $K$,
--
--   $$\gamma_K=\max_{a\in\mathbb Z_+}\frac{a}{a+1}\cdot\frac{K}{K+a}.$$
--
--   It is the long-run approximation ratio of the offline purely periodic planning algorithm: $\gamma_1=1/4$, and $1-\gamma_K=O(1/\sqrt K)$.
--
--   **Formalization Note** Written as the supremum over $a\ge1$; the terms tend to $0$, so the supremum is attained and equals the maximum.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Theorem 1, p.15; §4.3, p.14

import Mathlib

namespace RecoveringBandits

/-- **`γ_K = max_{a ∈ ℤ₊} a/(a+1) · K/(K+a)`** (arXiv:2106.14813v2, Theorem 1, p.15; §4.3, p.14).

**Formalization Note.** Written as the supremum over `a ≥ 1`. The terms are in `[0, 1)` and tend
to `0` as `a → ∞`, so the supremum is attained and equals the paper's maximum (for `K ≥ 1`). -/
noncomputable def gamma (K : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ a : ℕ, 1 ≤ a ∧ v = ((a : ℝ) / (a + 1)) * ((K : ℝ) / (K + a))}

end RecoveringBandits


