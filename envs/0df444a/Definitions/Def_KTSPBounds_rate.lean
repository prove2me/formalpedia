-- Prove2me | Definitions.Def_KTSPBounds_rate
-- name    : KTSPBounds_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:11.064668+00:00
-- url     : https://prove2.me/theorems/7858607d-ae80-4cc5-9362-305d43f4333c
-- title:
--   The rate $(k-1)/n^{\frac12(1+\frac1{k-1})}$
-- statement:
--   The quantity
--
--   $$
--   r(n,k) = \frac{k-1}{n^{\frac12\left(1+\frac1{k-1}\right)}}
--   $$
--
--   that governs the expected $k$-TSP length in Theorem 2. It equals $1/n$ at $k = 2$ and $(n-1)\,n^{-\frac12 - \frac{1}{2(n-1)}}$ at $k = n$.
--
--   **Formalization Note** The subtraction $k-1$ is real and the exponent is a real power. Theorems using it assume $k \ge 2$.
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, Theorem 2, p.9

import Mathlib

namespace KTSPBounds

/-- The rate `(k - 1) / n^{½(1 + 1/(k-1))}` of Theorem 2, p.9, Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1.

**Formalization Note.** `k - 1` is computed in `ℝ` and the exponent is a real power, so neither
natural-number subtraction nor natural-number division occurs. Every theorem of this mission
assumes `2 ≤ k`, so the denominator `k - 1` of the exponent is positive. -/
noncomputable def rate (n k : ℕ) : ℝ :=
  ((k : ℝ) - 1) / (n : ℝ) ^ ((1 / 2 : ℝ) * (1 + 1 / ((k : ℝ) - 1)))

end KTSPBounds


