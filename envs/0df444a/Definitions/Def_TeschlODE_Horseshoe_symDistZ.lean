-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_symDistZ
-- name    : TeschlODE_Horseshoe_symDistZ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:40:44.373882+00:00
-- url     : https://prove2.me/theorems/63af5d2d-8a08-42af-a975-c3fea9b73657
-- title:
--   The metric (11.35) on the two-sided sequence space $\Sigma_N$
-- statement:
--   On the two-sided space $\Sigma_N = \{0, \dots, N-1\}^{\mathbb{Z}}$ the book uses the metric
--   $$d(x, y) = \frac12 \sum_{n \in \mathbb{N}_0} \frac{|x_n - y_n| + |x_{-n} - y_{-n}|}{N^n}.$$
--   For $N \ge 2$ the series converges, since its $n$-th term is at most $2(N-1)/N^n$. The index $0$ is counted twice, once in each summand, and the factor $\tfrac12$ compensates for that.
--
--   **Formalization Note.** This is a function, not a `MetricSpace` instance. It is used explicitly in the continuity clauses of Theorem 13.1.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 306, §11.5, Eq. (11.35)

import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §11.5, p. 306, (11.35): the metric on the two-sided space `Σ_N = {0, …, N − 1}^ℤ`,
`d(x, y) = ½ ∑_{n ∈ ℕ₀} (|xₙ − yₙ| + |x₋ₙ − y₋ₙ|) / Nⁿ`. For `N ≥ 2` the series converges,
being bounded termwise by `2(N − 1)/Nⁿ`. -/
noncomputable def symDistZ (N : ℕ) (x y : ℤ → Fin N) : ℝ :=
  1 / 2 * ∑' n : ℕ,
    (|((x n : ℕ) : ℝ) - ((y n : ℕ) : ℝ)| + |((x (-(n : ℤ)) : ℕ) : ℝ) - ((y (-(n : ℤ)) : ℕ) : ℝ)|) /
      (N : ℝ) ^ n

end TeschlODE.Horseshoe


