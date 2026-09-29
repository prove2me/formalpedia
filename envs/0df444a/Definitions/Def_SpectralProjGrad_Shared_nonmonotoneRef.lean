-- Prove2me | Definitions.Def_SpectralProjGrad_Shared_nonmonotoneRef
-- name    : SpectralProjGrad_Shared_nonmonotoneRef
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:59:00.178986+00:00
-- url     : https://prove2.me/theorems/82dd701e-e043-4e62-b8f9-05c6e36fe23a
-- title:
--   Nonmonotone reference value $\max_{0\le j\le\min\{k,M-1\}} f(x_{k-j})$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $(x_k)_{k\ge0}$ be a sequence in $\mathbb R^n$ and let $M\ge1$ be an integer. The **nonmonotone reference value** at iteration $k$ is the largest objective value among the current iterate and the previous $\min\{k,M-1\}$ ones:
--
--   $$
--   R_k=\max_{0\le j\le \min\{k,\,M-1\}} f(x_{k-j}).
--   $$
--
--   It is the baseline of the nonmonotone Armijo conditions (1) (SPG1) and (3) (SPG2): a trial point is compared with the worst of the last $M$ objective values rather than with $f(x_k)$ alone. For $M=1$ it reduces to $f(x_k)$ and the line search is monotone.
--
--   Used by both missions of this paper: 02-spg1 (SPG1; p. 3, the maximum in test (1) of Algorithm 2.1) and 01-spg2 (SPG2; p. 4, the maximum in test (3) of Algorithm 2.2).
--
--   **Formalization Note** Iterations are indexed from $0$, so $R_0=f(x_0)$. The maximum is `Finset.sup'` over $j\in\{0,\dots,\min\{k,M-1\}\}$. For $M=0$ the Lean formula (with truncated $M-1=0$) gives $f(x_k)$; every statement that uses it assumes $M\ge1$.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 3, Algorithm 2.1, Step 2.3, the maximum in (1); p. 4, Algorithm 2.2 Step 2.3, eq. (3) (same maximum)

import Mathlib

namespace SpectralProjGrad.Shared

/-- The nonmonotone reference value of iteration `k` (0-based):
`max_{0 ≤ j ≤ min {k, M-1}} f(x_{k-j})`, the largest objective value among the last
`min {k, M-1} + 1` iterates `x_k, x_{k-1}, …`. -/
noncomputable def nonmonotoneRef {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M k : ℕ) : ℝ :=
  (Finset.range (min k (M - 1) + 1)).sup' Finset.nonempty_range_add_one
    (fun j => f (x (k - j)))

end SpectralProjGrad.Shared


