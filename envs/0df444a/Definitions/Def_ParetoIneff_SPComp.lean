-- Prove2me | Definitions.Def_ParetoIneff_SPComp
-- name    : ParetoIneff_SPComp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:35.395092+00:00
-- url     : https://prove2.me/theorems/df5f0e69-f8a3-4a66-9b88-483f43fcd321
-- title:
--   Component of $\mathcal{SP}_\alpha$
-- statement:
--   The single-task component of the **second-price mechanism with $\alpha$-relative reserve price**: given reports $s$, a machine $\iota$ with the smallest report receives the task, the reserve price is $r=\alpha\cdot\min_{i\in N}s_i$, and machine $\iota$ is paid
--   $$
--   \min\Bigl\{\min_{i\in N\setminus\{\iota\}}s_i,\ r\Bigr\},
--   $$
--   while every other machine is paid nothing.
--
--   The reserve caps the second-price payment at a factor $\alpha$ above the winning report.
--
--   **Formalization Note** The range of Definition 6 is $\alpha\ge1$. The inner minimum needs a second machine, so every theorem assumes $n\ge2$; at $n=1$ the Lean term is a junk value that no theorem uses.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definition 6, p.16

import Mathlib
import Definitions.Def_ParetoIneff_SingleTaskMech

open NNReal

namespace ParetoIneff

/-- The single-task component `𝒮𝒫_α^j` of the **second-price mechanism with `α`-relative reserve
price**, Definition 6, arXiv:1809.03454v7, p.16. With winner selector `σ` (a machine with the
smallest report) and reports `s ∈ ℝ≥0ⁿ`: the reserve price is `r = α · min_{i∈N} sᵢ`; the task goes
to `ι = σ s`; machine `ι` is paid `min{min_{i∈N∖{ι}} sᵢ, r}`; every other machine is paid `0`.

**Formalization Note** `α` is a real number; the reserve uses `α.toNNReal`, which equals `α` for
the paper's range `α ≥ 1`. The minima are infima in `ℝ≥0`. The minimum over `N ∖ {ι}` is over an
empty set when `n = 1`, where the paper's payment is undefined and the infimum is the junk value
`0`; every theorem about `𝒮𝒫_α` assumes `n ≥ 2`. -/
noncomputable def SPComp {n : ℕ} (α : ℝ) (σ : (Fin n → ℝ≥0) → Fin n) : SingleTaskMech n where
  alloc := σ
  pay s i :=
    if i = σ s then min (⨅ i' : {i' : Fin n // i' ≠ σ s}, s i') (α.toNNReal * ⨅ i', s i') else 0

end ParetoIneff


