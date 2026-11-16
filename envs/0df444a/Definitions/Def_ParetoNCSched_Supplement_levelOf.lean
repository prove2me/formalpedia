-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_levelOf
-- name    : ParetoNCSched_Supplement_levelOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:34:19.648762+00:00
-- url     : https://prove2.me/theorems/ba0b13b5-6e5f-448b-913f-adee56d925ee
-- title:
--   The random level $L=w_y^{-1}(B)$
-- statement:
--   For $B\in(0,1)$, the level of $\mathrm{RT}_\rho$ is $L=w_y^{-1}(B)$, the level below which the layers contribute a fraction $B$ of $\Phi(y)$. It is defined as
--
--   $$L=\inf\{s\ge0: w_y(s)\ge B\},$$
--
--   which, since $w_y$ is continuous and strictly increasing on $[0,\max_j y_j]$ from $0$ to $1$, is the unique $s\in(0,\max_j y_j)$ with $w_y(s)=B$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, p.13; Appendix H, p.40

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_wy

namespace ParetoNCSched.Supplement

/-- **The random level `L = w_y⁻¹(B)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Algorithm 2, line 1, p.13, and Appendix H, p.40:
"The algorithm lets L = w_y^{-1}(B) be the level below which the layers contribute a fraction B of
Φ(y), which is well defined since 0 < B < 1."

`levelOf y B = inf {s ≥ 0 : w_y(s) ≥ B}`.

**Formalization Note.** For `n ≥ 1`, `y > 0` and `B ∈ (0, 1)`, `w_y` is continuous,
`w_y(0) = 0`, `w_y(y_n) = 1` and strictly increasing on `[0, y_n]` (p.39), so the infimum is
the unique `s ∈ (0, y_n)` with `w_y(s) = B`, the paper's inverse. Only such `B` are used. -/
noncomputable def levelOf {n : ℕ} (y : Fin n → ℝ) (B : ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ B ≤ wy y s}

end ParetoNCSched.Supplement


