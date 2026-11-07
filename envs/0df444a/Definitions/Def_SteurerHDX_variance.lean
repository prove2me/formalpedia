-- Prove2me | Definitions.Def_SteurerHDX_variance
-- name    : SteurerHDX_variance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:51.222387+00:00
-- url     : https://prove2.me/theorems/5f6eabe1-7833-4c83-8273-b6072468a3ba
-- title:
--   The variance $\mathrm{Var}_\mu(f)$
-- statement:
--   For $f:\iota\to\mathbb R$,
--   $$\mathrm{Var}_\mu(f)=\frac12\,\mathbb E_{x,y\sim\mu}\bigl(f(x)-f(y)\bigr)^2 .$$
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.1, p.3

import Mathlib
import Definitions.Def_SteurerHDX_statDist

namespace SteurerHDX

/-- **The variance Var_μ(f).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.1, p.3:
"Var_μ(f) = ½ E_{x,y∼μ} (f(x) − f(y))²". -/
noncomputable def variance {ι : Type*} [Fintype ι] (W : Matrix ι ι ℝ) (f : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, statDist W x * statDist W y * (f x - f y) ^ 2

end SteurerHDX


