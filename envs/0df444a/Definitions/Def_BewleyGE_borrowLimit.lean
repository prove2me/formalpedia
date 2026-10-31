-- Prove2me | Definitions.Def_BewleyGE_borrowLimit
-- name    : BewleyGE_borrowLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:21.843182+00:00
-- url     : https://prove2.me/theorems/4a39066e-eda3-46cd-aa8f-3cc8c4d78a06
-- title:
--   Natural borrowing limit $\underline b=-\min_y p\cdot y/r$
-- statement:
--   At prices $p$ and interest rate $r>0$, the **natural borrowing limit** is
--   $$
--   \underline b(p,r)=-\frac{\min_{y\in\mathcal Y}p\cdot y}{r},
--   $$
--   the most an agent can owe and still repay from the lowest income forever.
--
--   **Formalization Note** Used only for $0<r<1$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2, p.5

import Mathlib
import Definitions.Def_BewleyGE_minIncome

namespace BewleyGE

/-- **Natural borrowing limit** `b̲ = −min_{y ∈ 𝒴} p · y / r`. Light, arXiv:1906.06810v2, §2, p.5.

**Formalization Note.** Used only for `0 < r < 1` (Lean's `x / 0 = 0` never enters). -/
noncomputable def borrowLimit {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ) : ℝ :=
  -minIncome E p / r

end BewleyGE


