-- Prove2me | Definitions.Def_BewleyGE_savingsSet
-- name    : BewleyGE_savingsSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:28.713434+00:00
-- url     : https://prove2.me/theorems/e15a3c62-bd2d-4ebf-a95a-27c9b27e990b
-- title:
--   Feasible savings $C(a,p)$
-- statement:
--   An agent with wealth $a$ facing prices $(p,r)$ may choose next period's savings $b$ in
--   $$
--   C(a,p)=\Big[\underline b(p,r),\ \min\Big\{a,\ \sum_{i=1}^n\frac{p_i\bar b}{(1-r)^2}\Big\}\Big].
--   $$
--   The constraint $b\le a$ keeps consumption expenditure $a-b$ nonnegative.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2, p.5 (restated §3.1, p.11)

import Mathlib
import Definitions.Def_BewleyGE_borrowLimit
import Definitions.Def_BewleyGE_savingsCap

namespace BewleyGE

/-- **Feasible savings** `C(a, p) = [b̲, min{a, ∑ᵢ pᵢ b̄/(1 − r)²}]`.
Light, arXiv:1906.06810v2, §2, p.5, restated §3.1, p.11.

**Formalization Note.** The interval is empty when `a < b̲`; it is only used for wealth
`a ∈ A(p, r)`, where `a ≥ b̲`. -/
noncomputable def savingsSet {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r a : ℝ) : Set ℝ :=
  Set.Icc (borrowLimit E p r) (min a (savingsCap E p r))

end BewleyGE


