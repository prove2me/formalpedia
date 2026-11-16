-- Prove2me | Definitions.Def_NKtLB_Supplement_twoPolylog
-- name    : NKtLB_Supplement_twoPolylog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:26:18.614999+00:00
-- url     : https://prove2.me/theorems/c50022be-531b-40bf-8e1e-7567f8b8d80e
-- title:
--   The time bound $2^{\log^d n}$
-- statement:
--   For a real $d$, $\mathrm{twoPolylog}_d(n)=\lceil 2^{(\log_2 n)^d}\rceil$, the time bound of the conclusion $\mathrm{UNSAT}\notin\mathsf{AMTIME}[2^{\log^d n}]$ of Theorems 59 and 65.
--
--   **Formalization Note** Real logarithm and real powers. At $n=0$ the bound is $1$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 59, p.39; Theorem 65, p.43

import Mathlib

namespace NKtLB.Supplement

/-- **The time bound `2^{log^d n}`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 59, p.39 and Theorem 65, p.43: "`UNSAT ∉
AMTIME[2^{log^d n}]` for any `d ≥ 1`"), rounded up: `n ↦ ⌈2^{(log₂ n)^d}⌉` for a real `d`.

**Formalization Note.** Real `log₂` and real powers; at `n = 0` the bound is `1`. -/
noncomputable def twoPolylog (d : ℝ) (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ (Real.logb 2 n ^ d)⌉₊

end NKtLB.Supplement


