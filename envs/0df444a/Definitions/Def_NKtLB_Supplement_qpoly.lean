-- Prove2me | Definitions.Def_NKtLB_Supplement_qpoly
-- name    : NKtLB_Supplement_qpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:26:00.871102+00:00
-- url     : https://prove2.me/theorems/b5e502f7-4533-4dcf-94eb-dc7375913b1c
-- title:
--   The time bound $n^{(\log n)^c}$
-- statement:
--   For $c\in\mathbb N$, $\mathrm{qpoly}_c(n)=\lceil n^{(\log_2 n)^c}\rceil$. A class written $\mathsf C[n^{\mathrm{poly}(\log n)}]$ or $\mathsf C[n^{\mathrm{polylog}(n)}]$ is the union over $c\in\mathbb N$ of $\mathsf C[\mathrm{qpoly}_c]$.
--
--   **Formalization Note** Real logarithm (with $\log_2 0=0$) and real power.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), pp.9–13 (classes $\mathsf C[n^{\mathrm{poly}(\log n)}]$)

import Mathlib

namespace NKtLB.Supplement

/-- **The time bound `n^{(log n)^c}`** (for the classes `NTIME[n^{poly(log n)}]`,
`AMTIME[n^{polylog(n)}]`, `SIZE^O[n^{polylog(n)}]`, … of Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), pp.9–13), rounded up:
`n ↦ ⌈n^{(log₂ n)^c}⌉`. A class `C[n^{poly(log n)}]` is the union over `c ∈ ℕ` of `C[qpoly c]`.

**Formalization Note.** Real `log₂` (`Real.logb 2 0 = 0`), real power. -/
noncomputable def qpoly (c : ℕ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (Real.logb 2 n ^ c)⌉₊

end NKtLB.Supplement


