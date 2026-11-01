-- Prove2me | Definitions.Def_WildeQIT_Recover_negLog2
-- name    : WildeQIT_Recover_negLog2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:20:19.634041+00:00
-- url     : https://prove2.me/theorems/258c5eb6-596f-4f27-8329-4649789a9997
-- title:
--   $-\log_2 x$ with value $+\infty$ at $0$
-- statement:
--   For a real number $x$ define
--
--   $$
--   \operatorname{negLog}_2(x)=\begin{cases}-\log_2 x & x>0,\\ +\infty & x\le 0,\end{cases}
--   $$
--
--   as an element of $[0,+\infty]$. Applied to a fidelity $F\in[0,1]$ it is the book's $-\log F$, which is nonnegative ((12.3)) and equal to $+\infty$ when $F=0$.
--
--   It is the integrand of the recoverability bound (12.103) and the right side of (12.1).
--
--   **Formalization Note** The value lies in $[0,+\infty]$. For $x>1$ the truncation to $0$ would occur, but the definition is only applied to fidelities, which lie in $[0,1]$. The value $+\infty$ at $0$ replaces Lean's junk value $\log 0=0$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, (12.1) and (12.3), p. 366; (12.103), p. 378

import Mathlib

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (12.1) and (12.3), p. 366,
and (12.103), p. 378: the quantity `−log F` with `F` a fidelity in `[0, 1]`.
-/

open scoped ENNReal

namespace WildeQIT.Recover

/-- **Minus binary logarithm with value `+∞` at `0`** (Wilde, arXiv:1106.1445v8, (12.3), p. 366):
`negLog2 x = −log₂ x` for `x > 0` and `+∞` for `x ≤ 0`, as an element of `[0, +∞]`.

**Formalization Note** It is applied only to fidelities `F ∈ [0, 1]`; there `−log₂ F ≥ 0`
((12.3)), so the truncation `ENNReal.ofReal` of a negative number never occurs, and `F = 0` gives
`+∞` instead of Lean's junk value `Real.log 0 = 0`. -/
noncomputable def negLog2 (x : ℝ) : ℝ≥0∞ :=
  if x ≤ 0 then ⊤ else ENNReal.ofReal (-Real.logb 2 x)

end WildeQIT.Recover


