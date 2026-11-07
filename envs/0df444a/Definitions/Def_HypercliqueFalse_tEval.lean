-- Prove2me | Definitions.Def_HypercliqueFalse_tEval
-- name    : HypercliqueFalse_tEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:32:19.732526+00:00
-- url     : https://prove2.me/theorems/91626a6d-20ed-4876-beb1-d51d866180ab
-- title:
--   Evaluating $T_h$ of size $(N,N,a,b,c)$ with $a,b,c\le N\le n$ (word RAM problem)
-- statement:
--   The problem of **evaluating $T_h$ of size $(N, N, a, b, c)$ with $a, b, c \le N \le n$** on the published word RAM. An instance at scale $s$ consists of dimensions $n, N, a, b, c$ with $N \le n \le s$ and $a, b, c \le N$, and arrays $A, B, C, D, E$ of $T_h$ of size $(N, N, a, b, c)$ whose variables $x_5,\dots,x_{h+1}$ range over $[n]$. The input is the encoding `tInput`; the machine must write $T_h(A,B,C,D,E)$ into the first cell after the input.
--
--   These are the leaves of the recursion, evaluated by Lemma 4.3 in time $O(N^4 n^{h-3}(abc)^{1-\delta})$.
--
--   **Formalization Note** The scale $s$ fixes the word size and the integer bound of `SolvedWithin`; $n$ is the instance's own range of $x_5, \dots$, as in the paper.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.3, p.11

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_HypercliqueFalse_tPoly
import Definitions.Def_HypercliqueFalse_tInput

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Evaluating `T_h` of size `(N, N, a, b, c)` with `a, b, c ≤ N ≤ n`**, as a problem of the
published word RAM. Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version,
sha256 6bd5cf5d…7730), Lemma 4.3, p.11: "T_h of size (N, N, a, b, c) with a, b, c ≤ N ≤ n can be
evaluated".

An instance at scale `s` is `⟨n, N, a, b, c, _, T⟩` with `N ≤ n ≤ s` and `a, b, c ≤ N`, and arrays
`T` of `T_h` of size `(N, N, a, b, c)` whose variables `x₅, …, x_{h+1}` range over `[n]`. The input
is `tInput T`; the program must write `tPoly T` into the first cell after the input.

**Formalization Note.** The scale `s` fixes the word size and the integer bound of `SolvedWithin`;
`n` is the instance's own range of `x₅, …`, as in the paper. -/
def tEval (h : ℕ) : Problem where
  Instance s := Σ' (n N a b c : ℕ) (_ : N ≤ n ∧ n ≤ s ∧ a ≤ N ∧ b ≤ N ∧ c ≤ N),
    TData h N N a b c n
  input x := tInput x.2.2.2.2.2.2
  output x f := f 0 = tPoly x.2.2.2.2.2.2

end HypercliqueFalse


