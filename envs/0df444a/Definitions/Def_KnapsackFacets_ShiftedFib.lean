-- Prove2me | Definitions.Def_KnapsackFacets_ShiftedFib
-- name    : KnapsackFacets_ShiftedFib
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:45.624299+00:00
-- url     : https://prove2.me/theorems/fe28c006-8c2a-4c5f-a920-9ead29e0beb1
-- title:
--   The shifted Fibonacci sequence $f$ of (1)–(2)
-- statement:
--   The “shifted” Fibonacci sequence $(f_i)_{i\ge1}$ is
--   $$
--   f_1=f_2=f_3=1,\qquad f_i=f_{i-2}+f_{i-1}\quad(i\ge4).
--   $$
--   Its first values are $1,1,1,2,3,5,8,13,\dots$ For a finite $S\subseteq\mathbb N$, $f(S)=\sum_{i\in S}f_i$.
--
--   The first $2r+1$ coefficients of the reduction instance of Theorem 4 are built from this sequence.
--
--   **Formalization Note** The sequence is 1-indexed as in the paper; the value at index $0$ is a placeholder ($0$) that no statement uses. It is not Mathlib's `Nat.fib`, which has $\mathrm{fib}(3)=2$.
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, §3, p.5, (1)–(2)

import Mathlib

set_option autoImplicit false

namespace KnapsackFacets

/-- **The “shifted” Fibonacci sequence** `(fᵢ)_{i ≥ 1}`. Chen & Zhu, arXiv:2211.03311v3, §3,
p.5, (1)–(2): "f₁ = f₂ = f₃ = 1, fᵢ = fᵢ₋₂ + fᵢ₋₁, i ≥ 4."

**Formalization Note.** The sequence is 1-indexed as in the paper: `shiftedFib i` is `fᵢ`
for `i ≥ 1`. The value at `0` is a junk value (`0`) that no statement uses. This is not
Mathlib's `Nat.fib` (which has `fib 1 = fib 2 = 1`, `fib 3 = 2`). -/
def shiftedFib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | i + 4 => shiftedFib (i + 2) + shiftedFib (i + 3)

end KnapsackFacets


