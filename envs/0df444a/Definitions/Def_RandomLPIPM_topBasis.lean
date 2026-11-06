-- Prove2me | Definitions.Def_RandomLPIPM_topBasis
-- name    : RandomLPIPM_topBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:44.666609+00:00
-- url     : https://prove2.me/theorems/4d3fda06-02ce-4c5c-a03e-a19b5358d8d3
-- title:
--   Indices of the $d$ largest coordinates of $\hat x$
-- statement:
--   For $x\in\mathbb R^n$ and $d\le n$, $\hat B$ is the set of indices of the $d$ largest coordinates of $x$: index $i$ belongs to $\hat B$ when fewer than $d$ indices $j$ satisfy $x_j>x_i$, or $x_j=x_i$ and $j<i$.
--
--   It is the guessed optimal basis of the rounding step of Theorem 8.11.
--
--   **Formalization Note** Ties are broken by index (the paper does not need a rule: under its hypotheses the $d$ largest coordinates are strictly separated from the others). For $d\le n$ the set has exactly $d$ elements.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, p.73

import Mathlib

open Matrix

namespace RandomLPIPM

/-- **The indices of the `d` largest coordinates of `x`.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 8.11, p.73: "letting `B̂`
be the index set of the `d` largest coordinates of `x̂`".

`i ∈ topBasis d x` iff fewer than `d` indices `j` beat `i`, where `j` beats `i` when `x_j > x_i`, or
`x_j = x_i` and `j < i`.

**Formalization Note.** Ties are broken by index (the paper does not say how; under its hypotheses
the `d` largest coordinates are strictly separated from the rest). For `d ≤ n` the set has exactly
`d` elements. -/
noncomputable def topBasis {n : ℕ} (d : ℕ) (x : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    (Finset.univ.filter fun j => x i < x j ∨ (x j = x i ∧ j < i)).card < d

end RandomLPIPM


