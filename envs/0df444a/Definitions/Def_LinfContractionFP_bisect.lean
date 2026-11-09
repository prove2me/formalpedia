-- Prove2me | Definitions.Def_LinfContractionFP_bisect
-- name    : LinfContractionFP_bisect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:21.659146+00:00
-- url     : https://prove2.me/theorems/b5e7982c-7b61-4f73-8f75-7721a54fbc5a
-- title:
--   Solve in dimension one: bisection on $f(x)-x$
-- statement:
--   For $d=1$: keep an interval $[a,b]$, starting at $[0,1]$. While $b-a>2\varepsilon$, evaluate $f$ at the midpoint $m$; set $a\gets m$ if $f(m)-m\ge0$ and $b\gets m$ otherwise. Return the midpoint of the final interval, together with the number of evaluations of $f$.
--
--   **Formalization Note** Ties ($f(m)=m$) move $a$. The loop runs its exact number of iterations, the least $j$ with $2^{-j}\le2\varepsilon$.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 4, p.6

import Mathlib
import Definitions.Def_LinfContractionFP_firstIndex

open scoped Classical

namespace LinfContractionFP

/-- The exact number of halvings of the bisection of Section 4 (`d = 1`): the interval has
length `(1/2)^j` after `j` halvings, and bisection stops once the length is at most `2ε`. -/
noncomputable def bisectIterations (ε : ℝ) : ℕ := firstIndex fun j => (1 / 2 : ℝ) ^ j ≤ 2 * ε

/-- Solve in dimension one: bisection on `f(x) − x` over `[0, 1]`, returning the midpoint of the
final interval and the number of evaluations of `f`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 4, p.6: "In
dimension one, Solve(f, ε) uses bisection on f(x) − x. Indeed, f(0) ≥ 0, f(1) ≤ 1, and
f(x) − x is strictly decreasing by contractivity. Thus, bisection maintains an interval
containing x*, and returning its midpoint once the interval has length at most 2ε yields an
ε-near fixed point using O(1 + log(1/ε)) evaluations of f."

**Formalization Note.** Dimension one is `Fin 1`. The interval `[a, b]` starts at `[0, 1]`;
while `b − a > 2ε` the midpoint `m` is evaluated once and `a ← m` if `f(m) − m ≥ 0`, else
`b ← m` (a reading of "bisection on f(x) − x"; ties go to `a`). The loop runs
`bisectIterations ε` times, its exact iteration count (the condition is also re-tested). The
second component counts evaluations of `f`. -/
noncomputable def bisect (f : (Fin 1 → ℝ) → (Fin 1 → ℝ)) (ε : ℝ) : (Fin 1 → ℝ) × ℕ := Id.run do
  let mut a : ℝ := 0
  let mut b : ℝ := 1
  let mut evals : ℕ := 0
  for _ in List.range (bisectIterations ε) do
    if 2 * ε < b - a then
      let m := (a + b) / 2
      let v := f (fun _ => m) 0
      evals := evals + 1
      if 0 ≤ v - m then a := m else b := m
  return (fun _ => (a + b) / 2, evals)

end LinfContractionFP


