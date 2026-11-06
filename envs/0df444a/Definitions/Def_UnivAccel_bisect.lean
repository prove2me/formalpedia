-- Prove2me | Definitions.Def_UnivAccel_bisect
-- name    : UnivAccel_bisect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:07.835251+00:00
-- url     : https://prove2.me/theorems/391a3a79-370e-47a3-ada3-e4c312dcdb16
-- title:
--   Bisection on a bracket $[a, b]$
-- statement:
--   Given $\phi : \mathbb R \to \mathbb R$ and a bracket $[a, b]$, **bisection** evaluates $\phi$ at the midpoint $m$ of the current bracket and keeps $[m, b']$ if $\phi(m) < 0$, $[a', m]$ if $\phi(m) > 0$, and the degenerate bracket $[m, m]$ if $\phi(m) = 0$. `bisect φ a b k` is the bracket after $k$ trials.
--
--   In §4.2 the implicit-Euler method uses bisection on the function $\phi(h) = h^2\|\nabla f(x_+(h))\|/(1 + 2h\sqrt\mu) - r$ to find a step duration; every trial costs one ball-oracle call.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2 "Computing h", p.14

import Mathlib

namespace UnivAccel

open Classical in
/-- Bisection on a bracket `[a, b]` for a root of `ϕ` (Adil–Kyng, *Universal Acceleration: New
Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256
c7b64bc2…980250), §4.2 "Computing h", p.14: "bisection on [a, b] then finds a root of ϕ"):
`bisect ϕ a b k` is the bracket after `k` trials. Each trial evaluates `ϕ` at the midpoint `m` and
keeps the half on which `ϕ` changes sign (`[m, b']` if `ϕ(m) < 0`, `[a', m]` if `ϕ(m) > 0`); if
`ϕ(m) = 0` the bracket collapses to `[m, m]`.

**Formalization Note** One trial is one evaluation of `ϕ`, i.e. one ball-oracle call in §4.2. -/
noncomputable def bisect (φ : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | k + 1 =>
    let p := bisect φ a b k
    let m := (p.1 + p.2) / 2
    if φ m < 0 then (m, p.2) else if 0 < φ m then (p.1, m) else (m, m)

end UnivAccel


