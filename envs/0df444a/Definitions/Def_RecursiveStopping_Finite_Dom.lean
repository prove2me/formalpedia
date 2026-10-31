-- Prove2me | Definitions.Def_RecursiveStopping_Finite_Dom
-- name    : RecursiveStopping_Finite_Dom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:19.613353+00:00
-- url     : https://prove2.me/theorems/eb18a1fd-377b-47e6-b94c-078d63e1cc10
-- title:
--   The finite-horizon state space $[0,T]\times\mathbb R^{d-1}$
-- statement:
--   For a horizon $T$ and $m=d-1$, the state space of the finite-horizon problem is
--
--   $$
--   [0,T]\times\mathbb R^{m}\subset\mathbb R\times\mathbb R^m,
--   $$
--
--   whose points are $z=(t,x)$ with $t$ the time coordinate and $x$ the spatial coordinate.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2.2, p.9

import Mathlib

namespace RecursiveStopping.Finite

/-- The finite-horizon state space `[0, T] × ℝ^{d−1}` of Colaneri & De Angelis,
arXiv:1905.02650v4, §2.2, p.9, with `m = d − 1`, as a subset of `ℝ × ℝ^m`. A point is
`z = (t, x)`, `t` the time coordinate. -/
def Dom (m : ℕ) (T : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
  Set.Icc 0 T ×ˢ Set.univ

end RecursiveStopping.Finite


