-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_SLWronskian
-- name    : TeschlODE_SturmLiouville_SLWronskian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:23:14.228739+00:00
-- url     : https://prove2.me/theorems/72ab4476-f04a-448b-a0d5-d3d2ce9d7120
-- title:
--   Modified Wronskian W_x(u, v) (5.47)
-- statement:
--   For functions $u, v$ on $[a,b]$ the **modified Wronskian** at $x \in [a,b]$ is
--   $$W_x(u, v) = u(x)\, p(x) v'(x) - p(x) u'(x)\, v(x). \qquad (5.47)$$
--   By Liouville's formula it is independent of $x$ when $u$ and $v$ solve (5.43) with the same $z$; it is then written $W(u, v)$.
--
--   **Formalization Note.** Derivatives are `derivWithin … (Set.Icc a b)`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 154, §5.3, Eq. (5.47)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.3, p. 154, (5.47): the modified Wronskian
`W_x(u, v) = u(x) p(x) v′(x) − p(x) u′(x) v(x)`, derivatives taken within `[a, b]`. -/
noncomputable def SLWronskian (p : ℝ → ℝ) (a b : ℝ) (u v : ℝ → ℂ) (x : ℝ) : ℂ :=
  u x * (p x : ℂ) * derivWithin v (Set.Icc a b) x -
    (p x : ℂ) * derivWithin u (Set.Icc a b) x * v x

end TeschlODE.SturmLiouville


