-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_SLResolvent
-- name    : TeschlODE_SturmLiouville_SLResolvent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:23:52.694863+00:00
-- url     : https://prove2.me/theorems/f04c8c60-abbb-4988-a4c0-2312a892c109
-- title:
--   Resolvent R_L(z) via the Green function (5.64)–(5.65)
-- statement:
--   Fix $z \in \mathbb{C}$ and let $u_a = u_a(z,\cdot)$, $u_b = u_b(z,\cdot)$ be solutions of $L u = z u$ satisfying the boundary condition at $a$, respectively at $b$ (normalised by (5.62)), with $W(z) = W(u_b, u_a) \ne 0$ (5.61). The **Green function** of $L$ is
--   $$G(z, x, t) = \frac{1}{W(z)} \begin{cases} u_b(z, x)\, u_a(z, t), & x \ge t,\\ u_b(z, t)\, u_a(z, x), & x \le t, \end{cases} \qquad (5.65)$$
--   and the **resolvent** is the integral operator
--   $$R_L(z) g(x) = \int_a^b G(z, x, t)\, g(t)\, r(t)\, dt, \qquad g \in H_0. \qquad (5.64)$$
--
--   **Formalization Note.** The definition takes the two functions $u_a$, $u_b$ (at the fixed $z$) as arguments; $W(z)$ is evaluated as $W_a(u_b, u_a)$, i.e. at $x = a$, which equals $W_x$ for every $x$ when $u_a, u_b$ are solutions. If $W(z) = 0$ Lean's $0^{-1} = 0$ makes the operator zero; every statement therefore assumes $W(z) \ne 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 158, §5.4, Eq. (5.64)–(5.65)

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_SLWronskian

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 158, (5.64)–(5.65): the resolvent `R_L(z) g(x) = ∫_a^b G(z, x, t) g(t) r(t) dt`
with Green function `G(z, x, t) = W(z)⁻¹ · u_b(z, x) u_a(z, t)` for `t ≤ x` and
`W(z)⁻¹ · u_b(z, t) u_a(z, x)` for `x ≤ t`, where `ua = u_a(z, ·)`, `ub = u_b(z, ·)` are the
solutions (5.62) at a fixed `z` and `W(z) = W(u_b(z), u_a(z))` (5.61), evaluated at `x = a`
(it is independent of `x`). Meaningful only when `W(z) ≠ 0`. -/
noncomputable def SLResolvent (p r : ℝ → ℝ) (a b : ℝ) (ua ub : ℝ → ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in a..b, (SLWronskian p a b ub ua a)⁻¹ *
    (if t ≤ x then ub x * ua t else ub t * ua x) * g t * (r t : ℂ)

end TeschlODE.SturmLiouville


