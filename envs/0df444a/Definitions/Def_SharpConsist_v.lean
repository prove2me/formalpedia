-- Prove2me | Definitions.Def_SharpConsist_v
-- name    : SharpConsist_v
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:36.735551+00:00
-- url     : https://prove2.me/theorems/2e945685-0f67-4aeb-bfae-5f37f58dc086
-- title:
--   The scalar profiles $v$, $w$ and constants $c$, $d$ of Eq. (5.2)
-- statement:
--   Fix a parameter $T$ (in the paper $T\in[7/5,3/2]$). Eq. (5.2) defines
--   $$d=\Bigl(\tfrac{T^2}{2}+T+1\Bigr)^{-1},\qquad c=\frac{dT^2}{2},$$
--   the **current profile**
--   $$v(t)=\begin{cases}d\bigl((T+1)t-t^2/2\bigr),&t\le T,\\ 1-de^{-(t-T)},&t\ge T,\end{cases}$$
--   its derivative $v'(t)=d(T+1-t)$ for $t\le T$ and $v'(t)=de^{-(t-T)}$ for $t>T$, and the **future profile**
--   $$w(t)=\begin{cases}c+dt,&t\le T,\\ v(t),&t\ge T.\end{cases}$$
--   The two pieces of $v$ meet at $t=T$ with value $1-d$ and slope $d$.
--
--   **Formalization Note.** The paper defines $v,w$ on $[0,\infty)$; here they are defined on all of $\mathbb R$ by the quadratic and linear pieces for $t\le T$. The derivative $v'$ is written by its formula (not as `deriv v`); a sanity check proves that it is the derivative of $v$ at every real $t$, including $t=T$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.1, Eq. (5.2), p.13

import Mathlib

namespace SharpConsist

/-- The constant `d = (T²/2 + T + 1)⁻¹` of Eq. (5.2). Fu–Zhang–Tao, arXiv:2609.09986 (held
version, sha256 874ec76c…), §5.1, Eq. (5.2), p.13. -/
noncomputable def dT (T : ℝ) : ℝ := (T ^ 2 / 2 + T + 1)⁻¹

/-- The constant `c = d T²/2` of Eq. (5.2), p.13. -/
noncomputable def cT (T : ℝ) : ℝ := dT T * T ^ 2 / 2

/-- The **current profile** `v` of Eq. (5.2), p.13:
`v(t) = d((T + 1)t − t²/2)` for `t ≤ T` and `v(t) = 1 − d e^{−(t−T)}` for `t ≥ T`.

**Formalization Note.** The paper defines `v` on `[0, ∞)`; here it is defined on all of `ℝ`, by the
quadratic piece for `t ≤ T`. Every argument at which the paper evaluates `v` is nonnegative. -/
noncomputable def v (T t : ℝ) : ℝ :=
  if t ≤ T then dT T * ((T + 1) * t - t ^ 2 / 2) else 1 - dT T * Real.exp (-(t - T))

/-- The derivative `v′` of the current profile, written by its formula:
`v′(t) = d(T + 1 − t)` for `t ≤ T` and `v′(t) = d e^{−(t−T)}` for `t > T` (§5.1, p.13; the piecewise
formulas are those of Appendix B.2, p.35).

**Formalization Note.** `v′` is an explicit formula, not `deriv v`; the two pieces agree at `t = T`
(both equal `d`), and `v′ t` is the derivative of `v` at every real `t`. -/
noncomputable def v' (T t : ℝ) : ℝ :=
  if t ≤ T then dT T * (T + 1 - t) else dT T * Real.exp (-(t - T))

/-- The **future profile** `w` of Eq. (5.2), p.13: `w(t) = c + d t` for `t ≤ T` and `w(t) = v(t)` for
`t ≥ T`.

**Formalization Note.** Defined on all of `ℝ` by the linear piece for `t ≤ T`, like `v`. -/
noncomputable def w (T t : ℝ) : ℝ :=
  if t ≤ T then cT T + dT T * t else v T t

end SharpConsist


