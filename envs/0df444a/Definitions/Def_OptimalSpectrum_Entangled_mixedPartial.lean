-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_mixedPartial
-- name    : OptimalSpectrum_Entangled_mixedPartial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:13.085223+00:00
-- url     : https://prove2.me/theorems/35f4836a-6f09-4c6e-ac2d-94723a7f27bd
-- title:
--   Mixed partial derivative $\partial^r/\partial t_1\cdots\partial t_r$ at $t=0$
-- statement:
--   For $F:\mathbb R^r\to\mathbb R$,
--
--   $$\frac{\partial^r F}{\partial t_1\cdots\partial t_r}\Big|_{t_1=\cdots=t_r=0},$$
--
--   the $r$-th derivative of $F$ at the origin applied to the coordinate directions $e_1,\dots,e_r$. For a polynomial $F$ this is the coefficient of $t_1\cdots t_r$.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.2, p. 21 (PDF p. 23)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Mixed partial derivative `∂^r/∂t₁⋯∂t_r` at `t = 0`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.2, printed p. 21 (PDF p. 23) and Lemma 7.6, printed p. 24 (PDF p. 26): the operator
`∂^r/∂t₁ ⋯ ∂t_r (·)|_(t₁=⋯=t_r=0)`.

For `F : ℝ^r → ℝ`, `mixedPartial r F` is the `r`-th Fréchet derivative of `F` at `0` evaluated on the
standard basis vectors `e₁, …, e_r`, i.e. `∂^r F/∂t₁⋯∂t_r (0)`.

**Formalization Note.** Every function the paper differentiates this way is a polynomial in
`t₁, …, t_r`, hence smooth, and then this value is the coefficient of `t₁⋯t_r`, as the page says. -/
noncomputable def mixedPartial (r : ℕ) (F : (Fin r → ℝ) → ℝ) : ℝ :=
  iteratedFDeriv ℝ r F 0 fun j => Pi.single j 1

end OptimalSpectrum.Entangled


