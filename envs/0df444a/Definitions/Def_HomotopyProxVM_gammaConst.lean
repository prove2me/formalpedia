-- Prove2me | Definitions.Def_HomotopyProxVM_gammaConst
-- name    : HomotopyProxVM_gammaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:53.122609+00:00
-- url     : https://prove2.me/theorems/a3ff2dbb-5f44-4935-a528-4e08e5fe58b7
-- title:
--   The constant $\Gamma$ of (18)
-- statement:
--   With $a=\|\nabla f(x^0)+\xi^0\|_2$ and $b=L_g+\|\xi^0\|_2$, the constant of (18) is
--
--   $$
--   \Gamma:=\frac{a}{\omega\, b}.
--   $$
--
--   **Formalization Note** The arguments $a$, $\omega$, $b$ are real numbers, so that the algebra of (18) and (65) can be stated separately. Statements that use $\Gamma$ assume $0<\omega$ and $0<b$, the conditions under which (18) is defined.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Theorem 4, (18), p.8

import Mathlib

namespace HomotopyProxVM

/-- The constant `Γ := ‖∇f(x⁰) + ξ⁰‖₂ / (ω (L_g + ‖ξ⁰‖₂))` of (18)
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Theorem 4, (18), p.8), with `a = ‖∇f(x⁰) + ξ⁰‖₂` and `b = L_g + ‖ξ⁰‖₂`.

**Formalization Note.** The denominator is nonzero exactly when `ω ≠ 0` and `b ≠ 0`; statements of
the mission that use `Γ` assume `0 < ω` and `0 < b`, the conditions under which (18) is defined. -/
noncomputable def gammaConst (a ω b : ℝ) : ℝ :=
  a / (ω * b)

end HomotopyProxVM


