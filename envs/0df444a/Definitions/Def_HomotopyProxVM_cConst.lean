-- Prove2me | Definitions.Def_HomotopyProxVM_cConst
-- name    : HomotopyProxVM_cConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:55.470982+00:00
-- url     : https://prove2.me/theorems/cf56f619-3d14-45f9-84e3-2b3e4a53fb28
-- title:
--   The constant $C$ of (18)
-- statement:
--   With $a=\|\nabla f(x^0)+\xi^0\|_2$, the constant of (18) is
--
--   $$
--   C:=\frac{a}{\mu_f}.
--   $$
--
--   It bounds the initial distance $\|x^0-x^*_{\tau_0}\|_2$.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Theorem 4, (18), p.8; (63), p.26

import Mathlib

namespace HomotopyProxVM

/-- The constant `C := ‖∇f(x⁰) + ξ⁰‖₂ / μ_f` of (18) (Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Theorem 4, (18), p.8), with
`a = ‖∇f(x⁰) + ξ⁰‖₂`. `μ_f > 0` by the definition of strong convexity. -/
noncomputable def cConst (a μ : ℝ) : ℝ :=
  a / μ

end HomotopyProxVM


