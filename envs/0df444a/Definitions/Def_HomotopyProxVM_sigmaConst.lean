-- Prove2me | Definitions.Def_HomotopyProxVM_sigmaConst
-- name    : HomotopyProxVM_sigmaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:38.882687+00:00
-- url     : https://prove2.me/theorems/77aa93f4-e0bd-4db2-a9eb-ea05d0deb837
-- title:
--   The rate $\sigma$ of (18)
-- statement:
--   With $\Gamma$ as in (18), the **rate** of Theorem 4 is
--
--   $$
--   \sigma:=\frac{1-\tau_0+\tau_0\omega\Gamma}{1-\tau_0+\tau_0\Gamma}.
--   $$
--
--   It is chosen so that (65) holds, which balances the speed of the homotopy against the contraction $\omega$.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Theorem 4, (18), p.8

import Mathlib
import Definitions.Def_HomotopyProxVM_gammaConst

namespace HomotopyProxVM

/-- The rate `σ := (1 − τ₀ + τ₀ ω Γ) / (1 − τ₀ + τ₀ Γ)` of (18), with `Γ` as in `gammaConst`
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Theorem 4, (18), p.8). Here `a = ‖∇f(x⁰) + ξ⁰‖₂` and `b = L_g + ‖ξ⁰‖₂`. -/
noncomputable def sigmaConst (τ₀ ω a b : ℝ) : ℝ :=
  (1 - τ₀ + τ₀ * ω * gammaConst a ω b) / (1 - τ₀ + τ₀ * gammaConst a ω b)

end HomotopyProxVM


