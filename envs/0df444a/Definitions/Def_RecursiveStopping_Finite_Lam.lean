-- Prove2me | Definitions.Def_RecursiveStopping_Finite_Lam
-- name    : RecursiveStopping_Finite_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:25.746189+00:00
-- url     : https://prove2.me/theorems/bf42c08f-d6ab-4fc4-853d-19643d7585d5
-- title:
--   The finite-horizon operator $\Lambda$, display (12)
-- statement:
--   Let $Z$ be the space-time flow, $Z^z_s=(t+s,X^z_s)$ for $z=(t,x)$, and $\mu$ the law of the delay (distribution function $F$). For $f$ on $[0,T]\times\mathbb R^{d-1}$,
--
--   $$
--   (\Lambda f)(z):=\int_{[0,T-t]}e^{-rs}\,\mathsf E\big[p\,\psi(Z^z_s)+(1-p)f(Z^z_s)\big]\,F(\mathrm ds).
--   $$
--
--   The integral stops at $T-t$ because a delayed outcome after the horizon is worthless (the indicator $\mathbf 1_{\{\tau+\vartheta\le T-t\}}$ of Problem 1'). The interval is closed, so an atom of $F$ at $0$ counts.
--
--   **Formalization Note** The page prints the discount as $e^{-rt}$, where $t$ is the fixed time coordinate of $z$; the integration variable is $s$, so the factor is $e^{-rs}$ as in (4). Both integrals are `lintegral`s.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (12), p.9

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Finite

/-- The finite-horizon operator `Λ` of Colaneri & De Angelis, arXiv:1905.02650v4, (12), p.9:
for `z = (t, x)`,
$$(\Lambda f)(z) := \int_0^{T-t} e^{-rs}\,E_z\big[p\psi(X_s)+(1-p)f(X_s)\big]\,F(ds),$$
the integral over `s ∈ [0, T − t]` (closed, so an atom of `F` at `0` counts), where `F` is the
law `μ` of the delay and `E_z[g(X_s)] = E[g(Z^z_s)]` for the space-time flow `Z`.

**Formalization Note** The page prints the discount as `e^{−rt}`; `t` is the fixed time
coordinate of `z` and the integration variable is `s`, so the factor is `e^{−rs}` (as in (4)
and in Problem 1'). Both integrals are `lintegral`s, so `Λf` is `[0, ∞]`-valued. -/
noncomputable def Lam {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ × EuclideanSpace ℝ (Fin m) → ℝ≥0 → Ω → ℝ × EuclideanSpace ℝ (Fin m))
    (μ : Measure ℝ≥0) (T r p : ℝ) (ψ f : ℝ × EuclideanSpace ℝ (Fin m) → ℝ)
    (z : ℝ × EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ s in Set.Iic (Real.toNNReal (T - z.1)), ENNReal.ofReal (Real.exp (-r * (s : ℝ))) *
    ∫⁻ ω, ENNReal.ofReal (p * ψ (Z z s ω) + (1 - p) * f (Z z s ω)) ∂P ∂μ

end RecursiveStopping.Finite


