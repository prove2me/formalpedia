-- Prove2me | Definitions.Def_RecursiveStopping_Infinite_Lam
-- name    : RecursiveStopping_Infinite_Lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:16.091004+00:00
-- url     : https://prove2.me/theorems/9ba7be45-e42a-478c-88eb-ce74553c619d
-- title:
--   The operator $\Lambda$ (infinite horizon)
-- statement:
--   Let $X$ be a flow on $\mathbb R^d$ under $\mathsf P$, $\mu$ the law of the delay $\vartheta$ on $[0,\infty)$ (distribution function $F$), $r$ a discount rate, $p$ a success probability and $\psi$ the delayed payoff. For $f:\mathbb R^d\to\mathbb R_+$,
--
--   $$
--   (\Lambda f)(x):=\int_0^\infty e^{-rt}\,\mathsf E_x\big[p\,\psi(X_t)+(1-p)f(X_t)\big]\,F(\mathrm dt),\qquad \mathsf E_x[g(X_t)]=\mathsf E[g(X^x_t)] .
--   $$
--
--   $(\Lambda f)(x)$ is the discounted expected reward of committing to the delayed option at $x$: after the random delay the payoff $\psi$ is collected with probability $p$, and otherwise the problem restarts with value $f$.
--
--   **Formalization Note** Both integrals are Lebesgue integrals of non-negative functions (`lintegral`), so $\Lambda f$ takes values in $[0,\infty]$ and is never assigned a default value.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (4), p.7

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- The operator `Λ` of Colaneri & De Angelis, arXiv:1905.02650v4, (4), p.7:
$$(\Lambda f)(x) := \int_0^\infty e^{-rt}\,E_x\big[p\psi(X_t)+(1-p)f(X_t)\big]\,F(dt),$$
where `F` is the law of the delay `ϑ` (here the probability measure `μ` on `[0, ∞)`) and
`E_x[g(X_t)] = E[g(X^x_t)]` for the flow `X` under `P`.

**Formalization Note** Both integrals are `lintegral`s of non-negative integrands (for
non-negative `ψ, f`), so `Λf` is `[0, ∞]`-valued and never a junk value. -/
noncomputable def Lam {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure ℝ≥0)
    (r p : ℝ) (ψ f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.exp (-r * (t : ℝ))) *
    ∫⁻ ω, ENNReal.ofReal (p * ψ (X x t ω) + (1 - p) * f (X x t ω)) ∂P ∂μ

end RecursiveStopping.Infinite


