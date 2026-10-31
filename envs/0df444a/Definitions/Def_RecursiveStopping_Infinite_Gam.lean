-- Prove2me | Definitions.Def_RecursiveStopping_Infinite_Gam
-- name    : RecursiveStopping_Infinite_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:08.972984+00:00
-- url     : https://prove2.me/theorems/6ebb1930-e7f4-4caa-8c6a-c57aef03aeb7
-- title:
--   The operator $\Gamma$ (infinite horizon)
-- statement:
--   With $\Lambda$ as in (4), the obstacle $\varphi$, and $\mathcal T$ the set of **all** $\mathbb F$-stopping times with values in $[0,\infty]$,
--
--   $$
--   (\Gamma f)(x):=\sup_{\tau\in\mathcal T}\mathsf E_x\Big[e^{-r\tau}\max\{\varphi(X_\tau),(\Lambda f)(X_\tau)\}\Big],
--   $$
--
--   with payoff $0$ on $\{\tau=\infty\}$. $(\Gamma f)(x)$ is the value of stopping optimally and then taking the better of the immediate payoff $\varphi$ and the delayed option $\Lambda f$. Problem 2, display (3), asks for $v=\Gamma v$.
--
--   **Formalization Note** The gain $\max\{\varphi,\Lambda f\}$ is computed in $[0,\infty]$ and the expectation is a `lintegral`, so $\Gamma f$ is $[0,\infty]$-valued.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (15), p.10; Problem 2, (3), p.7

import Mathlib
import Definitions.Def_RecursiveStopping_discPayoff
import Definitions.Def_RecursiveStopping_Infinite_Lam

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Infinite

/-- The operator `Γ` of Colaneri & De Angelis, arXiv:1905.02650v4, (15), p.10:
$$(\Gamma f)(x) := \sup_{\tau\in\mathcal T} E_x\Big[e^{-r\tau}\max\{\varphi(X_\tau),(\Lambda f)(X_\tau)\}\Big],$$
the supremum over **all** `𝔽`-stopping times `τ` with values in `[0, ∞]`, with the payoff `0`
on `{τ = ∞}` (`discPayoff`, the convention of p.6). Problem 2, (3), p.7, asks for `v` with
`v = Γv`.

**Formalization Note** The gain `max{ϕ, Λf}` is computed in `[0, ∞]` and the expectation is a
`lintegral`, so `Γf` is `[0, ∞]`-valued. -/
noncomputable def Gam {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ)
    (X : EuclideanSpace ℝ (Fin d) → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure ℝ≥0)
    (r p : ℝ) (ϕ ψ f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ (τ : Ω → ℝ≥0∞) (_ : IsStoppingTime 𝔽 τ),
    ∫⁻ ω, discPayoff r (fun y => max (ENNReal.ofReal (ϕ y)) (Lam P X μ r p ψ f y)) X x τ ω ∂P

end RecursiveStopping.Infinite


