-- Prove2me | Definitions.Def_DupacovaWets_Consistency_expect
-- name    : DupacovaWets_Consistency_expect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:28:05.455981+00:00
-- url     : https://prove2.me/theorems/0afd81ca-03c5-4ffb-bf05-08133892b1d9
-- title:
--   Expectation $E_Q g=\int g\,dQ$ with the $+\infty$ convention, and the expectation functional $x\mapsto E_Q f(x,\cdot)$
-- statement:
--   Let $(\Xi,\mathcal A)$ be a measurable space, $Q$ a measure on it, and $g:\Xi\to[-\infty,\infty]$. Write $g^+=\max(g,0)$ and $g^-=\max(-g,0)$. The expectation of $g$ under $Q$ is
--
--   $$
--   E_Q g=\begin{cases}+\infty, & \text{if } \int g^+\,dQ=\infty,\\[2pt] \int g^+\,dQ-\int g^-\,dQ, & \text{otherwise,}\end{cases}
--   $$
--
--   so it equals $-\infty$ when $\int g^+\,dQ<\infty$ and $\int g^-\,dQ=\infty$. This is the integral (3.2)/(3.6) of Dupačová and Wets together with their convention that $Ef(x)=\infty$ whenever $\xi\mapsto f(x,\xi)$ is not bounded above by a summable function.
--
--   For an integrand $f:\mathbb R^n\times\Xi\to[-\infty,\infty]$ the **expectation functional** is $x\mapsto E_Q f(x,\cdot)$. With $Q=P$ it is the paper's $Ef$; with $Q=P^\nu(\cdot,\zeta)$ it is the estimated objective $E^\nu f(\cdot,\zeta)$.
--
--   **Formalization Note** The integrals of $g^\pm$ are Lebesgue integrals of $[0,\infty]$-valued functions (`lintegral`), so no non-integrable function is silently assigned the value $0$. The case split keeps the extended-real expression $\infty-\infty$ from arising. For a non-measurable $g$ the `lintegral` is the lower integral; every function this mission integrates is measurable under Assumption 3.4.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 10, (3.2) with the convention following it; p. 12, (3.6)

import Mathlib
open MeasureTheory
open scoped ENNReal

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 10, (3.2) and (3.6), with the convention of p. 10:
the expectation `E_Q g = ∫ g dQ` of an extended-real-valued function `g`, set equal to `+∞`
whenever `g` is not bounded above by a summable function (`∫ g⁺ dQ = ∞`), and equal to
`∫ g⁺ dQ - ∫ g⁻ dQ` otherwise (which is `-∞` when `∫ g⁻ dQ = ∞`). -/
noncomputable def expect {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ) (g : Ξ → EReal) :
    EReal :=
  if ∫⁻ ξ, (g ξ).toENNReal ∂Q = ∞ then ⊤
  else ((∫⁻ ξ, (g ξ).toENNReal ∂Q : ℝ≥0∞) : EReal) - ((∫⁻ ξ, (-g ξ).toENNReal ∂Q : ℝ≥0∞) : EReal)

/-- The expectation functional `x ↦ E_Q f(x, ·)` on `ℝⁿ`: `Ef = expectFn P f` (3.2) and
`E^ν f(·, ζ) = expectFn (P^ν(·, ζ)) f` (3.6). -/
noncomputable def expectFn {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) : EuclideanSpace ℝ (Fin n) → EReal :=
  fun x => expect Q (f x)

end DupacovaWets.Consistency


