-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_probFun
-- name    : KallMayerSLP_NormalCC_probFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:54.386346+00:00
-- url     : https://prove2.me/theorems/bae31286-7e22-42bc-b09f-2e44e550fd58
-- title:
--   Probability function $G(x)=\mathbb P(\eta^{\mathsf T}x\ge\xi)$ of a separate chance constraint
-- statement:
--   Let $\eta$ be a random vector in $\mathbb R^n$ and $\xi$ a random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$. With $\zeta(x,\eta,\xi)=\eta^{\mathsf T}x-\xi$, the **probability function** of the separate chance constraint $\eta^{\mathsf T}x\ge\xi$ is
--   $$G(x)=\mathbb P\big(\zeta(x,\eta,\xi)\ge0\big)=\mathbb P(\eta^{\mathsf T}x\ge\xi),\qquad x\in\mathbb R^n .$$
--
--   The chance constraint $G(x)\ge\alpha$ with a prescribed probability level $\alpha$ is the object of §2.3.2–§2.3.3. No distributional assumption is built in; normality of $(\eta,\xi)$ is a hypothesis of the theorems.
--
--   **Formalization Note** The probability is the measure of the event as a real number (`Measure.real`).
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, eqs. (2.29), (2.31), p.106 (PDF p.116)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.NormalCC

/-- **The probability function of a separate chance constraint** (Kall & Mayer 2005, Chapter 2,
(2.29) and (2.31), p.106, PDF p.116): with `ζ(x, η, ξ) = ηᵀx − ξ`,
`G(x) = ℙ( ζ(x, η, ξ) ≥ 0 ) = ℙ( ηᵀx ≥ ξ )`.

Here `η : Ω → ℝⁿ` and `ξ : Ω → ℝ` are random variables on the probability space `(Ω, P)`; no
distributional assumption is built in (the normality of `(η, ξ)` is a hypothesis of the theorems).

**Formalization Note.** `ηᵀx` is the dot product `η ω ⬝ᵥ x` on `Fin n → ℝ`. The probability is
`P.real` (the measure of the event as a real number), which is the book's `ℙ` for a probability
measure `P`. -/
noncomputable def probFun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (η : Ω → Fin n → ℝ) (ξ : Ω → ℝ) (x : Fin n → ℝ) : ℝ :=
  P.real {ω | 0 ≤ η ω ⬝ᵥ x - ξ ω}

end KallMayerSLP.NormalCC


