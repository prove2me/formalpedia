-- Prove2me | Definitions.Def_RecursiveStopping_IsStrongMarkovFlow
-- name    : RecursiveStopping_IsStrongMarkovFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:49.504999+00:00
-- url     : https://prove2.me/theorems/c58956e5-66f9-46b2-aaf6-0295cd8e0e34
-- title:
--   Strong Markov property of a stochastic flow
-- statement:
--   Let $X=(X^x_t)_{x\in S,\,t\ge0}$ be a stochastic flow on $(\Omega,\mathcal F,\mathsf P)$ with values in a measurable space $S$, so that $X^x$ is the process started at $x$, and write $\mathsf E_x[\Phi(X_\cdot)]:=\mathsf E[\Phi(X^x_\cdot)]$. The flow has the **strong Markov property** with respect to $\mathbb F$ when, for every starting point $x$, every $\mathbb F$-stopping time $\tau$ with values in $[0,\infty]$ and every bounded measurable functional $\Phi$ of the path,
--
--   $$
--   \mathsf E\big[\Phi(X^x_{\tau+\cdot})\,\mathbf 1_{\{\tau<\infty\}}\,\big|\,\mathcal F_\tau\big]=\mathbf 1_{\{\tau<\infty\}}\,\mathsf E_{X^x_\tau}\big[\Phi(X_\cdot)\big]\qquad\mathsf P\text{-a.s.}
--   $$
--
--   This is the identity $\mathsf E_{X_\tau}[f(X_\cdot)]=\mathsf E[f(X_{\tau+\cdot})\,|\,\mathcal F_\tau]$ the paper uses to restart the problem at a stopping time.
--
--   **Formalization Note** Path space $S^{[0,\infty)}$ carries the product $\sigma$-algebra. The paper writes the identity for "any integrable functional"; bounded measurable functionals determine it.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, §2, pp.5–6

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping

/-- The **strong Markov property of a stochastic flow** (Colaneri & De Angelis,
arXiv:1905.02650v4, §2, pp.5–6): for every `F`-stopping time `τ`,
`E_{X_τ}[f(X_·)] = E[f(X_{τ+·}) | F_τ]`, where `E_x[f(X_·)] = E[f(X^x_·)]`.

For a flow `X : S → ℝ≥0 → Ω → S` (`X x t ω = X^x_t(ω)`) on one probability space `(Ω, F, P)`,
this says: for every starting point `x`, every `𝔽`-stopping time `τ : Ω → [0, ∞]` and every
bounded measurable functional `Φ` of the path (product σ-algebra on `ℝ≥0 → S`),
$$E\big[\Phi(X^x_{\tau+\cdot})\,\mathbf 1_{\{\tau<\infty\}}\,\big|\,\mathcal F_\tau\big]
  = \mathbf 1_{\{\tau<\infty\}}\,\big(y\mapsto E[\Phi(X^y_\cdot)]\big)(X^x_\tau)\quad P\text{-a.s.}$$

**Formalization Note** The paper states the identity for "any integrable functional"; bounded
measurable functionals determine it (truncation and monotone convergence). The identity is
asserted on `{τ < ∞}`, where `X_{τ+·}` is defined. -/
def IsStrongMarkovFlow {S Ω : Type*} [MeasurableSpace S] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ) (X : S → ℝ≥0 → Ω → S) : Prop :=
  ∀ (x : S) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝔽 τ) (Φ : (ℝ≥0 → S) → ℝ),
    Measurable Φ → (∃ C : ℝ, ∀ w, |Φ w| ≤ C) →
    P[{ω | τ ω ≠ ⊤}.indicator (fun ω => Φ (fun s => X x ((τ ω).toNNReal + s) ω))
        | hτ.measurableSpace]
      =ᵐ[P] {ω | τ ω ≠ ⊤}.indicator
        (fun ω => ∫ ω', Φ (fun s => X (X x (τ ω).toNNReal ω) s ω') ∂P)

end RecursiveStopping


