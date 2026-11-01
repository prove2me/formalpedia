-- Prove2me | Definitions.Def_SupermodDRO_scenarioWorstCase
-- name    : SupermodDRO_scenarioWorstCase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:47.209102+00:00
-- url     : https://prove2.me/theorems/1e450b06-f24b-49fb-8f33-81b089cf186e
-- title:
--   Worst-case expectation $\sup_{\mathbb P^k\in\mathcal F^k}\mathbb E_{\mathbb P^k}[h(\tilde z)]$
-- statement:
--   For an extended-real function $h$ on $\mathbb R^n$ and the data $(\mu^k,\delta^k,\underline z^k,\overline z^k)$ of one scenario,
--   $$
--   \sup_{\mathbb P^k\in\mathcal F^k}\mathbb E_{\mathbb P^k}[h(\tilde z)]\in[-\infty,+\infty].
--   $$
--   With $h=g(x,\cdot)$ it is the worst-case expected second-stage cost in a fixed scenario, the quantity of Propositions 1 and 3.
--
--   **Formalization Note** The expectation is the platform's extended expectation $\mathbb E[h]=\int h^+-\int h^-$ (Lebesgue integrals of $[0,\infty]$-valued functions), equal to $+\infty$ whenever $\int h^+=\infty$; in particular it is $+\infty$ when $h=+\infty$ on a set of positive probability.
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proposition 1, p.8, and Proposition 3, p.10

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_SupermodDRO_scenarioSet

open MeasureTheory

namespace SupermodDRO

/-- **Worst-case expectation over a fixed scenario, `sup_{ℙᵏ∈𝓕ᵏ} E_{ℙᵏ}[h(z̃)]`.** Long, Qi & Zhang,
*Supermodularity in Two-Stage Distributionally Robust Optimization*, author manuscript (June 2022),
Proposition 1, p.8, and Proposition 3, p.10, where `h = g(x, ·)`.

**Formalization Note** The expectation of the extended-real function `h` is the published
`DupacovaWets.Consistency.expect`: `∫ h⁺ − ∫ h⁻` as Lebesgue integrals of `[0, ∞]`-valued
functions, and `+∞` whenever `∫ h⁺ = ∞` (in particular when `h = +∞` on a set of positive mass).
The supremum is taken in `EReal`. -/
noncomputable def scenarioWorstCase {n : ℕ} (h : (Fin n → ℝ) → EReal) (μ δ zl zu : Fin n → ℝ) :
    EReal :=
  ⨆ P ∈ scenarioSet μ δ zl zu, DupacovaWets.Consistency.expect P h

end SupermodDRO


