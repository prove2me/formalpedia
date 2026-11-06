-- Prove2me | Definitions.Def_RiskDistMDP_DPP_rcd
-- name    : RiskDistMDP_DPP_rcd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:42.996264+00:00
-- url     : https://prove2.me/theorems/e8f99acc-f136-4b7a-9cda-de07f0257377
-- title:
--   Regular conditional distribution $P^{Y|\mathcal G}$ (Definition 2.1)
-- statement:
--   For a real random variable $Y$ and a sub-σ-algebra $\mathcal G\subseteq\mathcal H$, a **regular conditional distribution** $P^{Y|\mathcal G}:\Omega\times\mathcal B(\mathbb R)\to[0,1]$ is a version of $\mathbb P(Y\in\cdot\,|\,\mathcal G)$ such that
--
--   1. $\omega\mapsto P^{Y|\mathcal G}(\omega,A)$ is $\mathcal G$-measurable for every Borel $A$;
--   2. $P^{Y|\mathcal G}(\omega,\cdot)$ is a probability measure for every $\omega$;
--   3. $P^{Y|\mathcal G}(\omega,A)=\mathbb P(Y\in A\,|\,\mathcal G)(\omega)$ for $\mathbb P$-a.e. $\omega$.
--
--   It exists because $\mathbb R$ is Polish, and is unique up to a null set. The dynamic risk measure of the paper applies $\sigma_{t,x}$ to $P^{W|\mathcal U_t}(\omega,\cdot)$.
--
--   **Formalization Note** The definition picks one version: Mathlib's `condDistrib Y id ℙ`, with the identity $\Omega\to\Omega$ whose codomain carries $\mathcal G$. Every statement that uses it is a $\mathbb P$-a.s. statement, so the choice is immaterial.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Definition 2.1, p. 5; p. 6

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RiskDistMDP.DPP

/-- The **regular conditional distribution** `P^{Y|𝒢}(ω, ·)` of a real random variable `Y` given a
sub-σ-algebra `𝒢` (arXiv:2203.09612v4, Definition 2.1, p.5): a version of `ℙ(Y ∈ · | 𝒢)` that is a
probability measure for every `ω` and `𝒢`-measurable in `ω`.

**Formalization Note** It is Mathlib's `condDistrib Y id Pr` with the identity `Ω → Ω`, whose
codomain carries `𝒢`; it is a Markov kernel from `(Ω, 𝒢)` to `ℝ`, so `rcd Pr 𝒢 Y ω` is a probability
measure for every `ω` and `ω ↦ rcd Pr 𝒢 Y ω` is `𝒢`-measurable. For `𝒢 ≤ ℋ` and measurable `Y`
it is a version of `ℙ(Y ∈ · | 𝒢)` (`condDistrib_ae_eq_condExp`); it is a specific version, and every
use of it in the mission is a `Pr`-a.s. statement, so the choice of version is immaterial. -/
noncomputable def rcd {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsFiniteMeasure Pr]
    (𝒢 : MeasurableSpace Ω) (Y : Ω → ℝ) (ω : Ω) : Measure ℝ :=
  @condDistrib Ω Ω ℝ _ _ _ mΩ 𝒢 Y id Pr _ ω

end RiskDistMDP.DPP


