-- Prove2me | Definitions.Def_SimpleCorrMFG_Conv_RegCondDistrib
-- name    : SimpleCorrMFG_Conv_RegCondDistrib
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:46.725469+00:00
-- url     : https://prove2.me/theorems/d4e6c2ac-3b67-44d3-b38c-9c60e154aba0
-- title:
--   Appendix A, pp. 28–30 — regular conditional distributions and the empirical measure of a finite sequence
-- statement:
--   This file defines two general probabilistic objects used in Appendix A.
--
--   **Regular conditional distributions.** Let $(\Omega,\mathcal F,P)$ be a probability space, $Y$ a random variable with values in a measurable space $\mathcal Y$, $\mathcal C\subseteq\mathcal F$ a σ-algebra and $\kappa:\Omega\to\mathcal P(\mathcal Y)$. Then $\kappa$ is a regular conditional distribution of $Y$ given $\mathcal C$ if every $\kappa(\omega)$ is a probability measure and, for every measurable $A\subseteq\mathcal Y$, $\omega\mapsto\kappa(\omega)(A)$ is $\mathcal C$-measurable and
--   $$P(\{Y\in A\}\cap C)=\mathbb E\big[\mathbf 1_C\,\kappa(A)\big]\qquad\text{for all }C\in\mathcal C,$$
--   that is, $P(Y\in A\mid\mathcal C)=\kappa(A)$ almost surely.
--
--   **Empirical measure.** For random variables $Y_1,\dots,Y_N$ with values in $\mathcal Y$,
--   $$\mu^N_\omega=\frac1N\sum_{i=1}^N\delta_{Y_i(\omega)},\qquad\omega\in\Omega.$$
--
--   **Formalization Note** The expectation $\mathbb E[\mathbf 1_C\kappa(A)]$ is a lower Lebesgue integral of $[0,\infty]$-valued functions. The empirical measure of an empty family ($N=0$) is the zero measure.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 28–30 (Appendix A: the notion of regular conditional distribution used in Lemmas A.3–A.5; the empirical measure of Lemma A.5)

import Mathlib

namespace SimpleCorrMFG.Conv

open MeasureTheory

/-- `κ` is a regular conditional distribution of the random variable `Y` given the σ-algebra `C`
(Appendix A, pp. 28–30): every `κ(ω)` is a probability measure on `𝒴` and, for every Borel
`A ⊆ 𝒴`, `ω ↦ κ(ω)(A)` is `C`-measurable and `P({Y ∈ A} ∩ C) = E[1_C κ(A)]` for all `C ∈ C`; i.e.
`P(Y ∈ A | C) = κ(A)` almost surely. -/
def IsRegCondDistrib {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] (P : Measure Ω)
    (Y : Ω → 𝒴) (κ : Ω → Measure 𝒴) (C : MeasurableSpace Ω) : Prop :=
  (∀ ω, IsProbabilityMeasure (κ ω)) ∧
  ∀ A : Set 𝒴, MeasurableSet A →
    Measurable[C] (fun ω => κ ω A) ∧
      ∀ s : Set Ω, MeasurableSet[C] s → P (Y ⁻¹' A ∩ s) = ∫⁻ ω in s, κ ω A ∂P

/-- The empirical measure `μ^N_ω = N⁻¹ ∑_{i=1}^N δ_{Y_i(ω)}` of `Y_1, …, Y_N` (Lemma A.5, p. 30). For
`N = 0` it is the zero measure. -/
noncomputable def empiricalMeasure {Ω 𝒴 : Type*} [MeasurableSpace 𝒴] {N : ℕ} (Y : Fin N → Ω → 𝒴)
    (ω : Ω) : Measure 𝒴 :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (Y i ω)

end SimpleCorrMFG.Conv


