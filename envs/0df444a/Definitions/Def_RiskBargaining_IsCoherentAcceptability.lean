-- Prove2me | Definitions.Def_RiskBargaining_IsCoherentAcceptability
-- name    : RiskBargaining_IsCoherentAcceptability
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:12.202515+00:00
-- url     : https://prove2.me/theorems/36195e25-8ba9-47d3-b10f-a9d8220a433e
-- title:
--   Coherent acceptability functional on $L^p$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $p\ge 1$. A functional $\mathcal A:L^p\to\mathbb R$ is a **coherent acceptability functional** if for all $Y,Z\in L^p$, all $\lambda\ge 0$ and all $c\in\mathbb R$:
--
--   1. Monotonicity: $Y\le Z$ almost surely implies $\mathcal A(Y)\le\mathcal A(Z)$.
--   2. Positive homogeneity: $\mathcal A(\lambda Y)=\lambda\mathcal A(Y)$.
--   3. Super-additivity: $\mathcal A(Y+Z)\ge\mathcal A(Y)+\mathcal A(Z)$.
--   4. Translation invariance: $\mathcal A(Y+c)=\mathcal A(Y)+c$.
--
--   This is the class of risk preferences of the players in the bargaining game. Expectation and the Average Value-at-Risk belong to it.
--
--   **Formalization Note** $L^p$ is `Lp ℝ p μ`, whose elements are almost-everywhere classes, and the constant $c$ is `Lp.const p μ c`. The case $\lambda=0$ is included. Neither continuity nor the bound $\mathcal A\le\mathbb E$ is part of the definition.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Definition 1, p.7

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Coherent acceptability functional.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Definition 1, p.7.

`A : L^p → ℝ` is coherent when, for all `Y, Z ∈ L^p`, `lam ≥ 0` and `c ∈ ℝ`, the four clauses below
hold: monotonicity, positive homogeneity, super-additivity, translation invariance.

**Formalization Note.** `L^p` is `Lp ℝ p μ`; its elements are a.e.-classes. The constant `c` of clause 4
is `Lp.const p μ c`. Positive homogeneity includes `lam = 0`. Nothing else is required: no continuity,
no bound `A ≤ E`, no dual representation. -/
structure IsCoherentAcceptability (A : Lp ℝ p μ → ℝ) : Prop where
  /-- Monotonicity: `Y ≤ Z` almost surely implies `A Y ≤ A Z`. -/
  mono : ∀ Y Z : Lp ℝ p μ, (⇑Y) ≤ᵐ[μ] (⇑Z) → A Y ≤ A Z
  /-- Positive homogeneity: `A (lam Y) = lam A Y` for `lam ≥ 0`. -/
  pos_homog : ∀ (lam : ℝ) (Y : Lp ℝ p μ), 0 ≤ lam → A (lam • Y) = lam * A Y
  /-- Super-additivity: `A (Y + Z) ≥ A Y + A Z`. -/
  super_add : ∀ Y Z : Lp ℝ p μ, A Y + A Z ≤ A (Y + Z)
  /-- Translation invariance: `A (Y + c) = A Y + c`. -/
  translation : ∀ (Y : Lp ℝ p μ) (c : ℝ), A (Y + Lp.const p μ c) = A Y + c

end RiskBargaining


