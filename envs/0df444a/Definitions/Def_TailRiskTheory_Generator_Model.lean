-- Prove2me | Definitions.Def_TailRiskTheory_Generator_Model
-- name    : TailRiskTheory_Generator_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:54.057436+00:00
-- url     : https://prove2.me/theorems/4df309ec-31eb-437d-8320-8e901569310a
-- title:
--   §2–§4 and App. A, pp. 4–10, 18–19 — L^∞, the p-tail law (2), X^(p), p-tail risk measures and pairs (Defs. 1–2), (A3)–(A7), Defs. A.1–A.2, S_n
-- statement:
--   This file fixes the objects of Liu and Wang, *A Theory for Measures of Tail Risk*, on an atomless probability space $(\Omega,\mathcal F,\mathbb P)$, with the space of risks taken to be $\mathcal X = L^\infty$. A positive value of a random variable $X$ is a loss. Write $F_X(x)=\mathbb P(X\le x)$ for the distribution function (the published `distFn`).
--
--   1. **$L^\infty$** (the published `Linf`). The measurable functions $X:\Omega\to\mathbb R$ with $|X|\le C$ almost surely for some constant $C$.
--   2. **Essential infimum.** $\operatorname{ess\text{-}inf}(X)=\inf\{x\in\mathbb R: F_X(x)>0\}$.
--   3. **The $p$-tail** (eq. (2)). For $p\in(0,1)$ the $p$-tail $X_p$ of $X$ is a random variable with distribution function
--   $$\mathbb P(X_p\le x)=\frac{(\mathbb P(X\le x)-p)_+}{1-p},\qquad x\in\mathbb R .$$
--   A random variable $Z$ *has the law of $X_p$* if $F_Z$ equals this function.
--   4. **The mixture $X^{(p)}$** (p. 7). $Z$ has the law of $X^{(p)}$ if
--   $$\mathbb P(Z\le x)=p\,\mathbb 1_{\{x\ge \operatorname{ess\text{-}inf}(X)\}}+(1-p)\,\mathbb P(X\le x),\qquad x\in\mathbb R .$$
--   5. **Bernoulli.** $B\sim\mathrm{Bern}(p)$: $B$ is measurable, takes only the values $0$ and $1$, and $\mathbb P(B=1)=p$.
--   6. **$p$-tail risk measure** (Definition 1). A functional $\rho$ with $\rho(X)=\rho(Y)$ for all $X,Y\in\mathcal X$ with $X_p\overset{d}{=}Y_p$.
--   7. **$p$-tail pair** (Definition 2 with (3)). $(\rho,\rho^*)$ is a $p$-tail pair if $\rho^*$ is law-invariant and $\rho(X)=\rho^*(Z)$ for every $X\in\mathcal X$ and every $Z\in\mathcal X$ with the law of $X_p$; that is, $\rho(X)=\rho^*(X_p)$.
--   8. **Properties** (Appendix A), all over $\mathcal X$: convexity (A3) $\rho(\lambda X+(1-\lambda)Y)\le\lambda\rho(X)+(1-\lambda)\rho(Y)$ for $\lambda\in[0,1]$; positive homogeneity (A4) $\rho(\lambda X)=\lambda\rho(X)$ for $\lambda>0$; subadditivity (A5) $\rho(X+Y)\le\rho(X)+\rho(Y)$; comonotonic additivity (A6) $\rho(X+Y)=\rho(X)+\rho(Y)$ for comonotonic $X,Y$. Monotonicity (A1), translation invariance (A2) $\rho(X-m)=\rho(X)-m$, monetary risk measures and law invariance (A0) are the published `IsMonotone`, `IsTranslationInvariant`, `IsMonetary`, `IsLawInvariant`.
--   9. **Definition A.1.** A convex risk measure satisfies (A1), (A2), (A3); a coherent risk measure satisfies (A1), (A2), (A3), (A4).
--   10. **Definition A.2.** $X\prec_{\mathrm{st}}Y$ if $\mathbb E[f(X)]\le\mathbb E[f(Y)]$ for every increasing $f$ for which both expectations exist; for $X,Y\in L^1$, $X\prec_{\mathrm{cx}}Y$ if the same holds for every convex $f$. (A7): $\rho(X)\le\rho(Y)$ whenever $X\prec_{\mathrm{cx}}Y$.
--   11. **Aggregation sets** (p. 10). For distributions $F_1,\dots,F_n$ (given as the laws of $X_1,\dots,X_n\in\mathcal X$),
--   $$\mathcal S_n(F_1,\dots,F_n)=\{Y_1+\dots+Y_n: Y_i\in\mathcal X,\ Y_i\sim F_i\},$$
--   and $\mathcal S_n(F_1^{[p]},\dots,F_n^{[p]})$ is the same set with $Y_i$ having the law of $(X_i)_p$.
--
--   These are the objects of Theorem 1 (the transfer of properties between a tail risk measure and its generator) and of Theorem 3 (worst-case aggregation).
--
--   **Formalization Note** The paper's domain is a convex cone $\mathcal X\supseteq L^\infty$ with $(-\infty,\infty]$-valued risk measures; this file takes $\mathcal X=L^\infty$, the reading the paper itself offers (p. 5). Then $\mathcal X^*=\mathcal X$ (p. 7), and risk measures are real-valued functions on $\Omega\to\mathbb R$ whose values off $L^\infty$ never enter. $X_p$ and $X^{(p)}$ are relations on distribution functions, not constructions. The real infimum in the essential infimum returns the junk value $0$ only off $L^\infty$, and every use sits behind $X\in L^\infty$. "Both expectations exist" is integrability of $f(X)$ and $f(Y)$; the convex order is the published `ConvexOrder` with both variables on $(\Omega,\mathbb P)$, plus integrability of $X$ and $Y$. Distributions $F_i$ are represented by random variables in $L^\infty$, which is the paper's "compatible with random variables in $\mathcal X$".
-- source:
--   Liu and Wang, A Theory for Measures of Tail Risk, SSRN 2841909 (journal accepted version, Feb 19, 2020), pp. 4–10, §2–§4, Eqs. (2), (3), Definitions 1–2; pp. 18–19, (A0)–(A7), Definitions A.1–A.2

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting
import Definitions.Def_TailRiskSharing_VaRTail_Setting
import Definitions.Def_TailRiskSharing_TailConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone
import Definitions.Def_StochasticOrders_Convex_ConvexOrder

namespace TailRiskTheory.Generator

open MeasureTheory ProbabilityTheory
-- `Linf P` (published, §2 p. 4): the measurable, essentially bounded random variables. The mission
-- takes the paper's domain `𝒳` to be `L^∞` (p. 5); then `𝒳^* = 𝒳` (p. 7).
open TailRiskSharing.TailConv (Linf)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 7: the essential infimum `ess-inf(X) = inf {x : P(X ≤ x) > 0}`. It is the essential infimum for
`X ∈ L^∞`; off `L^∞` (set empty or unbounded below) the real `sInf` returns the junk value `0`, so every
use sits behind `X ∈ Linf P`. -/
noncomputable def essInfRV (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  sInf {x : ℝ | 0 < TailRiskSharing.VaRConv.distFn P X x}

/-- Eq. (2), p. 6: the distribution function of the `p`-tail `X_p` of `X`,
`P(X_p ≤ x) = (P(X ≤ x) - p)_+ / (1 - p)`. -/
noncomputable def tailDistFn (P : Measure Ω) (p : ℝ) (X : Ω → ℝ) (x : ℝ) : ℝ :=
  max (TailRiskSharing.VaRConv.distFn P X x - p) 0 / (1 - p)

/-- Eq. (2), p. 6: `Z` has the law of the `p`-tail `X_p` of `X`, i.e. `Z =d X_p`. -/
def IsPTailOf (P : Measure Ω) (p : ℝ) (X Z : Ω → ℝ) : Prop :=
  ∀ x : ℝ, TailRiskSharing.VaRConv.distFn P Z x = tailDistFn P p X x

/-- p. 7: `Z` has the law of `X^(p)`,
`P(X^(p) ≤ x) = p 1{x ≥ ess-inf(X)} + (1 - p) P(X ≤ x)`. -/
def IsPMixOf (P : Measure Ω) (p : ℝ) (X Z : Ω → ℝ) : Prop :=
  ∀ x : ℝ, TailRiskSharing.VaRConv.distFn P Z x =
    p * (if essInfRV P X ≤ x then 1 else 0) + (1 - p) * TailRiskSharing.VaRConv.distFn P X x

/-- p. 7: `B ∼ Bern(p)`, meaning `P(B = 1) = p` and `P(B = 0) = 1 - p`. -/
def IsBernoulli (P : Measure Ω) (p : ℝ) (B : Ω → ℝ) : Prop :=
  Measurable B ∧ (∀ ω, B ω = 0 ∨ B ω = 1) ∧ P.real {ω | B ω = 1} = p

/-- Definition 1, p. 6, with `𝒳 = L^∞`: `ρ` is a `p`-tail risk measure if `ρ(X) = ρ(Y)` for all
`X, Y ∈ 𝒳` with `X_p =d Y_p`. -/
def IsPTailRiskMeasure (P : Measure Ω) (p : ℝ) (rho : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ Linf P, ∀ Y ∈ Linf P,
    (∀ x : ℝ, tailDistFn P p X x = tailDistFn P p Y x) → rho X = rho Y

/-- Definition 2, p. 8, with (3), p. 7, on `𝒳 = L^∞`: `(ρ, ρ^*)` is a `p`-tail pair if `ρ^*` is
law-invariant and `ρ = T_p[ρ^*]`, i.e. `ρ(X) = ρ^*(X_p)` for every `X ∈ 𝒳` and every `Z ∈ 𝒳` with the
law of `X_p`. -/
def IsPTailPair (P : Measure Ω) (p : ℝ) (rho rhoStar : (Ω → ℝ) → ℝ) : Prop :=
  TailRiskSharing.VaRTail.IsLawInvariant P (Linf P) rhoStar ∧
    ∀ X ∈ Linf P, ∀ Z ∈ Linf P, IsPTailOf P p X Z → rho X = rhoStar Z

/-- (A3), p. 18: convexity, `ρ(λX + (1 - λ)Y) ≤ λρ(X) + (1 - λ)ρ(Y)` for `λ ∈ [0, 1]`. -/
def IsConvexRM (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ Linf P, ∀ Y ∈ Linf P, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    rho (fun ω => lam * X ω + (1 - lam) * Y ω) ≤ lam * rho X + (1 - lam) * rho Y

/-- (A4), p. 18: positive homogeneity, `ρ(λX) = λρ(X)` for `λ > 0`. -/
def IsPosHomogeneous (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ Linf P, ∀ lam : ℝ, 0 < lam → rho (fun ω => lam * X ω) = lam * rho X

/-- (A5), p. 18: subadditivity, `ρ(X + Y) ≤ ρ(X) + ρ(Y)`. -/
def IsSubadditive (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ Linf P, ∀ Y ∈ Linf P, rho (fun ω => X ω + Y ω) ≤ rho X + rho Y

/-- (A6), p. 18: comonotonic additivity, `ρ(X + Y) = ρ(X) + ρ(Y)` for comonotonic `X, Y`. -/
def IsComonoAdditive (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ Linf P, ∀ Y ∈ Linf P, TailRiskSharing.ComonoConv.Comonotone P X Y →
    rho (fun ω => X ω + Y ω) = rho X + rho Y

/-- Definition A.1, p. 18: a convex risk measure satisfies (A1), (A2) and (A3). -/
def IsConvexRiskMeasure (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  TailRiskSharing.VaRTail.IsMonetary P (Linf P) rho ∧ IsConvexRM P rho

/-- Definition A.1, p. 18: a coherent risk measure satisfies (A1), (A2), (A3) and (A4). -/
def IsCoherent (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  IsConvexRiskMeasure P rho ∧ IsPosHomogeneous P rho

/-- Definition A.2, p. 18: `X ≺st Y` if `E[f(X)] ≤ E[f(Y)]` for every increasing `f` for which both
expectations exist. -/
def StOrder (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Monotone f → Integrable (fun ω => f (X ω)) P → Integrable (fun ω => f (Y ω)) P →
    ∫ ω, f (X ω) ∂P ≤ ∫ ω, f (Y ω) ∂P

/-- Definition A.2, p. 18: for `X, Y ∈ L^1`, `X ≺cx Y` if `E[f(X)] ≤ E[f(Y)]` for every convex `f` for
which both expectations exist (the published convex order with both variables on `(Ω, P)`). -/
def CxOrder (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  Integrable X P ∧ Integrable Y P ∧ StochasticOrders.Convex.ConvexOrder P P X Y

/-- (A7), p. 19: `≺cx`-monotonicity, `ρ(X) ≤ ρ(Y)` if `X ≺cx Y`. -/
def IsCxMonotone (P : Measure Ω) (rho : (Ω → ℝ) → ℝ) : Prop :=
  ∀ X ∈ Linf P, ∀ Y ∈ Linf P, CxOrder P X Y → rho X ≤ rho Y

/-- p. 10: the aggregation set `S_n(F_1, …, F_n) = {X_1 + ⋯ + X_n : X_i ∈ 𝒳, X_i ∼ F_i}`, where
`F_i` is the law of the given representative `Xs i`. -/
def AggSet (P : Measure Ω) {n : ℕ} (Xs : Fin n → Ω → ℝ) : Set (Ω → ℝ) :=
  {S | ∃ Ys : Fin n → Ω → ℝ,
    (∀ i, Ys i ∈ Linf P ∧ ∀ x : ℝ,
      TailRiskSharing.VaRConv.distFn P (Ys i) x = TailRiskSharing.VaRConv.distFn P (Xs i) x) ∧
    S = fun ω => ∑ i, Ys i ω}

/-- p. 10: the aggregation set `S_n(F_1^[p], …, F_n^[p])` of the `p`-tail distributions, where
`F_i^[p]` is the law of `(Xs i)_p`. -/
def TailAggSet (P : Measure Ω) (p : ℝ) {n : ℕ} (Xs : Fin n → Ω → ℝ) : Set (Ω → ℝ) :=
  {T | ∃ Ys : Fin n → Ω → ℝ,
    (∀ i, Ys i ∈ Linf P ∧ IsPTailOf P p (Xs i) (Ys i)) ∧
    T = fun ω => ∑ i, Ys i ω}

end TailRiskTheory.Generator


