-- Prove2me | Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
-- name    : CohenPriceFairness_LocalWelfare_Sensitivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:24.332997+00:00
-- url     : https://prove2.me/theorems/69f7417a-8093-4a59-acdc-7f7a3ea16876
-- title:
--   Finite right derivatives and local sensitivity conventions
-- statement:
--   For a real function $f$, a finite right derivative $D$ at zero means
--   $$\lim_{\alpha\downarrow0}\frac{f(\alpha)-f(0)}{\alpha}=D.$$
--   Twice differentiable at $x$ means differentiable at every point in some neighborhood of $x$, with its derivative differentiable at $x$. This implies continuity at $x$ but imposes no continuity of the second derivative.
--
--   An active inverse for $f$ at $x$ consists of an open interval $(l,u)$ containing $x$, on which $f$ is monotone in either direction, and an inverse on its image: $g(f(p))=p$ on the interval and $g(y)\in(l,u)$, $f(g(y))=y$ for $y\in f((l,u))$. No nonzero derivative or smoothness of the inverse is assumed. Lemma regularity requires twice differentiability of $q_i,S_i,N_i,R_i$ at both baseline prices, and active inverses for $q_i,S_i,N_i$. Optimal policies are not required as a hypothesis to remain in these intervals.
--
--   For a derivative property $C$, a sensitivity claim at a baseline for one metric asserts both existence of at least one local optimal selection and, for every such selection $P$, existence of a finite right derivative $D$ of $\alpha\mapsto W(P(\alpha))$ satisfying $C(D)$. This predicate specifies what a theorem must conclude; it is not a market axiom.
-- source:
--   Cohen, Elmachtoub and Lei (2022), Price Discrimination with Fairness Constraints, Management Science, https://doi.org/10.1287/mnsc.2022.4317; published artifact, PDF pages = printed pages; SHA-256 b3f8804f1610eb36d8a2ef32e836f4a65285e6b8ad427f7c82172e7a3fd73147; p. 12, footnote 7; Lemma 1, pp. 30–31, and its proof pp. 31–33.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_FairPricing

open Filter Topology

namespace CohenPriceFairness.LocalWelfare

/-- The finite right derivative in footnote 7, p. 12. -/
def RightDerivative (f : ℝ → ℝ) (D : ℝ) : Prop :=
  Tendsto (fun α : ℝ => (f α - f 0) / α) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 D)

/-- Differentiability in a neighborhood and differentiability of the derivative at x.
Continuity at x follows; continuity of the second derivative is not assumed. -/
def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧ DifferentiableAt ℝ (deriv f) x

/-- Monotonicity and an inverse on the image of an open active interval at x.
No derivative condition on the inverse or nonzero derivative is imposed. -/
def ActiveInvertible (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ l u : ℝ, l < x ∧ x < u ∧
    (MonotoneOn f (Set.Ioo l u) ∨ AntitoneOn f (Set.Ioo l u)) ∧
    ∃ g : ℝ → ℝ,
      (∀ p ∈ Set.Ioo l u, g (f p) = p) ∧
      (∀ y ∈ f '' Set.Ioo l u, g y ∈ Set.Ioo l u ∧ f (g y) = y)

/-- Exactly the local regularity of Lemma 1 for all four source functions. -/
def LemmaRegularity (m : Market) (b : Prices) : Prop :=
  ∀ i,
    TwiceDifferentiableAt (demand m i) (b i) ∧
    TwiceDifferentiableAt (surplus m i) (b i) ∧
    TwiceDifferentiableAt (nonbuyer m i) (b i) ∧
    TwiceDifferentiableAt (profit m i) (b i) ∧
    ActiveInvertible (demand m i) (b i) ∧
    ActiveInvertible (surplus m i) (b i) ∧
    ActiveInvertible (nonbuyer m i) (b i)

/-- Existence of a policy, and the specified finite-derivative assertion for every policy. -/
def SensitivityClaim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) : Prop :=
  (∃ P : ℝ → Prices, LocalOptimalSelection m b k P) ∧
    ∀ P : ℝ → Prices, LocalOptimalSelection m b k P →
      ∃ D : ℝ, RightDerivative (fun α => welfare m (P α)) D ∧ C D

end CohenPriceFairness.LocalWelfare

/- Imported definition source (verbatim dependency snapshot for standalone inspection).

import Mathlib

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- A nonnegative valuation law with a finite first moment (pp. 6–7). -/
def ValuationLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, 0 ≤ v) ∧ Integrable (fun v : ℝ => v) μ

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_ValuationLaw

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- Two marginal valuation laws, real population masses, and common marginal cost. -/
structure Market where
  law : Fin 2 → Measure ℝ
  population : Fin 2 → ℝ
  cost : ℝ

/-- The general distribution-based market conventions, pp. 6–7. -/
def Market.Admissible (m : Market) : Prop :=
  0 ≤ m.cost ∧ ∀ i, 0 < m.population i ∧ ValuationLaw (m.law i)

noncomputable def demand (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  (m.law i (Set.Ici p)).toReal

noncomputable def surplus (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  ∫ v, max (v - p) 0 ∂m.law i

/-- Conditional mean of nonbuyers; explicitly zero on a null conditioning event. -/
noncomputable def nonbuyer (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  if m.law i (Set.Iio p) = 0 then 0
  else (∫ v in Set.Iio p, v ∂m.law i) / (m.law i (Set.Iio p)).toReal

noncomputable def profit (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  m.population i * (p - m.cost) * demand m i p

abbrev Prices := Fin 2 → ℝ

noncomputable def totalProfit (m : Market) (p : Prices) : ℝ :=
  profit m 0 (p 0) + profit m 1 (p 1)

/-- Group-specific surplus indices, as on pp. 7 and 31. -/
noncomputable def welfare (m : Market) (p : Prices) : ℝ :=
  totalProfit m p + m.population 0 * surplus m 0 (p 0) +
    m.population 1 * surplus m 1 (p 1)

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Market

namespace CohenPriceFairness.LocalWelfare

inductive Metric where
  | price | demand | surplus | nonbuyer
  deriving DecidableEq

noncomputable def metricValue (m : Market) : Metric → Fin 2 → ℝ → ℝ
  | .price => fun _ p => p
  | .demand => demand m
  | .surplus => surplus m
  | .nonbuyer => nonbuyer m

/-- All individual global maximizers on nonnegative prices. -/
def BaselineOptimal (m : Market) (b : Prices) : Prop :=
  ∀ i, 0 ≤ b i ∧ ∀ p : ℝ, 0 ≤ p → profit m i p ≤ profit m i (b i)

noncomputable def gap (m : Market) (k : Metric) (p : Prices) : ℝ :=
  |metricValue m k 0 (p 0) - metricValue m k 1 (p 1)|

/-- Equation (1), including its full parameter and price domains. -/
def FairFeasible (m : Market) (b : Prices) (k : Metric) (α : ℝ) (p : Prices) : Prop :=
  α ∈ Set.Icc 0 1 ∧ (∀ i, 0 ≤ p i) ∧ gap m k p ≤ (1 - α) * gap m k b

/-- The optimum set is defined by comparison against every feasible price pair. -/
def FairOptimal (m : Market) (b : Prices) (k : Metric) (α : ℝ) (p : Prices) : Prop :=
  FairFeasible m b k α p ∧
    ∀ q : Prices, FairFeasible m b k α q → totalProfit m q ≤ totalProfit m p

/-- A selection of actual optima on some right neighborhood, anchored at the baseline.
No continuity or differentiability, and no restriction to active price neighborhoods. -/
def LocalOptimalSelection (m : Market) (b : Prices) (k : Metric)
    (P : ℝ → Prices) : Prop :=
  P 0 = b ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
    ∀ α ∈ Set.Icc 0 ε, FairOptimal m b k α (P α)

end CohenPriceFairness.LocalWelfare
-/


