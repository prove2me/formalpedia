-- Prove2me | Definitions.Def_AIMInventoryAudit_UnknownBound_Costs
-- name    : AIMInventoryAudit_UnknownBound_Costs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:30:45.032378+00:00
-- url     : https://prove2.me/theorems/2ffb99b2-0907-4b13-aaba-e11d622b9902
-- title:
--   Unrestricted demand law, newsvendor quantile, and centered inventory costs
-- statement:
--   Let $\mu$ be a probability measure on finite nonnegative real demand, with no moment restriction. Its IID path measure is $\mu^{\otimes\mathbb N}$. For holding and shortage costs $h,b\ge0$, $B=\max\{b,h\}>0$, define
--
--   $$F(y)=\mu\{d:d\le y\},\qquad A=\{y\ge0:F(y)\ge b/(b+h)\},\qquad q=\inf A,$$
--   $$\ell(y,d)=h(y-d)^++b(d-y)^+,\quad Q_e(y)=\int\ell(y,d)\,d\mu\in[0,\infty],\quad R(y)=\int[\ell(y,d)-\ell(q,d)]\,d\mu.$$
--
--   The real cost $Q(y)=\int\ell(y,d)\,d\mu$ is used only in clauses that establish its integrability. The centered cost integrates the pointwise loss difference, which is bounded for each finite stock level, even for infinite-mean demand. Averages and partial sums evaluate the published, law-free modified AIM recursion; the explicit bound is $C=B(T^{-(1/2-\delta)}+T^{-1/2}+q^{1+2/\delta}/T)$.
--
--   The quantile is a real-valued wrapper around the published law-free `LostSalesOrderUpTo.Asymptotic.newsvendorLevel`, whose nonnegative infimum is the displayed infimum. These objects separate an unrestricted cost model from the operational recursion. Neither a minimization result, unbiasedness, nor any regret inequality is a definition field.
--
--   **Formalization Note** The law is a Mathlib probability measure on $\mathbb R_{\ge0}$, rather than the published positive-finite-mean demand structure. For $h>0$, nonemptiness of $A$ is a conclusion to establish; at $h=0$, statements require $A$ to be nonempty so a finite quantile exists. All elements of $A$ are nonnegative, so it is bounded below; the unused empty-infimum default is zero. Real costs on nonintegrable inputs have Lean’s default zero and are never asserted to equal genuine costs there. $Q_e$ keeps infinity. Period $t$ reads demand coordinate $t-1$, and every theorem uses only $1\le t\le T$.
-- source:
--   Huh & Rusmevichientong (2009), A Nonparametric Asymptotic Analysis of Inventory Planning with Censored Demand, author’s manuscript associated with doi:10.1287/moor.1080.0355, https://doi.org/10.1287/moor.1080.0355, §2.1, Equation (1) and newsvendor display, printed p. 6 / PDF p. 6; §3.1, printed pp. 11–12 / PDF pp. 11–12.

import Mathlib
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Definitions.Def_AIMInventory_UnknownBound_AIM

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace AIMInventoryAudit.UnknownBound

/-! Huh & Rusmevichientong (2009), author's manuscript, pp. 5–7 and 11–12.
The marginal law is a bare probability measure on finite nonnegative real demand.
No finite-mean or positive-mean condition is bundled into the model. -/

/-- IID demand paths; coordinate zero is paper period one. -/
def pathLaw (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] : Measure (ℕ → ℝ≥0) :=
  Measure.infinitePi (fun _ : ℕ => μ)

/-- The source CDF F(y) = P(D ≤ y), including equality atoms. -/
def cdf (μ : Measure ℝ≥0) (y : ℝ) : ℝ :=
  μ.real {d : ℝ≥0 | (d : ℝ) ≤ y}

/-- Nonnegative levels reaching the critical ratio, p. 6. -/
def criticalSet (μ : Measure ℝ≥0) (h b : ℝ) : Set ℝ :=
  {y | 0 ≤ y ∧ b / (b + h) ≤ cdf μ y}

/-- The published law-free newsvendor level, exposed as a real stock level.
Theorems derive nonemptiness when h > 0 and require it only at the h = 0 endpoint.
Outside that domain the empty-set infimum is the unused Lean default zero. -/
def quantile (μ : Measure ℝ≥0) (h b : ℝ) : ℝ :=
  (LostSalesOrderUpTo.Asymptotic.newsvendorLevel μ h b : ℝ)

/-- Finite sample loss ℓ(y,d), Equation (1), p. 6. -/
def loss (h b y : ℝ) (d : ℝ≥0) : ℝ :=
  h * max (y - (d : ℝ)) 0 + b * max ((d : ℝ) - y) 0

/-- Genuine nonnegative expected cost, possibly infinite. -/
def extendedCost (μ : Measure ℝ≥0) (h b y : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, ENNReal.ofReal (loss h b y d) ∂μ

/-- Real expected cost, used in source clauses only after finiteness is established. -/
def realCost (μ : Measure ℝ≥0) (h b y : ℝ) : ℝ := ∫ d, loss h b y d ∂μ

/-- Center the sample losses before integration, so infinite means are allowed. -/
def centeredCost (μ : Measure ℝ≥0) (h b y : ℝ) : ℝ :=
  ∫ d, (loss h b y d - loss h b (quantile μ h b) d) ∂μ

/-- Cumulative centered costs on a finite set of one-based rounds of the published run. -/
def centeredSum (μ : Measure ℝ≥0) (δ b h y₁ : ℝ) (I : Finset ℕ)
    (d : ℕ → ℝ≥0) : ℝ :=
  ∑ t ∈ I, centeredCost μ h b (AIMInventory.UnknownBound.modAimTarget δ b h y₁ d t)

/-- Source cumulative cost differences, only used in finite-cost clauses. -/
def realGapSum (μ : Measure ℝ≥0) (δ b h y₁ : ℝ) (I : Finset ℕ)
    (d : ℕ → ℝ≥0) : ℝ :=
  ∑ t ∈ I, (realCost μ h b (AIMInventory.UnknownBound.modAimTarget δ b h y₁ d t) -
    realCost μ h b (quantile μ h b))

/-- Finite-horizon average centered cost. -/
def centeredAverage (μ : Measure ℝ≥0) (δ b h y₁ : ℝ) (T : ℕ) (d : ℕ → ℝ≥0) : ℝ :=
  (1 / (T : ℝ)) * centeredSum μ δ b h y₁ (Finset.Icc 1 T) d

/-- Finite-horizon average of genuine extended costs. -/
def extendedAverage (μ : Measure ℝ≥0) (δ b h y₁ : ℝ) (T : ℕ)
    (d : ℕ → ℝ≥0) : ℝ≥0∞ :=
  (∑ t ∈ Finset.Icc 1 T,
    extendedCost μ h b (AIMInventory.UnknownBound.modAimTarget δ b h y₁ d t)) / (T : ℝ≥0∞)

/-- The source's real average cost, evaluated only under the finite-cost implication. -/
def realAverage (μ : Measure ℝ≥0) (δ b h y₁ : ℝ) (T : ℕ) (d : ℕ → ℝ≥0) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
    realCost μ h b (AIMInventory.UnknownBound.modAimTarget δ b h y₁ d t)

/-- Exactly the three terms of Theorem 7, including the exponent 1 + 2/δ. -/
def regretBound (δ b h q : ℝ) (T : ℕ) : ℝ :=
  max b h * (1 / Real.rpow (T : ℝ) ((1 / 2 : ℝ) - δ) +
    1 / Real.rpow (T : ℝ) (1 / 2 : ℝ) + Real.rpow q (1 + 2 / δ) / (T : ℝ))

end AIMInventoryAudit.UnknownBound


