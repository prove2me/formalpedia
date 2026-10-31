-- Prove2me | Definitions.Def_MinBuying_Model
-- name    : MinBuying_Model
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T16:12:59.669505+00:00
-- url     : https://prove2.me/theorems/e00b6d05-1d0c-4be0-9555-e71667b9e65b
-- title:
--   Min-buying payments and pricing objectives
-- statement:
--   Defines the payment as the least price among affordable products, with zero payment when none is affordable. Feasible price vectors have nonnegative coordinates. Revenue is the expected payment under a joint law. Defines all-price differentiated and uniform suprema, nonnegative probability laws, product and IID laws, and the source's finite attained positive-optimum conditions. Strict rejection is $\Pr(V<p)$; the right CDF is $\Pr(V\le p)$. No first-moment assumption is imposed.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . Section 2, pp.7–9, Eqs.(1)–(5).

import Mathlib

/-! Unit-demand min-buying payments and the source's optimization conventions.
No first-moment hypothesis is imposed on valuations. Every fixed feasible
price vector has a bounded, measurable payment function. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace MinBuying

abbrev Valuations (n : ℕ) := Fin n → ℝ
abbrev Prices (n : ℕ) := Fin n → ℝ
abbrev JointLaw (n : ℕ) := Measure (Valuations n)

def FeasiblePrices {n : ℕ} (p : Prices n) : Prop := ∀ i, 0 ≤ p i

/-- Inclusive affordability; equally priced purchases give the same payment. -/
def affordable {n : ℕ} (p : Prices n) (v : Valuations n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≤ v i)

def payment {n : ℕ} (p : Prices n) (v : Valuations n) : ℝ :=
  if h : (affordable p v).Nonempty then (affordable p v).inf' h p else 0

def Revenue {n : ℕ} (μ : JointLaw n) (p : Prices n) : ℝ :=
  ∫ v, payment p v ∂μ

def uniformRevenue {n : ℕ} (μ : JointLaw n) (p : ℝ) : ℝ :=
  Revenue μ (fun _ => p)

def differentiatedValues {n : ℕ} (μ : JointLaw n) : Set ℝ :=
  {r | ∃ p : Prices n, FeasiblePrices p ∧ r = Revenue μ p}

def uniformValues {n : ℕ} (μ : JointLaw n) : Set ℝ :=
  {r | ∃ p : ℝ, 0 ≤ p ∧ r = uniformRevenue μ p}

def DPRevenue {n : ℕ} (μ : JointLaw n) : ℝ := sSup (differentiatedValues μ)
def UPRevenue {n : ℕ} (μ : JointLaw n) : ℝ := sSup (uniformValues μ)

def ValidLaw {n : ℕ} (μ : JointLaw n) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i

def ValidMarginal (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ᵐ x ∂ν, 0 ≤ x

/-- The explicit standing assumptions on p.7: finite attained optima and
strictly positive optimal uniform revenue. Bounds protect the real suprema. -/
def WellPosed {n : ℕ} (μ : JointLaw n) : Prop :=
  BddAbove (differentiatedValues μ) ∧ BddAbove (uniformValues μ) ∧
  (∃ p : Prices n, FeasiblePrices p ∧ Revenue μ p = DPRevenue μ) ∧
  (∃ p : ℝ, 0 ≤ p ∧ uniformRevenue μ p = UPRevenue μ) ∧
  0 < UPRevenue μ

def productLaw {n : ℕ} (F : Fin n → Measure ℝ) : JointLaw n := Measure.pi F

def iidLaw (n : ℕ) (F : Measure ℝ) : JointLaw n := productLaw (fun _ => F)

/-- Strict rejection, deliberately different from the right CDF at atoms. -/
def rejection (F : Measure ℝ) (p : ℝ) : ℝ := (F (Iio p)).toReal

def cdf (F : Measure ℝ) (p : ℝ) : ℝ := (F (Iic p)).toReal

def independentRevenueFormula {n : ℕ} (F : Fin n → Measure ℝ)
    (p : Prices n) : ℝ :=
  ∑ i : Fin n, p i * (1 - rejection (F i) (p i)) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin n => j < i), rejection (F j) (p j)

end MinBuying


