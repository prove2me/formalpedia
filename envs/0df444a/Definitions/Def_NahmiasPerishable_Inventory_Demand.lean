-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Demand
-- name    : NahmiasPerishable_Inventory_Demand
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:23:07.244985+00:00
-- url     : https://prove2.me/theorems/3bb10ca4-0e04-46da-8105-17467d38db80
-- title:
--   Perishable inventory: Demand
-- statement:
--   Nonnegative demand with a Lebesgue density, its CDF, the lower extended-real quantile, iid product laws, and signed expected costs. The pure published newsvendor integral is used only on its integrable domain; otherwise its nonnegative extended expectation is used.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 683–686, DOI:10.1287/opre.30.4.680.

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
noncomputable section

namespace NahmiasPerishable.Inventory
attribute [local instance] Classical.propDecidable

/-- Nonnegative demand with a Lebesgue density, pp. 683–686. No support or positivity restriction. -/
structure Demand where
  law : Measure ℝ
  prob : IsProbabilityMeasure law
  nonneg : ∀ᵐ d ∂law, 0 ≤ d
  density : ℝ → ℝ≥0∞
  measurable_density : Measurable density
  law_density : law = volume.withDensity density

attribute [instance] Demand.prob

def cdf (μ : Measure ℝ) (z : ℝ) : ℝ := (μ (Iic z)).toReal

def pos (z : ℝ) : ℝ := max z 0

/-- Lower quantile in the complete extended real line. Empty set gives +∞; unbounded below gives −∞. -/
def lowerQuantile (μ : Measure ℝ) (u : ℝ) : EReal :=
  sInf ((fun z : ℝ => (z : EReal)) '' {z | u ≤ cdf μ z})

/-- Signed extended expectation; the two infinite parts are not assigned a finite default. -/
def expectation {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → EReal) : EReal :=
  (∫⁻ x, (f x).toENNReal ∂μ).toEReal - (∫⁻ x, (-f x).toENNReal ∂μ).toEReal

/-- Well-definedness of a signed expected cost, excluding only the undefined ∞−∞ case. -/
def ExpectationDefined {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → EReal) : Prop :=
  AEMeasurable f μ ∧
  ((∫⁻ x, (f x).toENNReal ∂μ) ≠ ⊤ ∨ (∫⁻ x, (-f x).toENNReal ∂μ) ≠ ⊤)

/-- Extended holding/shortage cost; the published pure integral is used on its integrable domain. -/
def stockCost (μ : Measure ℝ) (h p z : ℝ) : EReal :=
  if Integrable (fun d => h * pos (z-d) + p * pos (d-z)) μ then
    (ZhengQR.OrderQty.newsvendorCost h p μ z : EReal)
  else (∫⁻ d, ENNReal.ofReal (h * pos (z-d) + p * pos (d-z)) ∂μ).toEReal

/-- Independent finite demand paths. -/
def demandPaths (μ : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => μ)

end NahmiasPerishable.Inventory


