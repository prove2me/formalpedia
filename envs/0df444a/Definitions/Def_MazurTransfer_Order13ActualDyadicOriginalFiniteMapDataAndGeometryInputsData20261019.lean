-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFiniteMapDataAndGeometryInputsData20261019
-- name    : MazurTransfer_Order13ActualDyadicOriginalFiniteMapDataAndGeometryInputsData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T07:17:13.100811+00:00
-- url     : https://prove2.me/theorems/11f80123-23f6-407b-a4df-19d989391ce0
-- title:
--   Actual dyadic mixed finite-map data and geometry inputs
-- statement:
--   The literal original dyadic finite-map datum of degree three, its positive powers, all degree bounds and the proper smooth geometrically integral curve inputs over the reduced Noetherian dyadic ring. The original whole chosen values are retained. Named downstream consumer: representation of the actual relative Picard functor.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: ACTUAL original FLT FiniteMapData of degree three and
arbitrarily large degree for the SAME mixed dyadic curve and SAME zero
section, with its checked Picard geometry. Named downstream consumer:
original exact-pin dyadic Picard representation; HasChartSections remains
an independent obligation.
-/
import Definitions.Def_MazurTransfer_Order13MixedOriginalActualFiniteMapDataAndArbitraryDegreePowersData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_relative_dimension_and_picard_geometry

noncomputable section
namespace MazurTransfer.Order13ActualDyadicMixedFiniteMapData
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs
theorem originalDyadicFiniteMapPrimeProvider20261019 : Fact (Nat.Prime 2) := ⟨by decide⟩
attribute [local instance] originalDyadicFiniteMapPrimeProvider20261019

def dyadicFiniteMapData : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection :=
  Order13MixedSingleSectionActualFiniteMapData.actualFiniteMapData BaseRing

theorem dyadicFiniteMapData_degree : dyadicFiniteMapData.m = 3 := rfl

def dyadicPowerFiniteMapData (n : ℕ) (hn : n ≠ 0) :
    SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection :=
  Order13MixedSingleSectionArbitrarilyLargeFiniteMapData.actualPowerFiniteMapData BaseRing n hn

theorem dyadicPowerFiniteMapData_degree (n : ℕ) (hn : n ≠ 0) :
    (dyadicPowerFiniteMapData n hn).m = n * 3 := rfl

theorem exists_dyadic_finiteMapData_degree_ge (m₀ : ℕ) :
    ∃ F : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection, m₀ ≤ F.m :=
  Order13MixedSingleSectionArbitrarilyLargeFiniteMapData.exists_actual_finiteMapData_degree_ge BaseRing m₀

theorem actual_dyadic_picard_geometry_and_finite_map_inputs :
    IsNoetherianRing BaseRing ∧ IsReduced BaseRing ∧ IsProper (curveToBase BaseRing) ∧
    SmoothOfRelativeDimension 1 (curveToBase BaseRing) ∧
    GeometricallyIntegral (curveToBase BaseRing) ∧
    (∀ m₀, ∃ F : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection, m₀ ≤ F.m) := by
  obtain ⟨hN,hR,hP,hD,hG,-⟩ := MazurTransfer.order13_actual_dyadic_relative_dimension_and_picard_geometry.2.2.2.1
  exact ⟨hN,hR,hP,hD,hG,exists_dyadic_finiteMapData_degree_ge⟩

end MazurTransfer.Order13ActualDyadicMixedFiniteMapData
#print axioms MazurTransfer.Order13ActualDyadicMixedFiniteMapData.dyadicFiniteMapData
#print axioms MazurTransfer.Order13ActualDyadicMixedFiniteMapData.exists_dyadic_finiteMapData_degree_ge
#print axioms MazurTransfer.Order13ActualDyadicMixedFiniteMapData.actual_dyadic_picard_geometry_and_finite_map_inputs


