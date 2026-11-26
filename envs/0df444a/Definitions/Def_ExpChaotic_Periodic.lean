-- Prove2me | Definitions.Def_ExpChaotic_Periodic
-- name    : ExpChaotic_Periodic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:00:08.723313+00:00
-- url     : https://prove2.me/theorems/d3c8c17a-861f-4e08-a9bd-a6bbaa901cd9
-- title:
--   Periodic
-- statement:
--   Definitions and structural lemmas for Periodic, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Periodic.lean

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
abbrev logIterate (n : ℕ) : ℂ → ℂ := Complex.log^[n]
end
end ExponentialJuliaSetMisiurewicz


