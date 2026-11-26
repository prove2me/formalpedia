-- Prove2me | Definitions.Def_ExpChaotic_Covering
-- name    : ExpChaotic_Covering
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:59:41.278848+00:00
-- url     : https://prove2.me/theorems/9babb9d5-1aca-5251-9b69-f2a2954a7e84
-- title:
--   Covering
-- statement:
--   Definitions and structural lemmas for Covering, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Covering.lean

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
end
end ExponentialJuliaSetMisiurewicz


