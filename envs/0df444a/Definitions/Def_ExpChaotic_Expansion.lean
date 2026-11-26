-- Prove2me | Definitions.Def_ExpChaotic_Expansion
-- name    : ExpChaotic_Expansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:58:10.435463+00:00
-- url     : https://prove2.me/theorems/1525cb58-dc38-518e-aae3-3e0f7711cec2
-- title:
--   Expansion
-- statement:
--   Definitions and structural lemmas for Expansion, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Expansion.lean

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
end
end ExponentialJuliaSetMisiurewicz


