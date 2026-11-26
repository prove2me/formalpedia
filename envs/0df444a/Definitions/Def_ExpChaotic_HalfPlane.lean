-- Prove2me | Definitions.Def_ExpChaotic_HalfPlane
-- name    : ExpChaotic_HalfPlane
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:58:48.320491+00:00
-- url     : https://prove2.me/theorems/f654fbcd-a24a-5120-93b8-54327aaf60fb
-- title:
--   Half Plane
-- statement:
--   Definitions and structural lemmas for Half Plane, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
end
end ExponentialJuliaSetMisiurewicz


