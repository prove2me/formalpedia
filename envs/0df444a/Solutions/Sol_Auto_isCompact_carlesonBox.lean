-- Prove2me | solution 1 for Auto.isCompact_carlesonBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:00:17.736406+00:00
-- url     : https://prove2.me/submissions/9bc3fe39-3f73-4b86-94b8-ab49021a833a

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (L : ℝ) : IsCompact (carlesonBox L) := isCompact_Icc.prod isCompact_Icc
end Auto
