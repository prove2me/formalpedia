-- Prove2me | Definitions.Def_RiemannMasullo_ForMathlib_Analysis_LocallyConvex_WithSeminorms
-- name    : RiemannMasullo_ForMathlib_Analysis_LocallyConvex_WithSeminorms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:16:18.641215+00:00
-- url     : https://prove2.me/theorems/eb504499-91be-4ca1-89f0-b2494a35dc32
-- title:
--   With Seminorms
-- statement:
--   Definitions and structural lemmas for With Seminorms, from Ryan McCorvie and RiemannMasullo contributors; manuscript by Alessandro Maria Masullo's pinned Masullo formalization: partial supporting library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/ForMathlib/Analysis/LocallyConvex/WithSeminorms.lean

module
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Topology
namespace RiemannMasullo
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [PolynormableSpace 𝕜 F]
end RiemannMasullo


