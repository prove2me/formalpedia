-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P33
-- name    : QAlgorithms_Papers_Independent_Support50_P33
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T21:31:25.002201+00:00
-- url     : https://prove2.me/theorems/a281ff6b-4f3c-4c39-befc-df86ffc71598
-- title:
--   Definitions for Characterization of convex $μ$-compact sets
-- statement:
--   The objects the formalized statements of *Characterization of convex $μ$-compact sets* (arXiv:1004.3792) are stated in. Each was checked against the paper by a blind read-back and a moderator.
-- source:
--   Characterization of convex $μ$-compact sets, arXiv:1004.3792v1, https://arxiv.org/abs/1004.3792v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

/-!
# Characterization of convex µ-compact sets

M. E. Shirokov, arXiv:1004.3792v1, PDF pp.1–6.
The accepted locally convex Pettis-barycenter and envelope definitions are
reused from Frontier18.P10, and extended convexity from Dependency50.P25.
For convex A, GeneralBarycenterSpace A describes exactly the standing class:
closed, von Neumann bounded, complete and separable in the induced additive
uniformity, and metrizable. Completeness in the Hausdorff ambient uniform
space implies closedness; hence closedConvexHull ℝ A = A here.
All regularity, convergence and envelope comparisons are relative to A.
No nonemptiness, normability, or common bound on all sequence terms is added.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P33

open QAlgorithms.Papers.Independent.Frontier18.P10
open QAlgorithms.Papers.Independent.Dependency50.P25

/-- PDF p.1: measures use the Borel sigma algebra of their relative domain. -/
local instance paperMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  borel X

/-- PDF p.1: the chosen sigma algebra is exactly the Borel sigma algebra. -/
local instance paperBorel (X : Type*) [TopologicalSpace X] : BorelSpace X :=
  ⟨rfl⟩

example (X : Type*) [TopologicalSpace X] :
    (inferInstance : MeasurableSpace X) = borel X := by
  rfl

example (X : Type*) [TopologicalSpace X] : BorelSpace X := by
  exact ⟨rfl⟩

section LocallyConvexResults

variable {E : Type*} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

end LocallyConvexResults

end QAlgorithms.Papers.Independent.Support50.P33


