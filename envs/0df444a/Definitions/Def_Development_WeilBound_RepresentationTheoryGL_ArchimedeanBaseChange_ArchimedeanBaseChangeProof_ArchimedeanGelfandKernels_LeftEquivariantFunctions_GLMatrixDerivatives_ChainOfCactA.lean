-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:26.561371+00:00
-- url     : https://prove2.me/theorems/2d9b57d7-fc28-4663-aaba-71021c688df7
-- title:
--   Chain Of Cact A
-- statement:
--   Definitions and structural lemmas for Chain Of Cact A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ArchimedeanGelfandKernels/LeftEquivariantFunctions/GLMatrixDerivatives/ChainOfCactA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact
variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
def LocSupp {W : Type} [Zero W] (O : Set H) (ι : Γ → Z) (Φ : H × Z → W) : Prop :=
  ∀ x₀ ∈ O, ∃ U : Set H, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
    ∃ K : Set Γ, IsCompact K ∧ ∀ x ∈ U, ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0
def pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : H × Z → W) (p : H × Z) : H →L[ℝ] W :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ H Z)
variable {O : Set H} {OZ : Set Z}
section Int
variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}
end Int
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact


