-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:22.976455+00:00
-- url     : https://prove2.me/theorems/901756e3-dfc8-426b-a6c0-e1adab33ae30
-- title:
--   Set Integral Pow Eq Zero Of Pos Freq Euclidean
-- statement:
--   Definitions and structural lemmas for Set Integral Pow Eq Zero Of Pos Freq Euclidean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SetIntegralPowEqZeroOfPosFreqEuclidean.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummablePiProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Real FourierTransform Pointwise
namespace GlobalTheory
section Products
variable {ι : Type*} [Fintype ι] {J : ι → Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
end Products
section Banach
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {R : Type*} [NormedCommRing R] [NormedAlgebra 𝕜 R]
  [CompleteSpace R] {J : Type*}
end Banach
section Characters
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] {μ : Measure G}
  [μ.IsAddLeftInvariant] {L : AddSubgroup G} [Countable L] {D : Set G}
end Characters
section Lattice
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {D : Set E}
end Lattice
section Orthant
end Orthant
end GlobalTheory


