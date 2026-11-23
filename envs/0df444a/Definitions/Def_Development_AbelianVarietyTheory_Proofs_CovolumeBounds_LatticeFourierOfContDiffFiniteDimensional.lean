-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:37.203901+00:00
-- url     : https://prove2.me/theorems/f82e1cda-69ec-4a6c-929c-0ed02a0a4855
-- title:
--   Lattice Fourier Of Cont Diff Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Lattice Fourier Of Cont Diff Finite Dimensional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
namespace GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
def latticeCell (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] : Set E :=
  ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
def latticeFourierCoeff (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : E → V) (ν : E) : V :=
  (ZLattice.covolume L)⁻¹ • ∫ b in latticeCell L, e[-⟪ν, b⟫] • A b
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
end GlobalTheory


