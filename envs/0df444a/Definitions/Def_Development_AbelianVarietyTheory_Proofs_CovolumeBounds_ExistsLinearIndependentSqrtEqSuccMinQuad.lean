-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:44.854206+00:00
-- url     : https://prove2.me/theorems/5dae07fe-9326-457f-b009-9dd75f25e7db
-- title:
--   Exists Linear Independent Sqrt Eq Succ Min Quad
-- statement:
--   Definitions and structural lemmas for Exists Linear Independent Sqrt Eq Succ Min Quad, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsLinearIndependentSqrtEqSuccMinQuad.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
namespace GlobalTheory
section General
variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}
end General
section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}
variable [FiniteDimensional ℝ E] [DiscreteTopology L]
variable (L) [IsZLattice ℝ L]
end Normed
section Quadratic
variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V} {L : Submodule ℤ V}
  {n : ℕ}
end Quadratic
end GlobalTheory


