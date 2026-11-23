-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:49.901628+00:00
-- url     : https://prove2.me/theorems/b0ddfb90-2a2e-4c1d-a72d-c2675a0abe35
-- title:
--   Linear Independent Real Of Int Of Discrete
-- statement:
--   Definitions and structural lemmas for Linear Independent Real Of Int Of Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
namespace GlobalTheory
section Gram
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]
end Gram
section Covolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
variable [MeasurableSpace E] [BorelSpace E]
end Covolume
end GlobalTheory


