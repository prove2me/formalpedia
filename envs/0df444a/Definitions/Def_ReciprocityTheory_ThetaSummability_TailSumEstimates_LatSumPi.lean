-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaSummability_TailSumEstimates_LatSumPi
-- name    : ReciprocityTheory_ThetaSummability_TailSumEstimates_LatSumPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:56.191644+00:00
-- url     : https://prove2.me/theorems/e6ea2336-0971-42e5-bae7-93545cd10210
-- title:
--   Lat Sum Pi
-- statement:
--   Definitions and structural lemmas for Lat Sum Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/TailSumEstimates/LatSumPi.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ThetaSummability.Est
open Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
end ReciprocityTheory.ThetaSummability.Est


