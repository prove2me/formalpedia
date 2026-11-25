-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
-- name    : GroundTheory_HeightsAndTheta_Heights_CovolumeCount
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:04.756897+00:00
-- url     : https://prove2.me/theorems/e4812c19-e18a-596c-9cf8-37a69ebe5a66
-- title:
--   Covolume Count
-- statement:
--   Definitions and structural lemmas for Covolume Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeCount.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module ZSpan NumberField
noncomputable section
section Euclidean
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]
variable [IsZLattice ℝ L]
end Euclidean
section Bundle
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)
end Bundle
end
end GroundTheory.Heights₂.Heights


