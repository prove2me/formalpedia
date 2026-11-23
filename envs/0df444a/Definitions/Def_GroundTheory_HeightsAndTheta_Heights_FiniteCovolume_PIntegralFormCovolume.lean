-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIntegralFormCovolume
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIntegralFormCovolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:17.136323+00:00
-- url     : https://prove2.me/theorems/a7a99fa0-9d29-4297-9c2a-e12df45e65c0
-- title:
--   PIntegral Form Covolume
-- statement:
--   Definitions and structural lemmas for PIntegral Form Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIntegralFormCovolume.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StIntegralFormCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory Matrix
noncomputable section
variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


