-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTraceHermNondegenerate
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTraceHermNondegenerate
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:01:14.010918+00:00
-- url     : https://prove2.me/theorems/e81f3976-6ac0-40d4-b2d7-3d94cad23458
-- title:
--   PTrace Herm Nondegenerate
-- statement:
--   Definitions and structural lemmas for PTrace Herm Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTraceHermNondegenerate.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StTraceHermNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
end GroundTheory.Heights₂.Heights.FiniteCovolume


