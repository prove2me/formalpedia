-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_GL2BumpFunctions_Parametrix
-- name    : GroundTheory_AutomorphicForms_MultiplicityOne_GL2BumpFunctions_Parametrix
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:24.093651+00:00
-- url     : https://prove2.me/theorems/18fd0174-cebb-4df4-9f31-51149bd3e1ca
-- title:
--   Parametrix
-- statement:
--   Definitions and structural lemmas for Parametrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/GL2BumpFunctions/Parametrix.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace GroundTheory.Automorphic
noncomputable section
namespace Parametrix
variable (χ : ContDiffBump (0 : ℝ))
def kernel : Fin 3 → ℝ → ℝ :=
  ![fun t => max t 0 * deriv (deriv χ) t, fun t => 2 * max t 0 * deriv χ t, fun t => max t 0 * χ t]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
end Parametrix
end
end GroundTheory.Automorphic


