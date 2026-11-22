-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:34.102625+00:00
-- url     : https://prove2.me/theorems/5c3a718b-3f82-4aec-b8f2-e137184e6226
-- title:
--   Level Growth Bounds
-- statement:
--   Definitions and structural lemmas for Level Growth Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelGrowthBounds.lean

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds
open Finset Real
noncomputable def Pp (e : ℕ → ℝ) (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, √(1 + e l)
end Formalism.FourierDecayAlt.P.LevelGrowthBounds
namespace Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds
end Formalism.FourierDecayAlt.P


