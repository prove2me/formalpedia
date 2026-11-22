-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:01.181924+00:00
-- url     : https://prove2.me/theorems/2e49a051-4f19-4a03-bf66-a9fb3b00558e
-- title:
--   Rule Inv
-- statement:
--   Definitions and structural lemmas for Rule Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
end Formalism.FourierDecayAlt.R.PInv


