-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:03:27.671453+00:00
-- url     : https://prove2.me/theorems/7a6d29bf-6f4d-5ba3-94b5-39c83230c670
-- title:
--   Lev Mul Vec Outside
-- statement:
--   Definitions and structural lemmas for Lev Mul Vec Outside, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LevMulVecOutside.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
namespace GlobalTheory.LevelStabiliser
open GlobalTheory.LevelUnitary
variable (k i r' : ℕ)
end GlobalTheory.LevelStabiliser


