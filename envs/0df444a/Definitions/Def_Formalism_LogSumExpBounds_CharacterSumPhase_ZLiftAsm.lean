-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_ZLiftAsm
-- name    : Formalism_LogSumExpBounds_CharacterSumPhase_ZLiftAsm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:36.150057+00:00
-- url     : https://prove2.me/theorems/e1b1de33-d2c6-4764-b8f6-57389b73a284
-- title:
--   ZLift Asm
-- statement:
--   Definitions and structural lemmas for ZLift Asm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/ZLiftAsm.lean

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.P
open Finset
noncomputable def sz {f : ℕ} (x : Fin f → ℝ) (K : ℕ) (z : Fin f → ℂ) (a : ℝ) : ℝ :=
  ∑ A ∈ (univ : Finset (Fin f)).powerset, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * a ^ 2
end Formalism.NuclearRankWeightBounds.P


