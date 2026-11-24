-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:10:10.468651+00:00
-- url     : https://prove2.me/theorems/8e84a988-53eb-467e-8fe6-df7450a99da8
-- title:
--   Unitary Four Levi GL2 Root Index Of Card Sq
-- statement:
--   Definitions and structural lemmas for Unitary Four Levi GL2 Root Index Of Card Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2RootIndexOfCardSq.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG
namespace GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
def rootMat (σ : L →+* L) (x : L) : Matrix (Fin 4) (Fin 4) L :=
  !![1, x, 0, 0; 0, 1, 0, 0; 0, 0, 1, -σ x; 0, 0, 0, 1]
end GlobalTheory.SatakeWeyl.IdxFour
end


