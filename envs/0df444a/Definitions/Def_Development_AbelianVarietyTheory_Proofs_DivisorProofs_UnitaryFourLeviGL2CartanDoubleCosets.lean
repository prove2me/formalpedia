-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:01.854744+00:00
-- url     : https://prove2.me/theorems/0931ab86-f6e9-4207-bef3-35d555df44a6
-- title:
--   Unitary Four Levi GL2 Cartan Double Cosets
-- statement:
--   Definitions and structural lemmas for Unitary Four Levi GL2 Cartan Double Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryFourLeviGL2CartanDoubleCosets.lean

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
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl.Four
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
def unitaryFourUpperLeftBlock (g : GU σ 4) : Matrix (Fin 2) (Fin 2) L := !![mat g 0 0, mat g 0 1; mat g 1 0, mat g 1 1]
end GlobalTheory.SatakeWeyl.Four
end


