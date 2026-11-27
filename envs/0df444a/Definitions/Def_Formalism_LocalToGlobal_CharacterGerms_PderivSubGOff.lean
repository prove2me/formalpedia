-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
-- name    : Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T05:26:26.331141+00:00
-- url     : https://prove2.me/theorems/065e472c-b27e-53ad-b79c-d6b440a236b5
-- title:
--   Pderiv Sub GOff
-- statement:
--   Definitions and structural lemmas for Pderiv Sub GOff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
section Chain
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
end Chain
end Formalism.L2.FormalSeriesBounds.RF


