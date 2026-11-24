-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:43.483058+00:00
-- url     : https://prove2.me/theorems/bcf65a0c-708d-45f0-b1cf-3ac5fa8359f8
-- title:
--   XTwo Dvd Of Restrict Third Zero
-- statement:
--   Definitions and structural lemmas for XTwo Dvd Of Restrict Third Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/XTwoDvdOfRestrictThirdZero.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
def sh (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] h
def shI (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] h
end Formalism.L2.Th1.B.Wr


