-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
-- name    : Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:13.1478+00:00
-- url     : https://prove2.me/theorems/84f49442-27b9-402f-8b40-5e661842fbf4
-- title:
--   Mfact Mul Coeff Mv Exp Lin F
-- statement:
--   Definitions and structural lemmas for Mfact Mul Coeff Mv Exp Lin F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MfactMulCoeffMvExpLinF.lean

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
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
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
section ExpLin
variable {K : Type} [Field K] {τ : Type} [Fintype τ]
def linF (lam : τ → K) : MvPowerSeries τ K := ∑ w, lam w • (X w : MvPowerSeries τ K)
variable [CharZero K]
end ExpLin
section Rename
variable {K : Type} [Field K] {σ τ : Type}
end Rename
end Formalism.L2.FormalSeriesBounds


