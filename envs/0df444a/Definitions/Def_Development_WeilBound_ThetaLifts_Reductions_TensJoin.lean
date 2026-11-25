-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_TensJoin
-- name    : Development_WeilBound_ThetaLifts_Reductions_TensJoin
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:13.524472+00:00
-- url     : https://prove2.me/theorems/da93d996-473c-4662-95b6-31078f409dba
-- title:
--   Tens Join
-- statement:
--   Definitions and structural lemmas for Tens Join, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/TensJoin.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open PiTensorProduct
namespace PositivityTheory.ThKR.Join
open PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
end PositivityTheory.ThKR.Join
end


