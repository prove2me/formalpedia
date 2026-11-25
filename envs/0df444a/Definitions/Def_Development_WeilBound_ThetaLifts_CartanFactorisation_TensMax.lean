-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
-- name    : Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:06.566124+00:00
-- url     : https://prove2.me/theorems/d84cbd68-3dc5-4b3b-850e-fe378464f084
-- title:
--   Tens Max
-- statement:
--   Definitions and structural lemmas for Tens Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/TensMax.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
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
namespace PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
end PositivityTheory.ThKF.Unit
end


