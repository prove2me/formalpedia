-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
-- name    : Formalism_GaussJetBounds_GaussJetProofs_Transfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:31.600283+00:00
-- url     : https://prove2.me/theorems/90a1ec3e-ba9b-4cd0-add3-640ef6a2fd22
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Transfer.lean

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
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
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
namespace Transfer
section Maps
variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}
variable [NeZero d]
end Maps
section Normed
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
end Normed
end Transfer
end Formalism.DworkPowerSeriesWeights


