-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
-- name    : Formalism_GaussJetBounds_GaussJetProofs_FJEval
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:52.652623+00:00
-- url     : https://prove2.me/theorems/7df4aaca-1ec9-4ec0-bf78-bb74d36078bf
-- title:
--   FJEval
-- statement:
--   Definitions and structural lemmas for FJEval, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FJEval.lean

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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
open Formalism.IncomingBounds
section Eval
end Eval
section Maps
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]
end Maps
section Change
variable {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
end Change
end Formalism.DworkPowerSeriesWeights


