-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:10.109979+00:00
-- url     : https://prove2.me/theorems/2c898ced-f835-4a3d-9f17-4c1bd4364af1
-- title:
--   Tens Spans
-- statement:
--   Definitions and structural lemmas for Tens Spans, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorSpanning/TensSpans.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)
end PI.KerTens.W


