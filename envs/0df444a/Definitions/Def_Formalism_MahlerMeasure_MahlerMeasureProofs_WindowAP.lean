-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:43.309829+00:00
-- url     : https://prove2.me/theorems/e9cb0a24-b152-491b-bb49-0f046d99889e
-- title:
--   Window AP
-- statement:
--   Definitions and structural lemmas for Window AP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowAP.lean

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Finset
namespace ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
end ArithmeticProgressionDivisibility
open ArithmeticProgressionDivisibility
end Formalism.GM


