-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:22.965802+00:00
-- url     : https://prove2.me/theorems/e33a3184-ba18-4d84-b6f2-777d3297188f
-- title:
--   Window Mean AP
-- statement:
--   Definitions and structural lemmas for Window Mean AP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WindowMeanAP.lean

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
namespace ProgressionMeanBounds
open Finset Polynomial
end ProgressionMeanBounds
open Finset Polynomial ProgressionMeanBounds
end Formalism.GM


