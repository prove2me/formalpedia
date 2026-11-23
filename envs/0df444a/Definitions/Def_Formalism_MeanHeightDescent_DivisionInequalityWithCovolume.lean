-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
-- name    : Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:19.594802+00:00
-- url     : https://prove2.me/theorems/cdb07bac-6d77-41c3-b127-a7077c21d044
-- title:
--   Division Inequality With Covolume
-- statement:
--   Definitions and structural lemmas for Division Inequality With Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/DivisionInequalityWithCovolume.lean

import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_Assembly
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementJ
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CombinedAverageDegreeBoundOf
import Definitions.Def_Formalism_MeanHeightDescent_FlatDefect
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SumComponents
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.ExtensionFiltration
end Formalism.ExtensionFiltration


