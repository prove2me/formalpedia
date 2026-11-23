-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
-- name    : Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:30.589627+00:00
-- url     : https://prove2.me/theorems/8df658d1-c1af-4256-8ebe-cc82fd0c4d0e
-- title:
--   Descent Slope
-- statement:
--   Definitions and structural lemmas for Descent Slope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/DescentSlope.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.ExtensionFiltration
open Formalism.HN
end Formalism.ExtensionFiltration


