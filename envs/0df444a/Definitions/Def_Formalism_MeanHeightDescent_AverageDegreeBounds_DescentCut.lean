-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentCut
-- name    : Formalism_MeanHeightDescent_AverageDegreeBounds_DescentCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:09.861703+00:00
-- url     : https://prove2.me/theorems/62f90736-9a6f-4eb8-9a6a-37aeb23025a9
-- title:
--   Descent Cut
-- statement:
--   Definitions and structural lemmas for Descent Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/DescentCut.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DescentCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
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


