-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_Imports
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:57.108711+00:00
-- url     : https://prove2.me/theorems/7b3fbbb6-8328-416f-b255-c97ce98ca5dd
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Theta
namespace FibreMeasure
open MeasureTheory
section Shear
variable {G P : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [AddCommGroup P] [MeasurableSpace P] [MeasurableAdd₂ P] [MeasurableNeg P]
end Shear
end FibreMeasure
end GroundTheory.Heights₂.Theta


