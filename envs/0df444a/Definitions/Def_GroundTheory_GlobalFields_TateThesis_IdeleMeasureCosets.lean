-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
-- name    : GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:50.143282+00:00
-- url     : https://prove2.me/theorems/5cf4e5f1-6b22-5b1a-bf7d-a381ee91c26e
-- title:
--   Idele Measure Cosets
-- statement:
--   Definitions and structural lemmas for Idele Measure Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureCosets.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal
namespace GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
end
end GroundTheory.Global


