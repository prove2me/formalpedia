-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanD
-- name    : ReciprocityTheory_SemistableReduction_TorusMeanD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:31.750002+00:00
-- url     : https://prove2.me/theorems/807f0981-6569-4f47-99e9-396c1d56f77b
-- title:
--   Torus Mean D
-- statement:
--   Definitions and structural lemmas for Torus Mean D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanD.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end ReciprocityTheory.MultiplicativeHeights


