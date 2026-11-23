-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
-- name    : GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:02.16568+00:00
-- url     : https://prove2.me/theorems/04de3be7-9511-4f21-8d6c-fdd98c3aa9c8
-- title:
--   Index Product Formula
-- statement:
--   Definitions and structural lemmas for Index Product Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IndexProductFormula.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
end GroundTheory.Global


