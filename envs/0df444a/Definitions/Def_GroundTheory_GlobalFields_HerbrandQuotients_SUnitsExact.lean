-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:26.653794+00:00
-- url     : https://prove2.me/theorems/e2cbd010-86ef-4704-86c3-06bd81b27c8d
-- title:
--   SUnits Exact
-- statement:
--   Definitions and structural lemmas for SUnits Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsExact.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
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
open GroundTheory.GroupCoh
variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]
end GroundTheory.Global


