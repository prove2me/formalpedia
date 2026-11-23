-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:22.174198+00:00
-- url     : https://prove2.me/theorems/5137f9b9-a142-4685-9ebb-f3ea3eb0ae42
-- title:
--   Lattice Bridge
-- statement:
--   Definitions and structural lemmas for Lattice Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/LatticeBridge.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
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
open MulAction
open scoped TensorProduct
variable {G : Type*} [Group G] [Fintype G]
end GroundTheory.Global


