-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_PGroupFree
-- name    : GroundTheory_TateCohomology_PGroupFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:09.300123+00:00
-- url     : https://prove2.me/theorems/980bb732-791b-4ba1-83da-18bb1241573c
-- title:
--   PGroup Free
-- statement:
--   Definitions and structural lemmas for PGroup Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFree.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
section Naturality
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (f : A ⟶ B)
end Naturality
section Chains
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}
end Chains
section PGroup
variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
end PGroup
end GroundTheory.GroupCoh


