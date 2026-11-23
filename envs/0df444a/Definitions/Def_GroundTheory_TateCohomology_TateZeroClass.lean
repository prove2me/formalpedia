-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
-- name    : GroundTheory_TateCohomology_TateZeroClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:09.628833+00:00
-- url     : https://prove2.me/theorems/7de43614-9edf-4d2a-93df-c595993c4ab4
-- title:
--   Tate Zero Class
-- statement:
--   Definitions and structural lemmas for Tate Zero Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateZeroClass.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
noncomputable def tateZeroClass (M : Rep.{u} k G) : M.ρ.invariants →ₗ[k] tateCohomology M 0 :=
  ((tateCohomologyZeroIso k G).app M).inv.hom ∘ₗ (normRangeInvariants M).mkQ
end GroundTheory.GroupCoh


