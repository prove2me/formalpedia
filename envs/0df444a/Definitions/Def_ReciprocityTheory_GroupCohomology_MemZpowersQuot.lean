-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
-- name    : ReciprocityTheory_GroupCohomology_MemZpowersQuot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:42.776054+00:00
-- url     : https://prove2.me/theorems/818f7e80-17c9-497d-b612-09c2ac669214
-- title:
--   Mem Zpowers Quot
-- statement:
--   Definitions and structural lemmas for Mem Zpowers Quot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemZpowersQuot.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
namespace ProcyclicCohomology
open Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {s : G}
section Desc
variable {X : Type*} (n : ℕ) (T : ℕ → X)
end Desc
noncomputable def desc (W : Subgroup G) (h : ∀ g : G, ∃ j : ℕ, g⁻¹ * s ^ j ∈ W) {X : Type*}
    (T : ℕ → X) (g : G) : X :=
  T (Classical.choose (h g))
end ProcyclicCohomology
end ReciprocityTheory.Coh


