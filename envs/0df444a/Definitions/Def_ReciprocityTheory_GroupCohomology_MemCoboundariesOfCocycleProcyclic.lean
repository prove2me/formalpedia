-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_MemCoboundariesOfCocycleProcyclic
-- name    : ReciprocityTheory_GroupCohomology_MemCoboundariesOfCocycleProcyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:15.617831+00:00
-- url     : https://prove2.me/theorems/50b1da6b-6aef-40bc-8e91-87690d193323
-- title:
--   Mem Coboundaries Of Cocycle Procyclic
-- statement:
--   Definitions and structural lemmas for Mem Coboundaries Of Cocycle Procyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/MemCoboundariesOfCocycleProcyclic.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
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
open ReciprocityTheory.Gal Topology Function
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def tr (M : TRep R G) (f : G × G → M.V) (s : G) : ℕ → M.V
  | 0 => f (1, 1)
  | j + 1 => tr M f s j - f (s ^ j, s)
end ProcyclicCohomology
end ReciprocityTheory.Coh
namespace ReciprocityTheory.Coh
namespace ProcyclicCohomology
open ReciprocityTheory.Gal Topology Function
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end ProcyclicCohomology
end ReciprocityTheory.Coh


