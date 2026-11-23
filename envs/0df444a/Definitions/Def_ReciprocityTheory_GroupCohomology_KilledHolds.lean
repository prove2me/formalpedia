-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_KilledHolds
-- name    : ReciprocityTheory_GroupCohomology_KilledHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:02.396893+00:00
-- url     : https://prove2.me/theorems/603f3801-37b6-4d5b-a46e-e752908f78d0
-- title:
--   Killed Holds
-- statement:
--   Definitions and structural lemmas for Killed Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/KilledHolds.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace KernelCokernelKilling
section KillLES
variable {R : Type u} [CommRing R] {A B C : Cx R} {i : Hom A B} {p : Hom B C}
  {δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)}
end KillLES
section KillRep
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end KillRep
end KernelCokernelKilling
open KernelCokernelKilling
end
end ReciprocityTheory.Coh


