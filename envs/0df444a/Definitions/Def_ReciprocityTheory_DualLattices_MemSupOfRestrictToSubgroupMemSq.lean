-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
-- name    : ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:28:38.885265+00:00
-- url     : https://prove2.me/theorems/5a4a921e-864e-40bd-bb5d-f76b2d35206e
-- title:
--   Mem Sup Of Restrict To Subgroup Mem Sq
-- statement:
--   Definitions and structural lemmas for Mem Sup Of Restrict To Subgroup Mem Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemSupOfRestrictToSubgroupMemSq.lean

import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
end ReciprocityTheory.PGsh.L2


