-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
-- name    : ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:29.179891+00:00
-- url     : https://prove2.me/theorems/0326f0fc-afa5-402a-9dd9-4dbdb4c755df
-- title:
--   Wedge Ne Zero Of Linear Independent
-- statement:
--   Definitions and structural lemmas for Wedge Ne Zero Of Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WedgeNeZeroOfLinearIndependent.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
namespace ReciprocityTheory.PGsh
attribute [local instance] extModR
section Wedge
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
end Wedge
end ReciprocityTheory.PGsh


