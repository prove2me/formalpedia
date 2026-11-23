-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_RestrictHopfOrderLength
-- name    : ReciprocityTheory_DualLattices_RestrictHopfOrderLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:28.829663+00:00
-- url     : https://prove2.me/theorems/96b2f6a1-6d9c-4405-943b-25c11c5bf5f5
-- title:
--   Restrict Hopf Order Length
-- statement:
--   Definitions and structural lemmas for Restrict Hopf Order Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RestrictHopfOrderLength.lean

import Definitions.Def_ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder
end ReciprocityTheory.PGsh.Up


