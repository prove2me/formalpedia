-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_FrobeniusBlock
-- name    : ReciprocityTheory_DualLattices_FrobeniusBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:35.350072+00:00
-- url     : https://prove2.me/theorems/e6edb552-7f73-4e55-bafe-a951a9a1a99d
-- title:
--   Frobenius Block
-- statement:
--   Definitions and structural lemmas for Frobenius Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FrobeniusBlock.lean

import Definitions.Def_ReciprocityTheory_DualLattices_FormMonomialUnitVector
import Definitions.Def_ReciprocityTheory_DualLattices_FrobEqOfLe
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
open ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix ReciprocityTheory.PGsh.Up.UnitVectorPowers
end ReciprocityTheory.PGsh.Up


