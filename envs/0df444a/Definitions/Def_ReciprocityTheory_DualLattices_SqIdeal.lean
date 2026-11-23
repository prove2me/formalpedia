-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
-- name    : ReciprocityTheory_DualLattices_SqIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:06.558812+00:00
-- url     : https://prove2.me/theorems/7227789c-f46c-42d0-8d78-7307c17f3f41
-- title:
--   Sq Ideal
-- statement:
--   Definitions and structural lemmas for Sq Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SqIdeal.lean

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsAlt
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
import Definitions.Def_ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.U3
end ReciprocityTheory.PGsh.Up


