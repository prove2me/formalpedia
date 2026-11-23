-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SumLatInvMulVec
-- name    : ReciprocityTheory_DualLattices_SumLatInvMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:32.572044+00:00
-- url     : https://prove2.me/theorems/36edd1b4-d3fd-4219-a958-f48db473dfe7
-- title:
--   Sum Lat Inv Mul Vec
-- statement:
--   Definitions and structural lemmas for Sum Lat Inv Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SumLatInvMulVec.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor
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
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
def phiMap {n s h : ℕ} (A : Fin n → Matrix (Fin s) (Fin h) C) (w : Fin n × Fin h → C) :
    Fin n × Fin s → C := fun y => ∑ l, A y.1 y.2 l * w (y.1, l)
end ReciprocityTheory.PGsh.Up


