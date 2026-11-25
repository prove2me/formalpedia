-- Prove2me | Definitions.Def_Erdos684_Lower
-- name    : Erdos684_Lower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:19:37.425974+00:00
-- url     : https://prove2.me/theorems/6b51ace4-a4bb-4345-b11c-075da3865412
-- title:
--   Lower
-- statement:
--   Definitions and structural lemmas for Lower, from AItoBit (AItoBit/erdos-684-elementary-bounds; see pinned Apache-2.0 LICENSE and README.md)'s pinned Elementary upper and lower bounds for Erdos Problem 684 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Lower.lean

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Filter Real
open scoped Topology
namespace Erdos684
def obstructionModulus (K : ℕ) : ℕ := Nat.lcmUpto K * primorial K
end Erdos684


