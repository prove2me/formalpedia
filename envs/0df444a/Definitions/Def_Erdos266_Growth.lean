-- Prove2me | Definitions.Def_Erdos266_Growth
-- name    : Erdos266_Growth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:39:01.43949+00:00
-- url     : https://prove2.me/theorems/22265268-77d8-42ea-961a-d8618cc840c8
-- title:
--   Growth
-- statement:
--   Definitions and structural lemmas for Growth, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean

module
public import Definitions.Def_Erdos266_Defs
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
open Finset
def bigN (k : ℕ) : ℕ := 2 ^ (k ^ 2)
def bigM (k : ℕ) : ℕ := min (bigN k / (4 * k)) (Nat.sqrt (bigN k))
end Erdos266


