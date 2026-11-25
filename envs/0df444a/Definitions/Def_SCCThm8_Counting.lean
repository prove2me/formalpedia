-- Prove2me | Definitions.Def_SCCThm8_Counting
-- name    : SCCThm8_Counting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:46:33.220815+00:00
-- url     : https://prove2.me/theorems/22f9cb8e-3026-56c9-a061-7b3ac1ffd42b
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from Eyali1001 (Eyali1001/scc-group-barrier; see pinned Apache-2.0 LICENSE and README.md)'s pinned Group constructions cannot refute the Set Cover Conjecture, including tensor powers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Counting.lean

module
public import Definitions.Def_SCCThm8_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SCCThm8
open Finset
def cntRank {n : ℕ} (v : Finset (Fin n)) (i : Fin n) : ℕ := (v.filter (· < i)).card
def cntLift {n : ℕ} (v : Finset (Fin n)) (i : Fin n) : ℤ :=
  if i ∈ v then (if 2 * cntRank v i < v.card then 1 else -1) else 0
end SCCThm8


