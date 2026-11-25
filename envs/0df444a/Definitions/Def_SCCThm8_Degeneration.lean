-- Prove2me | Definitions.Def_SCCThm8_Degeneration
-- name    : SCCThm8_Degeneration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:48:30.250689+00:00
-- url     : https://prove2.me/theorems/2c864d4b-be52-49bf-8a41-0dd18c411d15
-- title:
--   Degeneration
-- statement:
--   Definitions and structural lemmas for Degeneration, from Eyali1001 (Eyali1001/scc-group-barrier; see pinned Apache-2.0 LICENSE and README.md)'s pinned Group constructions cannot refute the Set Cover Conjecture, including tensor powers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Degeneration.lean

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SCCThm8
open Finset
def ind {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : ℤ := if i ∈ X then 1 else 0
end SCCThm8


