-- Prove2me | Definitions.Def_SCCThm8_Numeric
-- name    : SCCThm8_Numeric
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:43:20.484426+00:00
-- url     : https://prove2.me/theorems/ab373cd5-a1c0-4f1c-90f1-5ff1c7236c49
-- title:
--   Numeric
-- statement:
--   Definitions and structural lemmas for Numeric, from Eyali1001 (Eyali1001/scc-group-barrier; see pinned Apache-2.0 LICENSE and README.md)'s pinned Group constructions cannot refute the Set Cover Conjecture, including tensor powers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SCCThm8
noncomputable def tau (k : ℕ) : ℚ :=
  (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k
def trin (k : ℕ) : ℕ := Nat.choose (3 * k) k * Nat.choose (2 * k) k
def cen (k : ℕ) : ℕ := Nat.choose (3 * k) (3 * k / 2)
end SCCThm8


