-- Prove2me | Definitions.Def_QuadraticFloor_Monic
-- name    : QuadraticFloor_Monic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:46:15.113336+00:00
-- url     : https://prove2.me/theorems/d08285f1-5b02-55a8-b918-5399665ee174
-- title:
--   Monic
-- statement:
--   Definitions and structural lemmas for Monic, from J. S. Farland (jkfarland-bot/QuadraticFloor; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuadraticFloor: quadratic floor sums and the trace of a quartic Bernoulli number development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean

module
public import Definitions.Def_QuadraticFloor_Corollaries
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
def Fodd (p : ℕ) (c : ℤ) : ℤ := floorSum 1 1 c p
end QuadraticFloor


