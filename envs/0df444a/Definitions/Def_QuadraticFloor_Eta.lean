-- Prove2me | Definitions.Def_QuadraticFloor_Eta
-- name    : QuadraticFloor_Eta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:43:35.203963+00:00
-- url     : https://prove2.me/theorems/da528204-d632-5340-aedd-a046c8b55652
-- title:
--   Eta
-- statement:
--   Definitions and structural lemmas for Eta, from J. S. Farland (jkfarland-bot/QuadraticFloor; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuadraticFloor: quadratic floor sums and the trace of a quartic Bernoulli number development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Eta.lean

module
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuadraticFloor
open Finset
def kap (p : ℕ) : MulChar (ZMod 8) ℤ := if p % 4 = 1 then ZMod.χ₈' else ZMod.χ₈
variable {p : ℕ} [hp : Fact p.Prime]
end QuadraticFloor


