-- Prove2me | Definitions.Def_QuarterSumLadder_Ladder
-- name    : QuarterSumLadder_Ladder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:08:59.773398+00:00
-- url     : https://prove2.me/theorems/065172cd-60ff-41cb-bd29-661c0bbb9ad4
-- title:
--   Ladder
-- statement:
--   Definitions and structural lemmas for Ladder, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
section Quartic
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
end Quartic
end QuarterSumLadder


