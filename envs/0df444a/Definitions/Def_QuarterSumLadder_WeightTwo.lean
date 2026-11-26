-- Prove2me | Definitions.Def_QuarterSumLadder_WeightTwo
-- name    : QuarterSumLadder_WeightTwo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:07:50.686279+00:00
-- url     : https://prove2.me/theorems/449f2141-f621-48c6-98a4-86cbc80405b2
-- title:
--   Weight Two
-- statement:
--   Definitions and structural lemmas for Weight Two, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean

module
public import Definitions.Def_QuarterSumLadder_Counts
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


