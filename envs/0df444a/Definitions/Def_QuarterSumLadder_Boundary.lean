-- Prove2me | Definitions.Def_QuarterSumLadder_Boundary
-- name    : QuarterSumLadder_Boundary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:11:26.816066+00:00
-- url     : https://prove2.me/theorems/0dfb10ad-a0c4-56e2-abc3-a0ffea2166f1
-- title:
--   Boundary
-- statement:
--   Definitions and structural lemmas for Boundary, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean

module
public import Definitions.Def_QuarterSumLadder_Ladder
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
namespace QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime] {χ : MulChar (ZMod p) GaussianInt}
  (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
end QuarterSumLadder


