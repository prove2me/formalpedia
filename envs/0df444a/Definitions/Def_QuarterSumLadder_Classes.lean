-- Prove2me | Definitions.Def_QuarterSumLadder_Classes
-- name    : QuarterSumLadder_Classes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:59:04.497876+00:00
-- url     : https://prove2.me/theorems/6bd0b589-f38d-510a-9b2d-3d11385511c0
-- title:
--   Classes
-- statement:
--   Definitions and structural lemmas for Classes, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Classes.lean

module
public import Definitions.Def_QuarterSumLadder_Prelim
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
section Quartic
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
abbrev FourVal (z : GaussianInt) : Prop := z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi
end Quartic
end QuarterSumLadder


