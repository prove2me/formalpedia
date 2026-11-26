-- Prove2me | Definitions.Def_QuarterSumLadder_Basic
-- name    : QuarterSumLadder_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:52:26.460033+00:00
-- url     : https://prove2.me/theorems/0d153ad6-00c4-4fba-891d-fce9631c77b2
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Basic.lean

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuarterSumLadder
def gi : GaussianInt := ⟨0, 1⟩
variable {p : ℕ} [hp : Fact p.Prime]
section Quartic
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
end Quartic
section Squares
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
end Squares
end QuarterSumLadder


