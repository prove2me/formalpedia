-- Prove2me | Definitions.Def_BandParity_Basic
-- name    : BandParity_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:51:03.917915+00:00
-- url     : https://prove2.me/theorems/60c5dc31-6ce5-40ee-bca0-2172466210a9
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
def gi : GaussianInt := ⟨0, 1⟩
variable {p : ℕ} [hp : Fact p.Prime]
section Quartic
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
end Quartic
end BandParity


