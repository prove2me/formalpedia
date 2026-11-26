-- Prove2me | Definitions.Def_MellinDuality_Basic
-- name    : MellinDuality_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:42:19.925827+00:00
-- url     : https://prove2.me/theorems/53ec3615-a29a-47f0-a1e4-e037e15b052a
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Basic.lean

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
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
end MellinDuality


