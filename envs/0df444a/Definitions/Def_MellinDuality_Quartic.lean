-- Prove2me | Definitions.Def_MellinDuality_Quartic
-- name    : MellinDuality_Quartic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:44:09.434579+00:00
-- url     : https://prove2.me/theorems/4788df74-395a-4db1-8c10-d166d86dea7a
-- title:
--   Quartic
-- statement:
--   Definitions and structural lemmas for Quartic, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean

module
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
def sqCorr (X : Finset (ZMod p)) (a : ZMod p) : ℤ := ∑ u ∈ X, parSign u * parSign (a * u ^ 2)
section Fibers
variable {χ : MulChar (ZMod p) GaussianInt}
variable (hp8 : p % 8 = 5) (hχ : orderOf χ = 4)
include hp8 hχ
end Fibers
end MellinDuality


