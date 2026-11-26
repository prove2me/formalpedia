-- Prove2me | Definitions.Def_MellinDuality_Pairs
-- name    : MellinDuality_Pairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:44:52.365904+00:00
-- url     : https://prove2.me/theorems/5d82d406-a7e5-4b34-ace8-4eddee47f7bb
-- title:
--   Pairs
-- statement:
--   Definitions and structural lemmas for Pairs, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Pairs.lean

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
open Finset
section Quartic
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
end Quartic
end MellinDuality


