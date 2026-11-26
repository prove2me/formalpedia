-- Prove2me | Definitions.Def_MellinDuality_Mellin
-- name    : MellinDuality_Mellin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:43:37.236524+00:00
-- url     : https://prove2.me/theorems/7e04b774-da44-5828-83e2-77ea02281cfb
-- title:
--   Mellin
-- statement:
--   Definitions and structural lemmas for Mellin, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Mellin.lean

module
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
section Ring
variable {R : Type*} [CommRing R]
end Ring
section Complex
end Complex
end MellinDuality


