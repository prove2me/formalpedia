-- Prove2me | Definitions.Def_MellinDuality_Half
-- name    : MellinDuality_Half
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:43:09.400727+00:00
-- url     : https://prove2.me/theorems/db1a9442-dbbd-577c-86cd-5da8fefd75a3
-- title:
--   Half
-- statement:
--   Definitions and structural lemmas for Half, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean

module
public import Definitions.Def_MellinDuality_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {R : Type*} [CommRing R]
end MellinDuality


