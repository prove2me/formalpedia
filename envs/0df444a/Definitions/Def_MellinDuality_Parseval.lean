-- Prove2me | Definitions.Def_MellinDuality_Parseval
-- name    : MellinDuality_Parseval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:44:02.791388+00:00
-- url     : https://prove2.me/theorems/1a38bca7-55f0-5094-9abc-21fe51ebe181
-- title:
--   Parseval
-- statement:
--   Definitions and structural lemmas for Parseval, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean

module
public import Definitions.Def_MellinDuality_Mellin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
end MellinDuality


