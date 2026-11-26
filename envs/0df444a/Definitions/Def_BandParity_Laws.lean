-- Prove2me | Definitions.Def_BandParity_Laws
-- name    : BandParity_Laws
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:00:05.261685+00:00
-- url     : https://prove2.me/theorems/e004643f-4b4e-49d7-a361-9898de14a36b
-- title:
--   Laws
-- statement:
--   Definitions and structural lemmas for Laws, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
abbrev cls (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter (fun x => χ x = z)
section Quartic
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
end Quartic
end BandParity


