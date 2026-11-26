-- Prove2me | Definitions.Def_BandParity_Main
-- name    : BandParity_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:03:50.754383+00:00
-- url     : https://prove2.me/theorems/7edac13f-9058-5034-bbce-58b1b4f5287e
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean

module
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
section Quartic
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
end Quartic
end BandParity


