-- Prove2me | Definitions.Def_BandParity_FixedBase
-- name    : BandParity_FixedBase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:52:20.403651+00:00
-- url     : https://prove2.me/theorems/ba7d33cb-38a4-45e8-8621-a2cc287e45e2
-- title:
--   Fixed Base
-- statement:
--   Definitions and structural lemmas for Fixed Base, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean

module
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
def T (χ : MulChar (ZMod p) R) : R := ∑ n : ZMod p, χ n * (n.val : R)
def floorSum (χ : MulChar (ZMod p) R) (b : ZMod p) : R :=
  ∑ n : ZMod p, χ n * ((b.val * n.val / p : ℕ) : R)
end BandParity


