-- Prove2me | Definitions.Def_BandParity_Solution
-- name    : BandParity_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:08:52.345543+00:00
-- url     : https://prove2.me/theorems/520f2085-fbf4-5a8f-b1a6-805d4cbe0e84
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean

module
public import Definitions.Def_BandParity
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace BandParity
open Finset
section Prime
variable {p : ℕ} [hp : Fact p.Prime]
section Quartic
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
end Quartic
end Prime
section OddModulus
variable {N : ℕ} [NeZero N] (hN : Odd N) (hN3 : 3 ≤ N)
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hN hN3 hH
end OddModulus
end BandParity


