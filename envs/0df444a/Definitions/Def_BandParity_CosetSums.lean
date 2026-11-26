-- Prove2me | Definitions.Def_BandParity_CosetSums
-- name    : BandParity_CosetSums
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:54:19.4156+00:00
-- url     : https://prove2.me/theorems/ef4f50ff-995c-4537-b14c-cc67acea85cc
-- title:
--   Coset Sums
-- statement:
--   Definitions and structural lemmas for Coset Sums, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
def cosetSum (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ :=
  ∑ n ∈ univ.filter (fun n : ZMod p => χ n = z), (n.val : ℤ)
def S (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ := cosetSum χ z / p
def k (χ : MulChar (ZMod p) GaussianInt) : ℤ := S χ 1 - S χ (-1)
def t (χ : MulChar (ZMod p) GaussianInt) : ℤ := S χ gi - S χ (-gi)
section Quartic
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
end Quartic
end BandParity


