-- Prove2me | Definitions.Def_BandParity_Defs
-- name    : BandParity_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:59:24.550076+00:00
-- url     : https://prove2.me/theorems/f79c952a-b886-4a2b-978b-cb3743878093
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Defs.lean

module
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
def parSign (x : ZMod p) : ℤ := (-1) ^ x.val
def band (x : ZMod p) : ℕ := x.val ^ 2 / p
def bandSum (χ : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n * (-1) ^ band n
def Q (p : ℕ) : ℤ := ((p - 1) / 4 : ℕ)
def kappa (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), legendreSym p n
end BandParity


