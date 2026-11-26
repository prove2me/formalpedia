-- Prove2me | Definitions.Def_BandParity_OddSubgroup
-- name    : BandParity_OddSubgroup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:53:16.625312+00:00
-- url     : https://prove2.me/theorems/3818cd2a-c822-500b-8664-be865d6cdb74
-- title:
--   Odd Subgroup
-- statement:
--   Definitions and structural lemmas for Odd Subgroup, from J. S. Farland (jkfarland-bot/Bandparity; see pinned Apache-2.0 LICENSE and README.md)'s pinned BandParity: the band-parity sum of a quartic character and two laws modulo 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean

module
public import Definitions.Def_BandParity_Matching
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BandParity
open Finset
variable {N : ℕ} [NeZero N]
def uSign (u : (ZMod N)ˣ) : ℤ := (-1) ^ (u : ZMod N).val
def bandSignPow (e : ℕ) (u : (ZMod N)ˣ) : ℤ := (-1) ^ ((u : ZMod N).val ^ e / N)
def coset (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (x : (ZMod N)ˣ) :
    Finset (ZMod N)ˣ :=
  univ.filter (fun u => x⁻¹ * u ∈ H)
def oddCount (S : Finset (ZMod N)ˣ) : ℕ :=
  (S.filter (fun u : (ZMod N)ˣ => Odd ((u : ZMod N).val))).card
def cosetBandSum (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (x : (ZMod N)ˣ) (e : ℕ) :
    ℤ :=
  ∑ u ∈ univ.filter (fun u : (ZMod N)ˣ =>
      2 * (u : ZMod N).val < N ∧ (x⁻¹ * u ∈ H ∨ x⁻¹ * (-u) ∈ H)),
    (if x⁻¹ * u ∈ H then 1 else -1) * bandSignPow e u
section Odd
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH
def powKer (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (e : ℕ) : Finset (ZMod N)ˣ :=
  univ.filter (fun k => k ∈ H ∧ k ^ e = 1)
end Odd
end BandParity


