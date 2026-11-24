-- Prove2me | Definitions.Def_ShelahHalesJewett_HalesJewett
-- name    : ShelahHalesJewett_HalesJewett
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:50:22.59008+00:00
-- url     : https://prove2.me/theorems/32cb84ed-71cb-4f5f-b39a-8f6c423ce3e1
-- title:
--   Hales Jewett
-- statement:
--   Definitions and structural lemmas for Hales Jewett, from Gabriel Dahia (gdahia/ShelahHalesJewett; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shelah primitive-recursive bound for Hales-Jewett numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/HalesJewett.lean

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.SetTheory.Cardinal.NatCard
public import Definitions.Def_ShelahHalesJewett_Line
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Combinatorics
namespace Subspace
def insensitiveBound (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, r => insensitiveBound k n (r ^ k) + r ^ k ^ insensitiveBound k n (r ^ k)
end Subspace
namespace Line
def shelahBound : ℕ → ℕ → ℕ
  | 0, r => min r 1
  | 1, _ => 1
  | k + 2, r => Subspace.insensitiveBound (k + 2) (shelahBound (k + 1) r) r
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
end Line
end Combinatorics


