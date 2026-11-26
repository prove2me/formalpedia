-- Prove2me | Definitions.Def_FixedOrderFactor_Diagonal
-- name    : FixedOrderFactor_Diagonal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:48:57.266502+00:00
-- url     : https://prove2.me/theorems/480af821-0dbc-53a1-a23e-f510210ead2a
-- title:
--   Diagonal
-- statement:
--   Definitions and structural lemmas for Diagonal, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Diagonal.lean

module
public import Definitions.Def_FixedOrderFactor_Values
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Real Filter Topology Finset
namespace FixedOrderFactor
noncomputable def zterm (N : Finset Nat.Primes) (s n : ℕ) : ℝ :=
  if 0 < n ∧ PrimeTo N n then 1 / (n : ℝ) ^ s else 0
noncomputable def pairTerm (N : Finset Nat.Primes) (r : ℕ) (ab : ℕ × ℕ) : ℝ :=
  if 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
  then 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r else 0
end FixedOrderFactor


