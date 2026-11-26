-- Prove2me | Definitions.Def_FixedOrderFactor_Model
-- name    : FixedOrderFactor_Model
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:47:27.068061+00:00
-- url     : https://prove2.me/theorems/a9740021-c993-58c9-9046-079f6f6e66b2
-- title:
--   Model
-- statement:
--   Definitions and structural lemmas for Model, from J. S. Farland (jkfarland-bot/FixedOrderFactor-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned FixedOrderFactor: order-r correction factor for mean squares of L(1, chi) and 35/34 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Model.lean

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Real Filter Topology Finset
namespace FixedOrderFactor
noncomputable def primesUpTo' (N : Finset Nat.Primes) (Y : ℕ) : Finset {q : Nat.Primes // q ∉ N} :=
  (primesUpTo N Y).subtype (· ∉ N)
end FixedOrderFactor


