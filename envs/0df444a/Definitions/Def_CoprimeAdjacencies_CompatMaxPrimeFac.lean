-- Prove2me | Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
-- name    : CoprimeAdjacencies_CompatMaxPrimeFac
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:10:02.968632+00:00
-- url     : https://prove2.me/theorems/88b55040-3495-4de5-b141-ac8500ad95d6
-- title:
--   Compat Max Prime Fac
-- statement:
--   Definitions and structural lemmas for Compat Max Prime Fac, from G. Sidoine and contributors's pinned Minimum coprime adjacencies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/MaxPrimeFac.lean

module
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nat
variable {m n p : ℕ}
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactorsList.getLastD n
end Nat


