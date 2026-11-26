-- Prove2me | Definitions.Def_SemigroupBetti_Antichain
-- name    : SemigroupBetti_Antichain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:54:39.293797+00:00
-- url     : https://prove2.me/theorems/8b030266-7efa-55be-a876-2f97d15141ad
-- title:
--   Antichain
-- statement:
--   Definitions and structural lemmas for Antichain, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Antichain.lean

module
public import Definitions.Def_SemigroupBetti_Identities
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
section PairAntichain
variable {T : Finset (ℕ × ℕ)}
def IsPairAntichain (T : Finset (ℕ × ℕ)) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x.1 ≤ y.1 → x.2 ≤ y.2 → x = y
end PairAntichain
namespace GenData
variable (G : GenData)
noncomputable def pairsE : Finset (ℕ × ℕ) :=
  G.famE.image (fun d => (G.sel d {1, 2} 1, G.sel d {1, 2} 2))
end GenData
end SemigroupBetti


