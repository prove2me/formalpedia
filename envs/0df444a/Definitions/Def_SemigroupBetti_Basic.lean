-- Prove2me | Definitions.Def_SemigroupBetti_Basic
-- name    : SemigroupBetti_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:19:05.623798+00:00
-- url     : https://prove2.me/theorems/56543e96-b268-54bc-ab69-1a7e3fc6b578
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Basic.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
def IsFactorization (n : Fin 4 → ℕ) (d : ℕ) (z : Fin 4 → ℕ) : Prop :=
  ∑ i, z i * n i = d
end SemigroupBetti


