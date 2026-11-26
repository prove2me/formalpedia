-- Prove2me | Definitions.Def_SemigroupBetti_Exceptional
-- name    : SemigroupBetti_Exceptional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:55:48.229698+00:00
-- url     : https://prove2.me/theorems/3eace754-7471-4e63-8a8b-20cc407c5257
-- title:
--   Exceptional
-- statement:
--   Definitions and structural lemmas for Exceptional, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Exceptional.lean

module
public import Definitions.Def_SemigroupBetti_Arith
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
namespace GenData
variable (G : GenData)
noncomputable def pairsOf (F : Finset ℕ) (K : Finset (Fin 4)) (i k : Fin 4) : Finset (ℕ × ℕ) :=
  F.image (fun d => (G.sel d K i, G.sel d K k))
section Exceptional
variable {G}
variable (hA : G.A = 1) (hB : G.B = G.W - 1)
include hA hB
set_option linter.unusedSectionVars false
end Exceptional
end GenData
end SemigroupBetti


