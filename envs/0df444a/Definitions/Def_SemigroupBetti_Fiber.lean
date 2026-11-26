-- Prove2me | Definitions.Def_SemigroupBetti_Fiber
-- name    : SemigroupBetti_Fiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:29:17.602416+00:00
-- url     : https://prove2.me/theorems/c1e5bc24-daa1-4d63-b563-7f996e55af68
-- title:
--   Fiber
-- statement:
--   Definitions and structural lemmas for Fiber, from Ben Keene (BenKeene/semigroup-betti; see pinned Apache-2.0 LICENSE and source headers)'s pinned Linear upper bound for the first Betti number of four-generated numerical semigroups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/SemigroupBetti/Fiber.lean

module
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_SharesVar_symm

set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SemigroupBetti
open Finset
namespace GenData
variable (G : GenData)
def fiber (d : ℕ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset fun _ => range (d / G.m + 1)).filter (fun z => G.nu z = d)
def nabla (d : ℕ) : SimpleGraph (G.fiber d) where
  Adj z z' := z ≠ z' ∧ SharesVar z.1 z'.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance (d : ℕ) : DecidableRel (G.nabla d).Adj := fun z z' =>
  inferInstanceAs (Decidable (z ≠ z' ∧ SharesVar z.1 z'.1))
def ncomp (d : ℕ) : ℕ := Fintype.card (G.nabla d).ConnectedComponent
def contributes (d : ℕ) : Prop := 2 ≤ G.ncomp d
instance (d : ℕ) : Decidable (G.contributes d) := inferInstanceAs (Decidable (2 ≤ _))
def H : ℕ := G.n 3 * ∑ i, G.n i
def beta1 : ℕ := ∑ d ∈ range (G.H + 1), (G.ncomp d - 1)
noncomputable def compSupp {d : ℕ} (C : (G.nabla d).ConnectedComponent) : Finset (Fin 4) := by
  classical
  exact univ.filter (fun i => ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i)
end GenData
end SemigroupBetti


