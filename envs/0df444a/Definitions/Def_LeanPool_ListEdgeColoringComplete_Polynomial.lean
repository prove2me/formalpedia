-- Prove2me | Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
-- name    : LeanPool_ListEdgeColoringComplete_Polynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T16:31:31.73392+00:00
-- url     : https://prove2.me/theorems/292818cc-d862-5110-9d32-b4d564f4c6e2
-- title:
--   Polynomial
-- statement:
--   Definitions and structural lemmas for Polynomial, from Juan Pablo Traverso Gianini (jtraverso/haggkvist-janssen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Haggkvist-Janssen bound on the list chromatic index of complete graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Polynomial.lean

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.LinearAlgebra.Vandermonde
public import Theorems.Thm_LeanPool_ListEdgeColoringComplete_canonicalRow_injective

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
abbrev StarVar (V : Type*) := (⊤ : SimpleGraph V).edgeSet ⊕ V
def starMember (f : V ≃ Fin n) (u : V) (k : Fin n) : StarVar V :=
  if h : f.symm k = u then Sum.inr u
  else Sum.inl ⟨s(u, f.symm k), by simpa [eq_comm] using h⟩
noncomputable def starPoly (f : V ≃ Fin n) (u : V) : MvPolynomial (StarVar V) ℚ :=
  ∑ π : Equiv.Perm (Fin n),
    C ((Equiv.Perm.sign π : ℤ) : ℚ) * ∏ k, X (starMember f u k) ^ (π k : ℕ)
noncomputable def graphPoly [Fintype V] (f : V ≃ Fin n) : MvPolynomial (StarVar V) ℚ :=
  ∏ u, starPoly f u
noncomputable def expo [Fintype V] (f : V ≃ Fin n) (P : V → Equiv.Perm (Fin n)) : StarVar V →₀ ℕ :=
  ∑ u, ∑ k, Finsupp.single (starMember f u k) (P u k : ℕ)
noncomputable def termSign [Fintype V] (P : V → Equiv.Perm (Fin n)) : ℚ :=
  ∏ u, ((Equiv.Perm.sign (P u) : ℤ) : ℚ)
noncomputable def canonicalPerm (f : V ≃ Fin n) (u : V) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (canonicalRow (f u))
    (Finite.injective_iff_bijective.mp (canonicalRow_injective _))
end LeanPool.ListEdgeColoringComplete


