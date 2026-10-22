-- Prove2me | Definitions.Def_RInf_braid
-- name    : RInf_braid
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T23:10:48.726916+00:00
-- url     : https://prove2.me/theorems/900dc54f-e62f-40ed-8af1-744c56f02534
-- title:
--   The world layer: the idealized pure Artin braid group with its commutator layer
-- statement:
--   The idealized world of the pure Artin braid group on n strings for n at least five. The world bundles the second commutator layer of the lower central series - the quotient of the second term by the third - as an abstract free abelian group with the biadditive commutator pairing through which the layer is generated; the induced action of the automorphisms of the braid group on the layer; the representation of the symmetric group on n + 1 letters through which the induced action factors by equation (8); the eigenvalue-one property of every value of that representation; the standard coordinates identifying the layer with the integer lattice whose rank is the number of triples of strings; and the Reidemeister transfer carrying infinite Reidemeister number on the layer to infinite Reidemeister number on the braid group - the reduction of Remark 1 and Lemma 2.2 that makes the layer the engine of the main theorem.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Sections 2-3 (the induced action and its factorization of equation (8), Theorems 8 and 11, and the transfer of Remark 1).

import Mathlib
import Definitions.Def_RInf_alg

/-!
# The world layer: the idealized pure Artin braid group with its commutator
layer

The world layer of the RInf mission: the idealized pure Artin braid group on n
strings for n at least five, carrying the second commutator layer of the lower
central series - the quotient of the second term by the third - as an abstract
free abelian group with the biadditive commutator pairing, the induced action
of the automorphisms of the braid group on the layer, the representation of
the symmetric group on n + 1 letters through which the induced action factors
by equation (8), the eigenvalue-one property of that representation
established in Theorems 8 and 11, the standard coordinates identifying the
layer with the integer lattice of rank the number of triples, and the
Reidemeister transfer from the layer to the braid group of Remark 1.
-/

namespace RInf

/-- The idealized world of the pure Artin braid group on n strings: the
commutator layer Q with the biadditive pairing comm of commutators, the
induced action act of the automorphisms on the layer, the symmetric-group
representation rep through which the induced action factors, the
eigenvalue-one property of the representation, the standard coordinates on
the layer of rank the number of triples of strings, and the Reidemeister
transfer carrying infinite Reidemeister number on the layer to infinite
Reidemeister number on the braid group. -/
structure BraidWorld (n : Nat) (P Q : Type*) [Group P] [AddCommGroup Q] where
  comm : P → P → Q
  comm_left : ∀ (g1 g2 h : P), comm (g1 * g2) h = comm g1 h + comm g2 h
  comm_right : ∀ (g h1 h2 : P), comm g (h1 * h2) = comm g h1 + comm g h2
  comm_surj : ∀ q : Q, ∃ g h : P, comm g h = q
  act : (P ≃* P) → Q ≃+ Q
  act_comm : ∀ (α : P ≃* P) (g h : P), act α (comm g h) = comm (α g) (α h)
  rep : Equiv.Perm (Fin (n + 1)) → Q ≃+ Q
  rep_one : rep 1 = AddEquiv.refl Q
  rep_mul : ∀ σ τ : Equiv.Perm (Fin (n + 1)), rep (σ * τ) = (rep σ).trans (rep τ)
  factor : ∀ α : P ≃* P, ∃ σ : Equiv.Perm (Fin (n + 1)), act α = rep σ
  rep_eigen : ∀ σ : Equiv.Perm (Fin (n + 1)), HasEigenOne (rep σ)
  coord : Q ≃+ (Fin (Nat.choose n 3) → Int)
  transfer : ∀ α : P ≃* P, ReidInfAdd (act α) → ReidInf α.toMonoidHom

end RInf


