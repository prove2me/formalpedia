-- Prove2me | Definitions.Def_NagataFactoriality_Basic_UFD
-- name    : NagataFactoriality_Basic_UFD
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:47:37.93681+00:00
-- url     : https://prove2.me/theorems/384e2ecb-56d1-5658-b02b-c6d6d04e6943
-- title:
--   UFD
-- statement:
--   Definitions and structural lemmas for UFD, from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz (Arthur742Ramos/NagataFactoriality; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Prime-generated Nagata factoriality theorem for Noetherian integral domains development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Basic/UFD.lean

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
set_option autoImplicit false
namespace NagataFactoriality
theorem ufd_iff_factorization_and_irreducibles_prime {α : Type*} [CommRing α] [IsDomain α] :
    UniqueFactorizationMonoid α ↔ WfDvdMonoid α ∧ ∀ p : α, Irreducible p → Prime p := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · letI : UniqueFactorizationMonoid α := h
      exact (inferInstance : WfDvdMonoid α)
    · intro p hp
      letI : UniqueFactorizationMonoid α := h
      exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hp
  · rintro ⟨hfac, hprime⟩
    exact UniqueFactorizationMonoid.of_exists_prime_factors (fun a ha => by
      letI : WfDvdMonoid α := hfac
      obtain ⟨f, hf, hassoc⟩ := WfDvdMonoid.exists_factors a ha
      refine ⟨f, ?_, hassoc⟩
      intro b hb
      exact hprime b (hf b hb))
theorem ufd_of_factorization_and_primes {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p) : UniqueFactorizationMonoid α := by
  exact (ufd_iff_factorization_and_irreducibles_prime (α := α)).2 ⟨hfac, hprime⟩
abbrev FactorizationEquivalent {α : Type*} [Monoid α] (f g : Multiset α) : Prop :=
  Multiset.Rel Associated f g
end NagataFactoriality


