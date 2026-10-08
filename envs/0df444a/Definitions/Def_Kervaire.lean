-- Prove2me | Definitions.Def_Kervaire
-- name    : Kervaire
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.871982+00:00
-- url     : https://prove2.me/theorems/99e0c083-942d-4684-b72b-550380ac5f36
-- statement:
--   For a group A, WordGroup(A) is the free product of A with the infinite cyclic group written multiplicatively as ℤ, so its elements are words in elements of A and a free letter t. The exponentSum of a word w is the integer image of w under the projection of the free product onto the ℤ factor, that is, the total exponent of t in w with A-letters contributing nothing. A word w is Unimodular when this exponent sum equals 1 or -1. The relatorClosure of w is the normal closure in WordGroup(A) of the single element w, which is automatically a normal subgroup, and RelatorQuotient(w) is the quotient of WordGroup(A) by it, the group obtained from A by adjoining t subject to the relation w = 1. Finally, coefficientMap(w) is the group homomorphism from A to RelatorQuotient(w) obtained by including A into the free product and then passing to the quotient. These are only definitions: the block states no theorem, for instance about injectivity of coefficientMap, which is the kind of question this setup is meant to express.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Kervaire.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Kervaire.lean; bytes 16..945
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Kervaire

universe u

abbrev WordGroup (A : Type u) [Group A] := Monoid.Coprod A (Multiplicative ℤ)

def exponentSum {A : Type u} [Group A] (w : WordGroup A) : ℤ :=
  Multiplicative.toAdd (Monoid.Coprod.snd w)

def Unimodular {A : Type u} [Group A] (w : WordGroup A) : Prop :=
  exponentSum w = 1 ∨ exponentSum w = -1

def relatorClosure {A : Type u} [Group A] (w : WordGroup A) : Subgroup (WordGroup A) :=
  Subgroup.normalClosure ({w} : Set (WordGroup A))

instance {A : Type u} [Group A] (w : WordGroup A) : (relatorClosure w).Normal :=
  inferInstanceAs (Subgroup.normalClosure ({w} : Set (WordGroup A))).Normal

abbrev RelatorQuotient {A : Type u} [Group A] (w : WordGroup A) :=
  WordGroup A ⧸ relatorClosure w

def coefficientMap {A : Type u} [Group A] (w : WordGroup A) : A →* RelatorQuotient w :=
  (QuotientGroup.mk' (relatorClosure w)).comp Monoid.Coprod.inl



end Kervaire
end
end OAI


