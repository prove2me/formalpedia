-- Prove2me | Definitions.Def_Tachikawa
-- name    : Tachikawa
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:28.490342+00:00
-- url     : https://prove2.me/theorems/8269d6c7-e9cf-49ec-b3a5-419c6d579190
-- statement:
--   Let k be the fraction field of the polynomial ring in three variables over the field with two elements, F₂(x,y,z). For a field K and a K-algebra A that is a ring, SymmetricOver(K,A) means there is a K-linear isomorphism e from A to its K-dual such that, for all a, b, c in A, e(ab)(c) = e(b)(ca) and e(ab)(c) = e(a)(bc); that is, A carries a nondegenerate associative bilinear form that is also cyclically invariant, in the sense given by these two identities. Counterexample is a defined proposition, not an established theorem. It asserts that there exist a ring A and a k-algebra structure on A such that A is finite-dimensional over k and SymmetricOver(k,A) holds, together with an abelian group M carrying compatible A-module and k-module structures (a scalar tower k, A, M), with M finite-dimensional over k, M not a projective A-module, and yet the Ext group Ext^n_A(M,M) is trivial (a subsingleton) for every positive integer n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Tachikawa.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Tachikawa.lean; bytes 16..893
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Tachikawa

noncomputable section

abbrev k := FractionRing (MvPolynomial (Fin 3) (ZMod 2))

def SymmetricOver (K A : Type) [Field K] [Ring A] [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))

def Counterexample : Prop :=
  ∃ (A : Type) (rA : Ring A),
    letI := rA
    ∃ (aA : Algebra k A),
      letI := aA
      Module.Finite k A ∧ SymmetricOver k A ∧
      ∃ (M : Type) (gM : AddCommGroup M),
        letI := gM
        ∃ (mA : Module A M) (mk : Module k M),
          letI := mA
          letI := mk
          IsScalarTower k A M ∧ Module.Finite k M ∧
          ¬ Module.Projective A M ∧
          ∀ n : ℕ, 0 < n →
            Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A M) n)



end
end Tachikawa
end OAI


