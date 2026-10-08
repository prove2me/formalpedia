-- Prove2me | Definitions.Def_OddKaplansky
-- name    : OddKaplansky
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.217513+00:00
-- url     : https://prove2.me/theorems/e3e9a22c-64b8-4e6a-9d70-2ec44663f461
-- statement:
--   Let M = C(1200,600) be the central binomial coefficient and let p be the smallest prime factor of (M!)^2 + 1 (both are fixed, irreducible definitions). For a field K, a group G, an element d of the group algebra K[G] and a function x : G → K, cellular(d,x) is the function sending g to the finite sum over the support of d of d(u)·x(gu), that is, the action of d by right-translated convolution on K-valued functions on G. MainClaim is a defined proposition, not an established theorem. It asserts that p is prime and odd, and that there exist a finite field K of characteristic p with exactly p^4 elements and a finitely generated group G containing a nontrivial element of finite order, together with elements a and b of K[G] such that ab = 1 but ba ≠ 1, while the map x ↦ cellular(b,x) on functions G → K is injective but not surjective.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OddKaplansky.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OddKaplansky.lean; bytes 16..797
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace OddKaplansky

@[irreducible] def sourceM : ℕ := Nat.choose 1200 600
@[irreducible] def sourcePrime : ℕ := Nat.minFac ((Nat.factorial sourceM)^2 + 1)

noncomputable section

def cellular {K G : Type} [Field K] [Group G]
    (d : MonoidAlgebra K G) (x : G → K) (g : G) : K :=
  d.coeff.sum fun u c => c * x (g * u)

def MainClaim : Prop :=
  sourcePrime.Prime ∧ Odd sourcePrime ∧
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K sourcePrime),
    Fintype.card K = sourcePrime^4 ∧
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G,
        a * b = 1 ∧ b * a ≠ 1 ∧
        Function.Injective (cellular b) ∧ ¬ Function.Surjective (cellular b)



end
end OddKaplansky
end OAI


