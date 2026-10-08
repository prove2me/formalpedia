-- Prove2me | Definitions.Def_FoulkesHowe
-- name    : FoulkesHowe
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.942985+00:00
-- url     : https://prove2.me/theorems/54e14ea1-4d91-463b-b223-1a6538f9dd6f
-- statement:
--   For a complex vector space V, the nth symmetric power SymPow(n,V) is defined as the complex span, inside the symmetric algebra of V, of all products ι(v₁)⋯ι(vₙ) of n elements of V, and symMonomial(n,V,v) denotes this product for a tuple v of n vectors, viewed as an element of SymPow(n,V). For natural numbers a and b, foulkesFormula(a,b,V,v), for a b-tuple of a-tuples of vectors v_{j,i}, is an element of SymPow(a, SymPow(b,V)): it equals (a!)^(−b) times the sum, over all b-tuples σ=(σ₀,…,σ_{b−1}) of permutations of {0,…,a−1}, of the a-fold monomial in the b-fold monomials whose ith entry is the product over j of v_{j,σ_j(i)}. IsFoulkesMap(a,b,V,μ) is the proposition that a given complex-linear map μ from SymPow(b, SymPow(a,V)) to SymPow(a, SymPow(b,V)) sends the b-fold monomial of the a-fold monomials of the rows v_j to foulkesFormula(a,b,V,v), for every such array v of vectors. These are definitions only; they do not assert that such a map exists, is unique, or is injective.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FoulkesHowe.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FoulkesHowe.lean; bytes 16..1376
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

def symMonomialRaw (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin n → V) : SymmetricAlgebra ℂ V :=
  ∏ i : Fin n, SymmetricAlgebra.ι ℂ V (v i)

def symPowSubmodule (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    Submodule ℂ (SymmetricAlgebra ℂ V) :=
  Submodule.span ℂ (Set.range (symMonomialRaw n V))

abbrev SymPow (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :=
  ↥(symPowSubmodule n V)

def symMonomial (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin n → V) : SymPow n V :=
  ⟨symMonomialRaw n V v, Submodule.subset_span (Set.mem_range_self v)⟩

def foulkesFormula (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (v : Fin b → Fin a → V) : SymPow a (SymPow b V) := by
  classical
  exact
    ((a.factorial : ℂ) ^ b)⁻¹ •
      ∑ σ : Fin b → Equiv.Perm (Fin a),
        symMonomial a (SymPow b V)
          (fun i => symMonomial b V (fun j => v j ((σ j) i)))

def IsFoulkesMap (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)) : Prop :=
  ∀ v : Fin b → Fin a → V,
    μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (v j))) =
      foulkesFormula a b V v



end Problem346
end
end OAI


