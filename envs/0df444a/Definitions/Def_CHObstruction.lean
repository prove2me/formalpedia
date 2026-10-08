-- Prove2me | Definitions.Def_CHObstruction
-- name    : CHObstruction
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.107162+00:00
-- url     : https://prove2.me/theorems/957a8b20-27a7-4b7b-8e90-c03835cc5ee0
-- statement:
--   For a relational language L, with L(n) the symbols of arity n, a relational model has a set-theoretic carrier and an interpretation of every symbol on tuples from that carrier. A substructure has a carrier contained in the larger carrier and exactly the restricted relations; an isomorphism is a bijection preserving and reflecting every relation. A union of a family contains each member as a substructure and has no carrier elements outside the family. ClassData specifies a class of models and a proposed strong-substructure relation. A cardinal θ is a Löwenheim–Skolem bound if it is at least ℵ₀ and the size of the language, and every subset A of any model M lies in a strong submodel N in the class with |N| ≤ |A| + θ; the Löwenheim–Skolem number is the least such bound. The defined abstract elementary class axioms require strong substructure to relate class members, be reflexive, antisymmetric and transitive, and imply ordinary substructure. Class membership is invariant under isomorphism, and strong substructure is invariant under pairs of isomorphisms agreeing on the smaller carrier. Coherence requires M₀ to be strong in M₁ whenever M₀ is an ordinary substructure of M₁ and both are strong in a common M₂. Every increasing chain indexed by a nonzero ordinal must have a union in the class, strong over every chain member and strong in every common strong extension; some Löwenheim–Skolem bound must exist. Categoricity at μ means a model of size μ exists and any two such class members are isomorphic; TwoModels(μ) means two nonisomorphic class members of size μ exist. CH is the proposition 2^ℵ₀ = ℵ₁. Finally, hanf(κ) = ℶ_{(2^κ)⁺}, where the index is the initial ordinal of the successor cardinal; endpoint = ℶ_{ω₂}, and tailThreshold = ℶ_{(2^ℵ₁)⁺}.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CHObstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CHObstruction.lean; bytes 16..3320
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

structure RelModel (L : ℕ → Type) where
  carrier : ZFSet.{u}
  rel : (n : ℕ) → L n → (Fin n → carrier) → Prop

namespace RelModel

variable {L : ℕ → Type}

structure IsSubstructure (M N : RelModel.{u} L) : Prop where
  subset : M.carrier ⊆ N.carrier
  restrict : ∀ (n) (r : L n) (a : Fin n → M.carrier),
    M.rel n r a ↔ N.rel n r (fun i => ⟨(a i).val, subset (a i).property⟩)

structure Iso (M N : RelModel.{u} L) where
  toEquiv : M.carrier ≃ N.carrier
  map_rel : ∀ (n) (r : L n) (a : Fin n → M.carrier),
    M.rel n r a ↔ N.rel n r (toEquiv ∘ a)

def IsUnion {ι : Type u} (F : ι → RelModel.{u} L) (U : RelModel.{u} L) : Prop :=
  (∀ i, IsSubstructure (F i) U) ∧
  ∀ x : U.carrier, ∃ i, x.val ∈ (F i).carrier

end RelModel

structure ClassData (L : ℕ → Type) where
  objects : RelModel.{u} L → Prop
  strong : RelModel.{u} L → RelModel.{u} L → Prop

namespace ClassData

variable {L : ℕ → Type} (K : ClassData.{u} L)

def LSBound (θ : Cardinal.{u}) : Prop :=
  ℵ₀ ≤ θ ∧ Cardinal.lift.{u, 0} (# (Σ n, L n)) ≤ θ ∧
  ∀ M, K.objects M → ∀ A : ZFSet.{u}, A ⊆ M.carrier →
    ∃ N, K.objects N ∧ K.strong N M ∧ A ⊆ N.carrier ∧ N.carrier.card ≤ A.card + θ

def HasLSNumber (θ : Cardinal.{u}) : Prop :=
  K.LSBound θ ∧ ∀ θ', K.LSBound θ' → θ ≤ θ'

structure IsAEC : Prop where
  strong_objects : ∀ {M N}, K.strong M N → K.objects M ∧ K.objects N
  refl : ∀ {M}, K.objects M → K.strong M M
  antisymm : ∀ {M N}, K.strong M N → K.strong N M → M = N
  trans : ∀ {M N P}, K.strong M N → K.strong N P → K.strong M P
  substructure : ∀ {M N}, K.strong M N → M.IsSubstructure N
  iso_objects : ∀ {M N}, K.objects M → Nonempty (M.Iso N) → K.objects N
  iso_strong : ∀ {M N M' N'} (h : K.strong M N)
    (e : M.Iso M') (f : N.Iso N'),
    (∀ x : M.carrier,
      (e.toEquiv x).val =
        (f.toEquiv ⟨x.val, (substructure h).subset x.property⟩).val) →
    K.strong M' N'
  coherence : ∀ {M₀ M₁ M₂}, M₀.IsSubstructure M₁ →
    K.strong M₀ M₂ → K.strong M₁ M₂ → K.strong M₀ M₁
  chain_union : ∀ (γ : Ordinal.{u}), γ ≠ 0 →
    ∀ (F : γ.ToType → RelModel.{u} L),
    (∀ i, K.objects (F i)) →
    (∀ i j, i ≤ j → K.strong (F i) (F j)) →
    ∃ U, K.objects U ∧ RelModel.IsUnion F U ∧
      (∀ i, K.strong (F i) U) ∧
      (∀ N, K.objects N → (∀ i, K.strong (F i) N) → K.strong U N)
  downward : ∃ θ, K.LSBound θ

def Categorical (μ : Cardinal.{u}) : Prop :=
  (∃ M, K.objects M ∧ M.carrier.card = μ) ∧
  ∀ M N, K.objects M → K.objects N →
    M.carrier.card = μ → N.carrier.card = μ → Nonempty (M.Iso N)

def TwoModels (μ : Cardinal.{u}) : Prop :=
  ∃ M N, K.objects M ∧ K.objects N ∧
    M.carrier.card = μ ∧ N.carrier.card = μ ∧ ¬ Nonempty (M.Iso N)

end ClassData

def CH : Prop := (2 : Cardinal.{u}) ^ ℵ₀ = ℵ_ 1

def hanf (κ : Cardinal.{u}) : Cardinal.{u} := beth (succ ((2 : Cardinal.{u}) ^ κ)).ord

def endpoint : Cardinal.{u} := beth (ω_ 2)

def tailThreshold : Cardinal.{u} := beth (succ ((2 : Cardinal.{u}) ^ (ℵ_ 1))).ord



end CHObstruction
end
end OAI


