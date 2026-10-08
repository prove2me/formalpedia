-- Prove2me | Definitions.Def_InfiniteMatroidCorollaries
-- name    : InfiniteMatroidCorollaries
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.231593+00:00
-- url     : https://prove2.me/theorems/d98d468b-7f82-4b9d-ada7-9ed9e46c2194
-- statement:
--   This block sets up tools for a counterexample about infinite matroids. contractOnto(M,C) is the matroid on the same ground type obtained by restricting the dual of M to C and dualizing back, i.e. contraction onto C. HasPackingCovering(M₀,M₁) holds when the two matroids share a ground set E and E splits into disjoint parts P and C such that there are disjoint sets S₀,S₁ ⊆ P spanning P in M₀|P and M₁|P respectively, and sets I₀,I₁ ⊆ C that are independent in the contractions of M₀ and M₁ onto C and whose union is all of C. The concrete types are D = Σ m, ((Fin m → Bool) → Bool), E0 = D × Bool and E = ℤ × D. An explicit integer bookkeeping then builds a bijection componentEquiv between Vertex(p) × (α × Bool), where Vertex(p) is the set of integers whose parity matches the Boolean p, and ℤ × α: bundleAt(n,b) sends a vertex n and bit b to n or n−1 (with the choice flipped for negative n), so that each integer is hit exactly once, and the bijection is proved. Given a matroid Q on α × Bool, rayMatroid(Q,p) is the direct sum of copies of Q indexed by Vertex(p), transported along componentEquiv to a matroid on ℤ × α. A matroid is uniform if every subset of its ground set is independent or spanning, and partitional if it is isomorphic to a direct sum of uniform matroids over some indexed family. HasIntersection(M,N) says there exist a set J independent in both and a disjoint split J = J₀ ∪ J₁ with closure_M(J₀) ∪ closure_N(J₁) equal to the ground set of M. For a family of matroids Mᵢ on a common type, FamilyCovering(F,M) means independent sets Iᵢ in each Mᵢ whose union is F, and FamilyPacking(M) means pairwise disjoint sets Sᵢ with Sᵢ spanning in Mᵢ. CoveringConjectureFor(F,M) is the defined proposition that covering F is equivalent to the statement that for every Y ⊆ F, packing for the restrictions Mᵢ|Y implies covering Y by them; PackingConjectureFor(F,M) is the dual proposition that packing holds iff, for every Y ⊆ F, covering Y by the contractions onto Y implies packing for those contractions. These are definitions of conjecture-style propositions, not established theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InfiniteMatroidCorollaries.lean; bytes 16..4634
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

abbrev D := (m : ℕ) × ((Fin m → Bool) → Bool)
abbrev E0 := D × Bool
abbrev E := ℤ × D

def contractOnto {α : Type*} (M : Matroid α) (C : Set α) : Matroid α :=
  (M.dual ↾ C).dual

def HasPackingCovering {α : Type*} (M₀ M₁ : Matroid α) : Prop :=
  ∃ P C S₀ S₁ I₀ I₁ : Set α,
    Disjoint P C ∧ P ∪ C = M₀.E ∧ M₁.E = M₀.E ∧
    S₀ ⊆ P ∧ S₁ ⊆ P ∧ Disjoint S₀ S₁ ∧
    (M₀ ↾ P).Spanning S₀ ∧ (M₁ ↾ P).Spanning S₁ ∧
    I₀ ⊆ C ∧ I₁ ⊆ C ∧
    (contractOnto M₀ C).Indep I₀ ∧
    (contractOnto M₁ C).Indep I₁ ∧ I₀ ∪ I₁ = C

def bundleAt (n : ℤ) (b : Bool) : ℤ :=
  if n < 0 then (if b then n - 1 else n) else (if b then n else n - 1)

def parityBit (p : Bool) : ℤ := if p then 1 else 0
abbrev Vertex (p : Bool) := {n : ℤ // n % 2 = parityBit p}

def componentMap {α : Type*} {p : Bool} (v : Vertex p) (x : α × Bool) : ℤ × α :=
  (bundleAt v x.2,x.1)

def globalComponentMap (α : Type*) (p : Bool) (x : Vertex p × (α × Bool)) : ℤ × α :=
  componentMap x.1 x.2

noncomputable def componentEquiv (α : Type*) (p : Bool) : (Vertex p × (α × Bool)) ≃ (ℤ × α) :=
  Equiv.ofBijective (globalComponentMap α p) (by
    have bundleAt_bounds (n : ℤ) (b : Bool) : n - 1 ≤ bundleAt n b ∧ bundleAt n b ≤ n := by
      unfold bundleAt
      split_ifs <;> omega
    have bundleAt_injective (n : ℤ) : Function.Injective (bundleAt n) := by
      intro b c h
      cases b <;> cases c <;> simp_all [bundleAt] <;> split_ifs at h <;> omega
    have bundleAt_right (n : ℤ) : ∃ b, bundleAt n b = n := by
      by_cases h : n < 0
      · exact ⟨false,by simp [bundleAt,h]⟩
      · exact ⟨true,by simp [bundleAt,h]⟩
    have bundleAt_left (n : ℤ) : ∃ b, bundleAt n b = n - 1 := by
      by_cases h : n < 0
      · exact ⟨true,by simp [bundleAt,h]⟩
      · exact ⟨false,by simp [bundleAt,h]⟩

    have globalComponentMap_injective :
        Function.Injective (globalComponentMap α p) := by
      rintro ⟨⟨n,hn⟩,d,b⟩ ⟨⟨m,hm⟩,e,c⟩ h
      have hnm : bundleAt n b = bundleAt m c := congrArg Prod.fst h
      have hde : d = e := congrArg Prod.snd h
      have hb := bundleAt_bounds n b
      have hc := bundleAt_bounds m c
      have hnm' : n = m := by omega
      subst m
      have hbc := bundleAt_injective n hnm
      subst e; subst c
      rfl

    have globalComponentMap_surjective :
        Function.Surjective (globalComponentMap α p) := by
      rintro ⟨n,d⟩
      by_cases hn : n % 2 = parityBit p
      · obtain ⟨b,hb⟩ := bundleAt_right n
        exact ⟨(⟨n,hn⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
      · have hn' : (n+1) % 2 = parityBit p := by
          cases p <;> simp only [parityBit,Bool.false_eq_true,ite_false,ite_true] at hn ⊢ <;> omega
        obtain ⟨b,hb⟩ := bundleAt_left (n+1)
        exact ⟨(⟨n+1,hn'⟩,d,b),by simp [globalComponentMap,componentMap,hb]⟩
    exact ⟨globalComponentMap_injective, globalComponentMap_surjective⟩)

noncomputable def rayMatroid {α : Type*} (Q : Matroid (α × Bool)) (p : Bool) : Matroid (ℤ × α) :=
  (Matroid.sum' (fun _ : Vertex p ↦ Q)).mapEquiv (componentEquiv α p)

def IsUniform {α : Type*} (M : Matroid α) : Prop :=
  ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X

def IsPartitional {α : Type} (M : Matroid α) : Prop :=
  ∃ (ι : Type) (β : ι → Type) (N : ∀ i, Matroid (β i)) (e : (Σ i, β i) ≃ α),
    (∀ i, IsUniform (N i)) ∧ M = (Matroid.sigma N).mapEquiv e

def HasIntersection {α : Type*} (M N : Matroid α) : Prop :=
  ∃ J J₀ J₁ : Set α, M.Indep J ∧ N.Indep J ∧
    Disjoint J₀ J₁ ∧ J₀ ∪ J₁ = J ∧ M.closure J₀ ∪ N.closure J₁ = M.E

def FamilyCovering {α ι : Type*} (F : Set α) (M : ι → Matroid α) : Prop :=
  ∃ I : ι → Set α, (∀ i, (M i).Indep (I i)) ∧ (⋃ i, I i) = F

def FamilyPacking {α ι : Type*} (M : ι → Matroid α) : Prop :=
  ∃ S : ι → Set α, (Pairwise fun i j ↦ Disjoint (S i) (S j)) ∧
    ∀ i, (M i).Spanning (S i)

def CoveringConjectureFor {α ι : Type*} (F : Set α) (M : ι → Matroid α) : Prop :=
  FamilyCovering F M ↔ ∀ Y ⊆ F,
    FamilyPacking (fun i ↦ M i ↾ Y) → FamilyCovering Y (fun i ↦ M i ↾ Y)

def PackingConjectureFor {α ι : Type*} (F : Set α) (M : ι → Matroid α) : Prop :=
  FamilyPacking M ↔ ∀ Y ⊆ F,
    FamilyCovering Y (fun i ↦ contractOnto (M i) Y) →
    FamilyPacking (fun i ↦ contractOnto (M i) Y)



end InfiniteMatroidCounterexample
end OAI


