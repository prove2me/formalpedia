-- Prove2me | Definitions.Def_Erdos30Basic
-- name    : Erdos30Basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T17:39:44.915985+00:00
-- url     : https://prove2.me/theorems/f2086694-3349-4fea-b412-c00aa4dcf04a
-- title:
--   Sidon sets and the extremal function $h(N)$
-- statement:
--   This file fixes the objects of Erdős Problem #30. Its declarations are transcribed from the formal-conjectures library (`IsSidon`, its decidability instance and `Finset.maxSidonSubsetCard` from `FormalConjecturesForMathlib/Combinatorics/Basic.lean`, and `h` from `FormalConjectures/ErdosProblems/30.lean`), placed in the namespace `Erdos30`.
--
--   1. **Sidon sets.** Let $\alpha$ be an additive commutative monoid. A set $A\subseteq\alpha$ is a *Sidon set* if for all $i_1,j_1,i_2,j_2\in A$,
--   $$i_1+i_2=j_1+j_2 \implies (i_1=j_1 \text{ and } i_2=j_2)\ \text{ or }\ (i_1=j_2 \text{ and } i_2=j_1),$$
--   i.e. every sum of two elements of $A$ determines the unordered pair of summands.
--   2. **Decidability.** For a finite set $A$ with decidable equality the Sidon property is decidable, by checking the defining condition over all quadruples.
--   3. **Maximal Sidon subsets.** For a finite set $X\subseteq\alpha$, $\operatorname{maxSidon}(X)$ is the largest cardinality of a subset $B\subseteq X$ that is a Sidon set (the empty set is Sidon, so the maximum exists and is $\ge 0$).
--   4. **The extremal function.** For $N\in\mathbb N$,
--   $$h(N)=\operatorname{maxSidon}(\{1,2,\dots,N\}),$$
--   the maximum size of a Sidon set of positive integers not exceeding $N$. In particular $h(0)=0$, and $h(1),\dots,h(15)=1,2,2,3,3,3,4,4,4,4,4,5,5,5,5$.
--
--   Every statement of the mission is phrased in terms of $h$.
-- source:
--   Google DeepMind, formal-conjectures: FormalConjecturesForMathlib/Combinatorics/Basic.lean (IsSidon, Finset.maxSidonSubsetCard) and FormalConjectures/ErdosProblems/30.lean (Erdos30.h), https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/30.lean ; Erdős Problem #30, https://www.erdosproblems.com/30

import Mathlib

namespace Erdos30

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The maximum size of a Sidon set in the supplied `Finset`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

/-- `h N` is the maximum size of a Sidon set in `{1, …, N}`. -/
abbrev h (N : ℕ) : ℕ := maxSidonSubsetCard (Finset.Icc 1 N)

end Erdos30


