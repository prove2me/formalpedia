-- Prove2me | Definitions.Def_HousingRI_IsStrongCore
-- name    : HousingRI_IsStrongCore
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:10:51.868996+00:00
-- url     : https://prove2.me/theorems/56418679-2137-4623-be45-5944c9cfb3e2
-- title:
--   Coalitions that weakly block an allocation, and the strong core of a housing market
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$. An **allocation** gives each agent exactly one object and no object to two agents; it is a bijection $x:N\to N$, $x_i$ being agent $i$'s allotment.
--
--   1. A nonempty coalition $S\subseteq N$ **weakly blocks** $x$ if there is an allocation $z$ with $\{z_i:i\in S\}=S$, $z_i\,R_i\,x_i$ for every $i\in S$, and $z_j\,P_j\,x_j$ for some $j\in S$.
--   2. An allocation $x$ is in the **strong core** if no coalition weakly blocks it.
--
--   The strong core is the solution concept whose unique element under strict preferences, $\tau(R)$, is the subject of Theorem 1.
--
--   **Formalization Note** The condition $\{z_i:i\in S\}=S$ is written as "$z$ maps $S$ into $S$", which is equivalent for a bijection $z$ of a finite set. Coalitions are finite sets of agents.
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §2, p.6 (allocation) and p.7 (coalitions that weakly block, strong core).

import Mathlib

namespace HousingRI

/-- **Weakly blocks** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, §2, p.7): "A
non-empty coalition S ⊆ N weakly blocks an allocation x if there is an allocation z such that
(1) {zᵢ : i ∈ S} = S, (2) for each i ∈ S, zᵢRᵢxᵢ, and (3) for some j ∈ S, zⱼPⱼxⱼ."

**Formalization Note.** Preferences are a utility matrix (`j Rᵢ k` is `A i k ≤ A i j`). An
allocation (p.6: each agent receives exactly one object, `∪ᵢ{xᵢ} = N`) is a bijection `N → N`.
Condition (1) is written `∀ i ∈ S, z i ∈ S`; for a bijection `z` of a finite `N` this is
equivalent to `{zᵢ : i ∈ S} = S`. -/
def WeaklyBlocks {N : Type*} (A : N → N → ℝ) (x : N → N) (S : Finset N) (z : N → N) : Prop :=
  S.Nonempty ∧ Function.Bijective z ∧ (∀ i ∈ S, z i ∈ S) ∧
    (∀ i ∈ S, A i (x i) ≤ A i (z i)) ∧ ∃ j ∈ S, A j (x j) < A j (z j)

/-- **Strong core** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, §2, p.7): "An
allocation x is in the strong core of the market if there is no coalition that weakly blocks x."

**Formalization Note.** `x` must itself be an allocation, i.e. a bijection `N → N` (p.6). -/
def IsStrongCore {N : Type*} (A : N → N → ℝ) (x : N → N) : Prop :=
  Function.Bijective x ∧ ¬ ∃ (S : Finset N) (z : N → N), WeaklyBlocks A x S z

end HousingRI


