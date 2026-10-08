-- Prove2me | Definitions.Def_WhitneyMatroid_Binary_Cycles
-- name    : WhitneyMatroid_Binary_Cycles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:42:58.990363+00:00
-- url     : https://prove2.me/theorems/f3d3384f-aa8b-4d5f-b2f4-b0c128935535
-- title:
--   Sums mod 2, cycles, true sums and Postulate (C*) (Appendix)
-- statement:
--   Let $\alpha$ be a set of elements and let $\mathcal C$ be a family of subsets of $\alpha$, thought of as the *circuits* of a matroid. Following Whitney's appendix, subsets are added **mod 2**: the sum of finitely many sets $N_i$, $i \in s$, is the set of elements lying in an odd number of them,
--
--   $$\sum_{i \in s} N_i \pmod 2 = \{\, x : \#\{ i \in s : x \in N_i \} \text{ is odd} \,\}.$$
--
--   For two sets this is the symmetric difference, so $(e_1 + e_2) + (e_2 + e_3) = e_1 + e_3$.
--
--   1. A **cycle** is any sum (mod 2) of circuits. Since a circuit repeated twice cancels, it is enough to sum a finite *set* of circuits; the empty sum gives the **null cycle** $\emptyset$.
--   2. A set $N$ is the **true sum** of $N_1, \dots, N_s$ if these have no common elements (they are pairwise disjoint) and $N = N_1 + \dots + N_s$; for disjoint sets the sum is the union. The empty family has true sum $\emptyset$.
--   3. The family satisfies **Postulate (C\*)** if each cycle is a true sum of circuits.
--
--   For a matroid $M$ these notions are applied to the family of its circuits. Postulate (C\*) singles out exactly the matroids that are represented by matrices of integers mod 2, which is the subject of Whitney's appendix.
--
--   **Formalization Note** Sets are `Set α`; the sum mod 2 `sumMod2 s N` of a family indexed by a finite set `s` uses the parity of a finite count, so it is defined for any family. A cycle is `sumMod2 F id` for a finite set `F` of circuits; a true sum is a union over a finite, pairwise disjoint set of circuits. The definitions take the circuit family as a parameter, so they apply both to an abstract system of "circuits" and to a Mathlib matroid `M` via the family `{C | M.IsCircuit C}`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 530–531, Appendix: chains (A.1), sums mod 2, cycle, true sum, Postulate (C*)

import Mathlib

namespace WhitneyMatroid.Binary

open Classical in
/-- The sum (mod 2) of the sets `N i`, `i ∈ s` (Appendix, pp. 530–531): an element belongs to
the sum exactly when it lies in an odd number of the summands. For two sets this is the
symmetric difference, e.g. `(e₁ + e₂) + (e₂ + e₃) = e₁ + e₃`. -/
noncomputable def sumMod2 {ι α : Type*} (s : Finset ι) (N : ι → Set α) : Set α :=
  {x | Odd (s.filter (fun i => x ∈ N i)).card}

/-- A *cycle* with respect to a family `𝒞` of circuits (Appendix, p. 531): any sum (mod 2) of
finitely many circuits. Summands repeated an even number of times cancel, so it is enough to sum
a finite set `F` of circuits; the empty sum gives the null cycle `∅`. -/
def IsCycleOf {α : Type*} (𝒞 : Set (Set α)) (Q : Set α) : Prop :=
  ∃ F : Finset (Set α), (↑F : Set (Set α)) ⊆ 𝒞 ∧ Q = sumMod2 F id

/-- `Q` is a *true sum* of circuits of `𝒞` (Appendix, p. 531): `Q = N₁ + ⋯ + N_s` for finitely
many circuits `N₁, …, N_s` of `𝒞` with no common elements (pairwise disjoint), so the sum is
their union. The empty family gives `Q = ∅`. -/
def IsTrueSumOf {α : Type*} (𝒞 : Set (Set α)) (Q : Set α) : Prop :=
  ∃ F : Finset (Set α), (↑F : Set (Set α)) ⊆ 𝒞 ∧
    (↑F : Set (Set α)).PairwiseDisjoint id ∧ Q = ⋃ N ∈ F, N

/-- Postulate (C*) (Appendix, p. 531): each cycle is a true sum of circuits. -/
def SatisfiesCStar {α : Type*} (𝒞 : Set (Set α)) : Prop :=
  ∀ Q : Set α, IsCycleOf 𝒞 Q → IsTrueSumOf 𝒞 Q

end WhitneyMatroid.Binary


