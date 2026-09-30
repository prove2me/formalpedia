-- Prove2me | Definitions.Def_ComplementFreeCA_CFRounding_Auction
-- name    : ComplementFreeCA_CFRounding_Auction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:11:48.238986+00:00
-- url     : https://prove2.me/theorems/cb6254b1-cb5a-462a-9287-52690ab69e78
-- title:
--   Combinatorial auction: normalized, monotone and complement-free valuations, allocations, welfare
-- statement:
--   A set $M=\{1,\dots,m\}$ of items is sold to bidders $N=\{1,\dots,n\}$. A **valuation** is a function $v$ assigning a real value $v(S)$ to every bundle $S\subseteq M$. This file fixes the basic vocabulary of the model.
--
--   1. $v$ is **normalized** if $v(\emptyset)=0$.
--   2. $v$ is **monotone** if $v(S)\le v(T)$ whenever $S\subseteq T\subseteq M$.
--   3. $v$ is **complement free** (subadditive) if for all bundles $S,T$,
--   $$v(S\cup T)\le v(S)+v(T).$$
--   4. An **allocation** is a tuple of bundles $(A_1,\dots,A_n)$ with $A_i\cap A_{i'}=\emptyset$ for $i\ne i'$; items may remain unallocated.
--   5. The **social welfare** of bundles $(A_1,\dots,A_n)$ under valuations $v_1,\dots,v_n$ is $\sum_{i} v_i(A_i)$.
--
--   Normalization and monotonicity are the paper's standing assumptions on every valuation; complement freeness is the class for which the algorithm of Section 3.1 is designed.
--
--   **Formalization Note** Bidders are `Fin n`, items `Fin m`, bundles `Finset (Fin m)`, and a valuation is a function `Finset (Fin m) → ℝ`. The welfare is defined for any tuple of bundles (not only allocations), since it is also applied to the infeasible preallocation of Section 3.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 1, §1 (model: normalized, monotone, allocation, social welfare) and p. 2, §1 (complement free: v(S ∪ T) ≤ v(S) + v(T))

import Mathlib

namespace ComplementFreeCA.CFRounding

/-- A valuation `v` on bundles of the items `Fin m` is *normalized*: `v ∅ = 0` (p. 1). -/
def IsNormalized {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  v ∅ = 0

/-- A valuation `v` is *monotone*: `S ⊆ T → v S ≤ v T` (p. 1). -/
def IsMonotone {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), S ⊆ T → v S ≤ v T

/-- A valuation `v` is *complement free* (subadditive): `v (S ∪ T) ≤ v S + v T` for all
bundles `S, T` (p. 2). -/
def IsSubadditive {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), v (S ∪ T) ≤ v S + v T

/-- An allocation of the items `Fin m` to the bidders `Fin n`: pairwise disjoint bundles
(p. 1). Items may stay unallocated. -/
def IsAllocation {n m : ℕ} (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i i' : Fin n, i ≠ i' → Disjoint (A i) (A i')

/-- The social welfare `∑ᵢ vᵢ(Aᵢ)` of an assignment of bundles `A` (p. 1). -/
def welfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (A : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i, v i (A i)

end ComplementFreeCA.CFRounding


