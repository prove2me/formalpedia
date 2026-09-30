-- Prove2me | Definitions.Def_ComplementFreeCA_XOSRounding_Algorithm
-- name    : ComplementFreeCA_XOSRounding_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:20:17.077709+00:00
-- url     : https://prove2.me/theorems/f43d39fe-6a25-4b7d-95e8-4d7ec6071c9d
-- title:
--   The clause-based assignment step of the XOS rounding algorithm
-- statement:
--   Fix an XOS oracle $\mathrm{cl}_i$ for each bidder $i$. Given a preallocation $\sigma=(S_1,\dots,S_n)$, let $p^i=\mathrm{cl}_i(S_i)$ be the maximizing clause for $S_i$ in $v_i$, with item values $p^i_1,\dots,p^i_m$. The algorithm of §3.2 allocates each item $j$ to a bidder $i$ with $p^i_j\ge p^{i'}_j$ for all $i'\in N$.
--
--   1. An **assignment rule** $\mathrm{win}$ maps a preallocation $\sigma$ and an item $j$ to a bidder; it is a **highest-clause rule** if
--   $$p^{i'}_j\le p^{\mathrm{win}(\sigma,j)}_j\qquad\text{for all } \sigma,\ j,\ i'.$$
--   Ties may be broken in any way.
--   2. The **algorithm's allocation** on $\sigma$ gives bidder $i$ the items $A_i(\sigma)=\{j:\mathrm{win}(\sigma,j)=i\}$; its welfare is $\mathrm{ALG}(\sigma)=\sum_i v_i(A_i(\sigma))$.
--   3. For $n\ge 1$, $Q_j(\sigma)=\max_{i\in N} p^i_j$ is the largest clause value of item $j$ after the rounding step.
--
--   These are the random variables $\mathrm{ALG}$ and $Q_j$ of the proof of Theorem 3.2.
--
--   **Formalization Note** The rule `win` may depend on the whole preallocation, which covers every tie-breaking convention; statements about the algorithm quantify over every highest-clause rule. `maxClauseEntry` takes the proof `0 < n` as an argument because the maximum over bidders needs at least one bidder.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 7, §3.2, algorithm steps (i)-(iii) and proof of Theorem 3.2 (definitions of Q_j and ALG)

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSRounding_Model

namespace ComplementFreeCA.XOSRounding

open Finset

/-- Step (iii)'s assignment rule: given the preallocation profile `σ` and the clauses
`cl i (σ i)`, the rule `win σ j` names a bidder whose clause value for item `j` is maximal,
`p^{i'}_j ≤ p^{win σ j}_j` for all `i'`. Ties may be broken arbitrarily. -/
def IsHighestClauseRule {n m : ℕ} (cl : Fin n → Finset (Fin m) → Fin m → ℝ)
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) : Prop :=
  ∀ (σ : Fin n → Finset (Fin m)) (j : Fin m) (i' : Fin n),
    cl i' (σ i') j ≤ cl (win σ j) (σ (win σ j)) j

/-- The allocation output by the algorithm of §3.2 on the preallocation `σ`: bidder `i`
receives exactly the items `j` with `win σ j = i`. -/
def algAllocation {n m : ℕ} (win : (Fin n → Finset (Fin m)) → Fin m → Fin n)
    (σ : Fin n → Finset (Fin m)) : Fin n → Finset (Fin m) :=
  fun i => univ.filter fun j => win σ j = i

/-- `ALG(σ)`: the social welfare of the algorithm's allocation on the preallocation `σ`. -/
def algWelfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (σ : Fin n → Finset (Fin m)) : ℝ :=
  welfare v (algAllocation win σ)

/-- `Q_j(σ) = max_{i ∈ N} p^i_j`, where `p^i = cl i (σ i)` is the clause chosen for bidder
`i`'s preallocated bundle. Requires at least one bidder (`0 < n`). -/
def maxClauseEntry {n m : ℕ} (hn : 0 < n) (cl : Fin n → Finset (Fin m) → Fin m → ℝ)
    (σ : Fin n → Finset (Fin m)) (j : Fin m) : ℝ :=
  (univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, mem_univ _⟩ fun i => cl i (σ i) j

end ComplementFreeCA.XOSRounding


