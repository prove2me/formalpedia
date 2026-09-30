-- Prove2me | Definitions.Def_ComplementFreeCA_XOSGreedy_Model
-- name    : ComplementFreeCA_XOSGreedy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:32:49.350356+00:00
-- url     : https://prove2.me/theorems/54d1d975-821e-4541-bb09-26854e681ec4
-- title:
--   XOS valuations, allocations, social welfare, demand and XOS oracles
-- statement:
--   This file fixes the combinatorial-auction model of Dobzinski, Nisan and Schapira for XOS bidders. A set $M=\{1,\dots,m\}$ of items is sold to $n$ bidders.
--
--   1. **XOS expression.** An *additive valuation* (a *clause*) is given by nonnegative item values $w(1),\dots,w(m)$ and assigns to a bundle $S\subseteq M$ the value $w(S)=\sum_{j\in S} w(j)$. An *XOS expression* is a nonempty finite set of clauses $\{w_1,\dots,w_t\}$; the *XOS valuation* it defines is
--   $$
--   v(S)=\max_{k} w_k(S)\qquad (S\subseteq M).
--   $$
--   Such a valuation is automatically normalized ($v(\emptyset)=0$) and monotone.
--   2. **Allocation.** An allocation is a tuple of bundles $O_1,\dots,O_n\subseteq M$ with $O_i\cap O_{i'}=\emptyset$ for $i\neq i'$; items may remain unallocated.
--   3. **Social welfare.** For a profile of XOS valuations $v_1,\dots,v_n$, the welfare of bundles $S_1,\dots,S_n$ is $\sum_i v_i(S_i)$.
--   4. **Demand oracle.** A map $(i,p)\mapsto \mathrm{dem}(i,p)$ is a demand oracle if, for every bidder $i$ and every item-price vector $p\in\mathbb R^m$, the bundle $\mathrm{dem}(i,p)$ maximizes $v_i(T)-\sum_{j\in T}p_j$ over all $T\subseteq M$.
--   5. **XOS oracle.** A map $(i,S)\mapsto \mathrm{cl}(i,S)$ is an XOS oracle if, for every bidder $i$ and bundle $S$, $\mathrm{cl}(i,S)$ is one of the clauses of $v_i$'s expression and is a *maximizing clause* for $S$: $\mathrm{cl}(i,S)(S)=v_i(S)$.
--
--   These are the objects on which the greedy price-update algorithm of §3.3 runs; every theorem of this mission is stated for every demand oracle and every XOS oracle meeting these specifications, so no tie-breaking rule is fixed.
--
--   **Formalization Note** Bidders are `Fin n`, items `Fin m`, bundles `Finset (Fin m)`. The XOS valuation is given by its expression (the paper's "XOS expression"), a `Finset` of clauses `Fin m → ℝ` with nonnegative entries, and the maximum is `Finset.sup'`. Normalization and monotonicity, the paper's standing assumptions (p. 1), follow from this representation. The paper's "S_1, …, S_m" in the definition of an allocation (p. 1) is a slip for one bundle per bidder, S_1, …, S_n.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 1 (§1, model; demand query (ii)) and p. 4 (additive valuations, Definition 2.1, maximizing clause, XOS oracle)

import Mathlib

namespace ComplementFreeCA.XOSGreedy

/-- An XOS expression over the items `Fin m` (Definition 2.1): a nonempty finite set of
clauses, each clause an additive valuation given by its item values `w j ≥ 0`. -/
structure XOSExpr (m : ℕ) where
  /-- The clauses `w_1, …, w_t`; the clause `w` gives item `j` the value `w j`. -/
  clauses : Finset (Fin m → ℝ)
  /-- There is at least one clause (`t ≥ 1`). -/
  nonempty : clauses.Nonempty
  /-- Every clause is a monotone additive valuation: its item values are nonnegative. -/
  nonneg : ∀ w ∈ clauses, ∀ j, 0 ≤ w j

/-- The XOS valuation defined by an expression: `v(S) = max_k w_k(S)`, where
`w_k(S) = ∑_{j ∈ S} w_k(j)`. -/
noncomputable def XOSExpr.val {m : ℕ} (E : XOSExpr m) (S : Finset (Fin m)) : ℝ :=
  E.clauses.sup' E.nonempty (fun w => ∑ j ∈ S, w j)

/-- An allocation of the items `Fin m` to the bidders `Fin n`: bundles that are pairwise
disjoint (`S_i ∩ S_j = ∅` for `i ≠ j`). Items may stay unallocated. -/
def IsAllocation {n m : ℕ} (O : Fin n → Finset (Fin m)) : Prop :=
  ∀ i i', i ≠ i' → Disjoint (O i) (O i')

/-- The social welfare `∑_i v_i(S_i)` of the bundles `S` for the XOS profile `E`. -/
noncomputable def welfare {n m : ℕ} (E : Fin n → XOSExpr m) (S : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i, (E i).val (S i)

/-- `dem` is a demand oracle for the profile `E`: for every bidder `i` and every price vector
`p`, the bundle `dem i p` maximizes `v_i(T) - ∑_{j ∈ T} p_j` over all bundles `T`. -/
def IsDemandOracle {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) : Prop :=
  ∀ i p T, (E i).val T - ∑ j ∈ T, p j ≤ (E i).val (dem i p) - ∑ j ∈ dem i p, p j

/-- `cl` is an XOS oracle for the profile `E`: for every bidder `i` and bundle `S`, the
additive valuation `cl i S` is a clause of `E i` and a maximizing clause for `S`,
i.e. `∑_{j ∈ S} (cl i S) j = v_i(S)`. -/
def IsXOSOracle {n m : ℕ} (E : Fin n → XOSExpr m)
    (cl : Fin n → Finset (Fin m) → (Fin m → ℝ)) : Prop :=
  ∀ i S, cl i S ∈ (E i).clauses ∧ ∑ j ∈ S, cl i S j = (E i).val S

end ComplementFreeCA.XOSGreedy


