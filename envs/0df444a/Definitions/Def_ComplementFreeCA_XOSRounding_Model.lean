-- Prove2me | Definitions.Def_ComplementFreeCA_XOSRounding_Model
-- name    : ComplementFreeCA_XOSRounding_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:19:16.862762+00:00
-- url     : https://prove2.me/theorems/cf8c072e-b117-47d4-b246-9ab678d69377
-- title:
--   Combinatorial auction with XOS bidders, allocations, welfare and the LP relaxation
-- statement:
--   This file fixes the model of the combinatorial auction and its standard linear programming relaxation.
--
--   **Auction.** A set $M=\{1,\dots,m\}$ of items is sold to bidders $N=\{1,\dots,n\}$. Bidder $i$ has a valuation $v_i$ assigning a real value $v_i(S)$ to every bundle $S\subseteq M$. An **allocation** is a tuple of bundles $(A_1,\dots,A_n)$ that are pairwise disjoint, $A_i\cap A_{i'}=\emptyset$ for $i\neq i'$; items may remain unallocated. Its **social welfare** is $\sum_{i} v_i(A_i)$.
--
--   **XOS valuations.** A *clause* is an additive valuation $w$, given by its item values $(w_1,\dots,w_m)$, with value $w(S)=\sum_{j\in S} w_j$ on a bundle $S$. An admissible clause set $W$ is a nonempty finite set of clauses whose item values are all nonnegative. A valuation $v$ is **XOS with expression $W$** if
--   $$v(S)=\max_{w\in W}\ \sum_{j\in S} w_j \qquad\text{for every } S\subseteq M,$$
--   that is, some clause of $W$ attains $v(S)$ and no clause of $W$ exceeds it. A clause of $W$ attaining $v(S)$ is a **maximizing clause for $S$ in $v$**, and an **XOS oracle** is any map $S\mapsto \mathrm{cl}(S)$ returning a maximizing clause for $S$ (the choice among several is arbitrary).
--
--   **LP relaxation.** For variables $x_{i,S}$, one for each bidder $i$ and each bundle $S\subseteq M$ (the empty bundle included), $x$ is **feasible** if
--   1. for each item $j$: $\sum_{i}\sum_{S\ni j} x_{i,S}\le 1$;
--   2. for each bidder $i$: $\sum_{S} x_{i,S}\le 1$;
--   3. $x_{i,S}\ge 0$ for all $i,S$.
--
--   Its **objective value** is $\mathrm{OPT}^*(x)=\sum_{i,S} x_{i,S}\,v_i(S)$, and $x$ is an **optimal fractional solution** if it is feasible and no feasible $y$ has a larger objective value.
--
--   These objects are the setting of the clause-based randomized rounding algorithm for XOS bidders and of its analysis.
--
--   **Formalization Note** Bidders are `Fin n`, items `Fin m`, bundles `Finset (Fin m)`. XOS is stated through its expression $W$ (the paper's "XOS formula"): normalization $v(\emptyset)=0$ and monotonicity, the paper's standing assumptions, follow from the nonnegativity of the clause entries and are not separate hypotheses. The maximum over $W$ is written as "attained and not exceeded" to avoid a dependent nonemptiness proof.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 1 (§1, the model), p. 4 (§2, additive valuations and Definition 2.1, maximizing clause, XOS oracle), p. 5 (§3, the LP relaxation)

import Mathlib

namespace ComplementFreeCA.XOSRounding

open Finset

/-- A finite set of clauses (additive valuations on the items `Fin m`) is an admissible XOS
expression: it is nonempty and every clause assigns a nonnegative value to every item. -/
def IsXOSClauseSet {m : ℕ} (W : Finset (Fin m → ℝ)) : Prop :=
  W.Nonempty ∧ ∀ w ∈ W, ∀ j, 0 ≤ w j

/-- `v` is the XOS valuation with expression `W` (Definition 2.1): `W` is an admissible clause
set and, for every bundle `S`, `v S = max_{w ∈ W} ∑_{j ∈ S} w j` (the maximum is attained by
some clause of `W`, and no clause of `W` exceeds `v S`). -/
def IsXOSWith {m : ℕ} (v : Finset (Fin m) → ℝ) (W : Finset (Fin m → ℝ)) : Prop :=
  IsXOSClauseSet W ∧
    ∀ S : Finset (Fin m), (∃ w ∈ W, ∑ j ∈ S, w j = v S) ∧ ∀ w ∈ W, ∑ j ∈ S, w j ≤ v S

/-- An XOS oracle for `v` with expression `W`: for every bundle `S`, `cl S` is a maximizing
clause for `S` in `v`, i.e. a clause of `W` whose value on `S` equals `v S`. -/
def IsXOSOracle {m : ℕ} (v : Finset (Fin m) → ℝ) (W : Finset (Fin m → ℝ))
    (cl : Finset (Fin m) → Fin m → ℝ) : Prop :=
  ∀ S : Finset (Fin m), cl S ∈ W ∧ ∑ j ∈ S, cl S j = v S

/-- An allocation of the items `Fin m` to the bidders `Fin n`: the bundles are pairwise
disjoint (items may stay unallocated). -/
def IsAllocation {n m : ℕ} (A : Fin n → Finset (Fin m)) : Prop :=
  Pairwise fun i i' => Disjoint (A i) (A i')

/-- The social welfare `∑_i v_i(A_i)` of an assignment of bundles `A`. -/
def welfare {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (A : Fin n → Finset (Fin m)) : ℝ :=
  ∑ i, v i (A i)

/-- Feasibility for the standard LP relaxation of the combinatorial auction (p. 5):
for each item `j`, `∑_{i, S ∋ j} x_{i,S} ≤ 1`; for each bidder `i`, `∑_S x_{i,S} ≤ 1`;
and `x_{i,S} ≥ 0` for all `i, S`. The variables are indexed by all bidders and all bundles,
including the empty bundle. -/
def IsLPFeasible {n m : ℕ} (x : Fin n → Finset (Fin m) → ℝ) : Prop :=
  (∀ j : Fin m, ∑ i, ∑ S ∈ univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S ≤ 1) ∧
    (∀ i : Fin n, ∑ S, x i S ≤ 1) ∧
    (∀ i S, 0 ≤ x i S)

/-- The objective value `∑_{i,S} x_{i,S} v_i(S)` of the LP relaxation. -/
def lpValue {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (x : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  ∑ i, ∑ S, x i S * v i S

/-- `x` is an optimal fractional solution of the LP relaxation for the valuations `v`. -/
def IsLPOptimal {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (x : Fin n → Finset (Fin m) → ℝ) :
    Prop :=
  IsLPFeasible x ∧ ∀ y, IsLPFeasible y → lpValue v y ≤ lpValue v x

end ComplementFreeCA.XOSRounding


