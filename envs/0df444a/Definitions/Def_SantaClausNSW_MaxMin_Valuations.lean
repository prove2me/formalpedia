-- Prove2me | Definitions.Def_SantaClausNSW_MaxMin_Valuations
-- name    : SantaClausNSW_MaxMin_Valuations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:34:23.631196+00:00
-- url     : https://prove2.me/theorems/dfac1087-790f-4c4c-8f81-2a116b60b56e
-- title:
--   Additive, submodular and subadditive valuations, allocations, the max-min value, the bit bound σ and the configuration LP
-- statement:
--   There are $n$ agents and $m$ items, indexed $0,\dots,n-1$ and $0,\dots,m-1$. A **valuation** is a function $v$ from sets of items to $\mathbb R$ that is normalized, $v(\emptyset)=0$, and monotone, $v(S)\le v(S')$ for $S\subseteq S'$ (the published `IsNormalized`, `IsMonotone`). It is **additive** if $v(S)=\sum_{j\in S}v(\{j\})$, **submodular** if $v(S\cup\{j\})-v(S)\ge v(S'\cup\{j\})-v(S')$ whenever $S\subseteq S'$ and $j\notin S'$, and **subadditive** if $v(S\cup S')\le v(S)+v(S')$.
--
--   An **allocation** is a family $(A_i)$ of pairwise disjoint bundles (items may stay unassigned); its max-min value is
--   $$\operatorname{mm}(v,A)=\min_{i}v_i(A_i).$$
--   The **bit bound** $\sigma$ says that every value $v_i(S)$ equals $a/b$ with naturals $a,b\le 2^\sigma$, $b\neq0$.
--
--   A **feasible configuration solution** is a family of masses $y_{i,S}\ge0$ with $\sum_S y_{i,S}=1$ for every agent and $\sum_i\sum_{S\ni j}y_{i,S}\le1$ for every item; its configurations are those of positive mass. It has **objective value** $t$ if every configuration $S$ of positive mass of agent $i$ has $v_i(S)\ge t$. $T_{LP}$ is the supremum of the targets $t\ge0$ at which such a solution exists (for $n\ge1$ it is a maximum).
--
--   A **supporting clause** for $(v,S)$ is a vector $w\ge0$ on $S$ with $w(Q)\le v(Q)$ for $Q\subseteq S$ and $w(S)=v(S)$; an **additive lower bound** on $S$ drops the equality. The **marginal clause** along an ordering $j_1,\dots,j_s$ gives $j_k$ the value $v(\{j_1,\dots,j_k\})-v(\{j_1,\dots,j_{k-1}\})$. Finally, $\Pr[E(Q)]$ for the random set $Q\subseteq S$ retaining item $j$ independently with probability $p_j$ is $\sum_{Q\subseteq S,\,E(Q)}\prod_{j\in Q}p_j\prod_{j\in S\setminus Q}(1-p_j)$.
--
--   These objects are the vocabulary of §2 and §3 of the paper; every statement of the mission uses them.
--
--   **Formalization Note.** Agents and items are `Fin n`, `Fin m`; valuations are real-valued. `mmValue` is `0` when $n=0$; every statement assumes $n\ge1$. `TLP` is an `sSup`; for $n\ge1$ the feasible targets form a nonempty interval $[0,T_{LP}]$ bounded by $\min_i v_i(M)$, so it is the paper's largest target.
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 10–11 §2; p. 17 (13); p. 19 §3.4–3.5; p. 25 Lemma 3.9; p. 67 App. E.1

import Mathlib
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation

namespace SantaClausNSW.MaxMin

open MultiAllocToAlloc.Subadditive

/-!
# Valuations, allocations, the max-min value and the configuration LP

Chen, Feng, Hu, Li, Zhang, *Santa Claus and Weighted Nash Social Welfare with Subadditive
Valuations*, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 10–11 §2, p. 17 (13),
p. 19 §3.5, p. 67 App. E.1.

Agents are `Fin n`, items are `Fin m`; a valuation is a function `Finset (Fin m) → ℝ`.
Normalization and monotonicity are the published `MultiAllocToAlloc.Subadditive.IsNormalized`
and `IsMonotone`.
-/

/-- Additive (p. 10): `v(S) = ∑_{j ∈ S} v({j})` for every `S`. -/
def IsAdditive {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S : Finset (Fin m), v S = ∑ j ∈ S, v {j}

/-- Submodular (p. 10): `v(S ∪ {j}) − v(S) ≥ v(S' ∪ {j}) − v(S')` whenever `S ⊆ S'` and
`j ∉ S'`. -/
def IsSubmodular {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S S' : Finset (Fin m), ∀ j : Fin m, S ⊆ S' → j ∉ S' →
    v (insert j S') - v S' ≤ v (insert j S) - v S

/-- Subadditive (p. 10): `v(S ∪ S') ≤ v(S) + v(S')` for all `S, S'`. -/
def IsSubadditive {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S S' : Finset (Fin m), v (S ∪ S') ≤ v S + v S'

/-- A valuation of the paper (p. 10): normalized and monotone. -/
def IsValuation {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  IsNormalized v ∧ IsMonotone v

/-- An allocation (p. 10): pairwise disjoint bundles; items may stay unassigned. -/
def IsAllocation {n m : ℕ} (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i k : Fin n, i ≠ k → Disjoint (A i) (A k)

/-- The max-min objective `min_{i ∈ N} v_i(A_i)` (p. 10). For `n = 0` there is no agent and the
value is `0`; every statement of the mission assumes `n ≥ 1`. -/
noncomputable def mmValue {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (A : Fin n → Finset (Fin m)) : ℝ :=
  if h : 0 < n then
    (Finset.univ : Finset (Fin n)).inf' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (fun i => v i (A i))
  else 0

/-- The encoding bound of App. E.1 (p. 67): every value `v_i(S)` is a rational `a / b` with
natural numbers `a, b ≤ 2^σ`, `b ≠ 0`. -/
def BitBounded {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : ℕ) : Prop :=
  ∀ (i : Fin n) (S : Finset (Fin m)), ∃ a b : ℕ, b ≠ 0 ∧ a ≤ 2 ^ σ ∧ b ≤ 2 ^ σ ∧
    v i S = (a : ℝ) / (b : ℝ)

/-- A feasible configuration solution (p. 10, (2) and (3)): masses `y_{i,S} ≥ 0` with
`∑_S y_{i,S} = 1` for every agent and `∑_i ∑_{S ∋ j} y_{i,S} ≤ 1` for every item. The
configuration set `C_i` of agent `i` is the support `{S : y_{i,S} > 0}`. -/
def IsConfigSolution {n m : ℕ} (y : Fin n → Finset (Fin m) → ℝ) : Prop :=
  (∀ i S, 0 ≤ y i S) ∧
  (∀ i : Fin n, ∑ S : Finset (Fin m), y i S = 1) ∧
  (∀ j : Fin m, ∑ i : Fin n, ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin m) => j ∈ S),
      y i S ≤ 1)

/-- `y` uses only configurations of `C_i(t) = {S : v_i(S) ≥ t}` (p. 11). -/
def HasObjective {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (y : Fin n → Finset (Fin m) → ℝ)
    (t : ℝ) : Prop :=
  ∀ i S, 0 < y i S → t ≤ v i S

/-- A configuration solution with objective value `t` (p. 11). -/
def IsConfigSolutionAt {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (y : Fin n → Finset (Fin m) → ℝ) (t : ℝ) : Prop :=
  IsConfigSolution y ∧ HasObjective v y t

/-- The configuration LP at target `t ≥ 0` is feasible. -/
def LPFeasibleAt {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ y : Fin n → Finset (Fin m) → ℝ, IsConfigSolutionAt v y t

/-- `T_LP`, the largest target for which the configuration LP is feasible (p. 11). For `n ≥ 1`
the feasible targets form the nonempty interval `[0, T_LP]` (target `0` is feasible with every
agent on `∅`, every feasible target is at most `v_i(M)`), so the supremum is a maximum. -/
noncomputable def TLP {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  sSup {t : ℝ | LPFeasibleAt v t}

/-- A supporting clause for `(i, S)`, equation (13) (p. 17): a nonnegative vector `w` on `S` with
`w(Q) ≤ v(Q)` for every `Q ⊆ S` and `w(S) = v(S)`. Coordinates outside `S` are ignored. -/
def IsSupportingClause {m : ℕ} (v : Finset (Fin m) → ℝ) (S : Finset (Fin m))
    (w : Fin m → ℝ) : Prop :=
  (∀ j ∈ S, 0 ≤ w j) ∧ (∀ Q ⊆ S, ∑ j ∈ Q, w j ≤ v Q) ∧ ∑ j ∈ S, w j = v S

/-- The marginal clause of Dobzinski–Nisan–Schapira (§3.4, p. 19) along an ordering `ord` of a
set: the `k`-th item of `ord` gets `v({ord_0, …, ord_k}) − v({ord_0, …, ord_{k−1}})`; items not in
`ord` get `0`. -/
def marginalClause {m : ℕ} (v : Finset (Fin m) → ℝ) (ord : List (Fin m)) : Fin m → ℝ :=
  fun j => if j ∈ ord then
      v (ord.take (ord.idxOf j + 1)).toFinset - v (ord.take (ord.idxOf j)).toFinset
    else 0

/-- An additive lower bound on `S` (§3.5, p. 19): nonnegative coefficients `a_j`, `j ∈ S`, with
`a(Q) ≤ v(Q)` for every `Q ⊆ S`. Coordinates outside `S` are ignored. -/
def IsAdditiveLowerBound {m : ℕ} (v : Finset (Fin m) → ℝ) (S : Finset (Fin m))
    (a : Fin m → ℝ) : Prop :=
  (∀ j ∈ S, 0 ≤ a j) ∧ ∀ Q ⊆ S, ∑ j ∈ Q, a j ≤ v Q

/-- The probability that the random set `Q ⊆ S`, which retains each item `j ∈ S` independently
with probability `p_j`, satisfies `E` (Lemma 3.9, p. 25):
`∑_{Q ⊆ S, E(Q)} ∏_{j ∈ Q} p_j ∏_{j ∈ S \ Q} (1 − p_j)`. -/
noncomputable def retainProb {m : ℕ} (S : Finset (Fin m)) (p : Fin m → ℝ)
    (E : Finset (Fin m) → Prop) [DecidablePred E] : ℝ :=
  ∑ Q ∈ S.powerset.filter E, (∏ j ∈ Q, p j) * ∏ j ∈ S \ Q, (1 - p j)

end SantaClausNSW.MaxMin


