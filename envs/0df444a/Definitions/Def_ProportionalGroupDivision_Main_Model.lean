-- Prove2me | Definitions.Def_ProportionalGroupDivision_Main_Model
-- name    : ProportionalGroupDivision_Main_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:10.341006+00:00
-- url     : https://prove2.me/theorems/c3953708-d41f-44c4-8f8e-8a419969b108
-- title:
--   Definition 1 — group fair division, PROP-$c$ allocations and $\mathrm{PROP}(n_1,\dots,n_k)$
-- statement:
--   There are $k$ groups; group $i$ has $n_i$ agents, and agent $j$ of group $i$ is written $(i,j)$. The goods form a finite set $G$, and agent $(i,j)$ has a nonnegative additive valuation: a value $\mu_{(i,j)}(g)\ge 0$ for each good and
--
--   $$\mu_{(i,j)}(X)=\sum_{g\in X}\mu_{(i,j)}(g)\qquad(X\subseteq G).$$
--
--   No upper bound, positivity or normalization of the values is assumed. A **partition** $G=B_1\sqcup\dots\sqcup B_k$ assigns every good to one group; bundles may be empty.
--
--   For a positive integer $c$, a partition satisfies **PROP-$c$** if for every agent $(i,j)$ there is a set $C\subseteq G\setminus B_i$ with $|C|\le c$ such that
--
--   $$\mu_{(i,j)}(B_i)\ \ge\ \frac{\mu_{(i,j)}(G)}{k}-\mu_{(i,j)}(C).$$
--
--   The sets $C$ are witnesses only: they may differ between agents and overlap. Finally, $\mathrm{PROP}(n_1,\dots,n_k)$ is the smallest positive integer $c$ such that for $k$ groups of sizes $n_1,\dots,n_k$ and **any** finite set of goods with **any** nonnegative additive valuations there is a partition satisfying PROP-$c$.
--
--   $\mathrm{PROP}$ is the quantity bounded by the paper's main result (Theorem 2).
--
--   **Formalization Note** Goods are `Fin m` for an arbitrary $m\in\mathbb N$ (every finite set is in bijection with some `Fin m`; $m=0$ is the empty set of goods). A partition is a map $\sigma$ from goods to groups and $B_i=\sigma^{-1}(i)$. $\mathrm{PROP}$ is an infimum in `ℕ∞` over positive integers, so it equals $\infty$ if no positive integer works; its finiteness is part of Theorem 2, not of the definition.
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, §1.1 and Definition 1, PDF p. 2 = printed p. 2

import Mathlib

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-!
# Group fair division and PROP (Definition 1, PDF p. 2)

Shekhovtsov–Sokolov–Cherniavskii–Kupavskii, *Nearly Tight Bounds for Proportional Group Fair
Divisions and One-Sided Discrepancy*, STOC 2027 submission #606, §1.1 and Definition 1, p. 2.

There are `k` groups; group `i` has `n i` agents, and agent `j` of group `i` is the dependent pair
`(i, j)` with `j : Fin (n i)` (the paper's `j ∈ [n_i]`, indexed from `0`). The goods form a finite
set `G`; every finite set is in bijection with some `Fin m`, so goods are `Fin m` for an arbitrary
`m : ℕ` (including `m = 0`, the empty set of goods). Agent `(i, j)` has a valuation
`μ i j : Fin m → ℝ` of single goods, nonnegative, and is additive: `μ_{(i,j)}(X) = ∑_{g ∈ X} μ i j g`.
-/

/-- The valuation table of an instance: `μ i j g` is the value agent `j` of group `i` assigns to
good `g`. -/
abbrev Valuation {k : ℕ} (n : Fin k → ℕ) (m : ℕ) : Type := (i : Fin k) → Fin (n i) → Fin m → ℝ

/-- All valuations are nonnegative (§1.1, p. 2). No upper bound or normalization is imposed. -/
def IsNonneg {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (μ : Valuation n m) : Prop :=
  ∀ i j g, 0 ≤ μ i j g

/-- The additive value `μ_{(i,j)}(X) = ∑_{g ∈ X} μ_{(i,j)}(g)` of a set of goods. -/
def value {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (μ : Valuation n m) (i : Fin k) (j : Fin (n i))
    (X : Finset (Fin m)) : ℝ :=
  ∑ g ∈ X, μ i j g

/-- A partition `G = B_1 ⊔ ⋯ ⊔ B_k` (bundles may be empty) is a map `σ : Fin m → Fin k`
sending each good to the group receiving it; `bundle σ i = B_i`. -/
def bundle {k m : ℕ} (σ : Fin m → Fin k) (i : Fin k) : Finset (Fin m) :=
  Finset.univ.filter (fun g => σ g = i)

/-- Definition 1 (p. 2): the partition `σ` satisfies PROP-`c` for the valuations `μ` if for every
agent `(i, j)` there is a set `C ⊆ G \ B_i` with `|C| ≤ c` and
`μ_{(i,j)}(B_i) ≥ μ_{(i,j)}(G)/k − μ_{(i,j)}(C)`. The witness `C` may differ between agents. -/
def IsPROP {k : ℕ} {n : Fin k → ℕ} {m : ℕ} (c : ℕ) (μ : Valuation n m) (σ : Fin m → Fin k) :
    Prop :=
  ∀ (i : Fin k) (j : Fin (n i)), ∃ C : Finset (Fin m), (∀ g ∈ C, σ g ≠ i) ∧ C.card ≤ c ∧
    value μ i j Finset.univ / (k : ℝ) - value μ i j C ≤ value μ i j (bundle σ i)

/-- The integer `c` works for the group sizes `n`: for every finite set of goods and every
nonnegative additive valuation table there is a partition satisfying PROP-`c`. -/
def PROPAchievable {k : ℕ} (n : Fin k → ℕ) (c : ℕ) : Prop :=
  ∀ (m : ℕ) (μ : Valuation n m), IsNonneg μ → ∃ σ : Fin m → Fin k, IsPROP c μ σ

/-- Definition 1 (p. 2): `PROP(n_1, …, n_k)`, the smallest positive integer `c` such that for
`k` groups of sizes `n_1, …, n_k` with any valuations there is a partition satisfying PROP-`c`.
It is an infimum in `ℕ∞`: if no positive integer works the value is `⊤` (no junk `0`). -/
noncomputable def PROP {k : ℕ} (n : Fin k → ℕ) : ℕ∞ :=
  sInf {c : ℕ∞ | ∃ c' : ℕ, (c' : ℕ∞) = c ∧ 0 < c' ∧ PROPAchievable n c'}

end ProportionalGroupDivision.Main


