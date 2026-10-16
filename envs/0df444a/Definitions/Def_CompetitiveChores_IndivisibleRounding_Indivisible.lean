-- Prove2me | Definitions.Def_CompetitiveChores_IndivisibleRounding_Indivisible
-- name    : CompetitiveChores_IndivisibleRounding_Indivisible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:31.189814+00:00
-- url     : https://prove2.me/theorems/21331a20-a632-492b-bf8f-4453c3408b5f
-- title:
--   pp. 36–38 — indivisible allocations, weighted-EF¹₁ (Definition 32) and weighted-Prop1 (Definition 33)
-- statement:
--   Indivisible allocations of chores and the two relaxed fairness notions of §7 (pp. 36–37).
--
--   An allocation $z$ is **indivisible** if every $z_{i,j}$ is $0$ or $1$. A feasible indivisible allocation assigns each chore $j$ to one agent $\sigma(j)$, and the bundle $z_i$ is identified with the set of chores $\{j:\sigma(j)=i\}$. For a set $S$ of chores, $u_i(S)=\sum_{j\in S}v_{i,j}$ and its price is $\sum_{c\in S}p_c$.
--
--   Let $\beta\in\mathbb R^n_{>0}$ be a weight vector.
--
--   1. **Definition 32 (weighted-EF¹₁).** $z$ is weighted envy-free up to the removal of a chore from the first bundle and the addition of another chore to the other bundle if for any agents $i$ with non-empty $z_i$ and $i'$ there are chores $j\in z_i$ and $j'\in[m]$ with
--   $$\frac{u_i(z_i\setminus\{j\})}{\beta_i}\ \ge\ \frac{u_i(z_{i'}\cup\{j'\})}{\beta_{i'}}.\qquad(10)$$
--   2. **Definition 33 (weighted-Prop1).** $z$ is weighted-proportional up to one chore if for each agent $i$ with non-empty $z_i$ there is a chore $j\in z_i$ with
--   $$\frac{u_i(z_i\setminus\{j\})}{\beta_i}\ \ge\ \frac{u_i([m])}{\sum_{i'=1}^n\beta_{i'}}.\qquad(11)$$
--
--   These are the fairness guarantees of Theorem 34.
--
--   **Formalization Note** An indivisible feasible allocation is a map $\sigma:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$; `indicator σ` is the corresponding 0/1 matrix, so it can be fed to the divisible notions (utility profile, competitiveness). In (10) the pair $(i,i')$ ranges over all ordered pairs, $i'=i$ included, and $j'$ over all chores, as on the page; $z_{i'}\cup\{j'\}$ is `insert j' (bundle σ i')`. The weights are arbitrary positive reals, not normalized.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 36 (indivisible allocations), p. 36 Definition 32 (10), p. 37 Definition 33 (11)

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting

namespace CompetitiveChores.IndivisibleRounding

open Classical

variable {n m : ℕ}

/-- p. 36: the indivisible allocation in which chore `j` goes entirely to agent `σ j`, as a matrix:
`z_{i,j} = 1` if `σ j = i` and `z_{i,j} = 0` otherwise. Every indivisible feasible allocation is of
this form. -/
noncomputable def indicator (σ : Fin m → Fin n) : Fin n → Fin m → ℝ :=
  fun i j => if σ j = i then 1 else 0

/-- p. 36: the bundle of agent `i` in the indivisible allocation `σ`, identified with the set of chores
consumed by `i`. -/
noncomputable def bundle (σ : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => σ j = i)

/-- p. 36: the utility `u_i(S) = ∑_{j ∈ S} v_{i,j}` of agent `i` for a set `S` of chores. -/
def setUtility (v : Fin n → Fin m → ℝ) (i : Fin n) (S : Finset (Fin m)) : ℝ :=
  ∑ j ∈ S, v i j

/-- p. 38: the price `∑_{c ∈ S} p_c` of a set `S` of chores. -/
def setPrice (p : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ j ∈ S, p j

/-- Definition 32, p. 36 (weighted-EF¹₁): for every pair of agents `i` with non-empty bundle `z_i` and
`i'` there are chores `j ∈ z_i` and `j' ∈ [m]` with
`u_i(z_i ∖ {j}) / β_i ≥ u_i(z_{i'} ∪ {j'}) / β_{i'}` (inequality (10)). -/
def IsWeightedEF11 (v : Fin n → Fin m → ℝ) (β : Fin n → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i i', (bundle σ i).Nonempty → ∃ j ∈ bundle σ i, ∃ j' : Fin m,
    setUtility v i (insert j' (bundle σ i')) / β i' ≤ setUtility v i ((bundle σ i).erase j) / β i

/-- Definition 33, p. 37 (weighted-Prop1): for each agent `i` with non-empty bundle `z_i` there is a
chore `j ∈ z_i` with `u_i(z_i ∖ {j}) / β_i ≥ u_i([m]) / ∑_{i'} β_{i'}` (inequality (11)). -/
def IsWeightedProp1 (v : Fin n → Fin m → ℝ) (β : Fin n → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i, (bundle σ i).Nonempty → ∃ j ∈ bundle σ i,
    setUtility v i Finset.univ / ∑ i', β i' ≤ setUtility v i ((bundle σ i).erase j) / β i

end CompetitiveChores.IndivisibleRounding


