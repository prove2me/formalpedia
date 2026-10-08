-- Prove2me | Definitions.Def_LeightonRao_BadExample_Setting
-- name    : LeightonRao_BadExample_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:43.082989+00:00
-- url     : https://prove2.me/theorems/a124737e-2df2-4d81-98dc-e4b851557dc0
-- title:
--   §1.2, §1.5, §2.1, pp. 788–794 — network, cut capacity, uniform min-cut 𝒮, concurrent max-flow f, unit-capacity network, edge expansion
-- statement:
--   Let $V$ be a finite set of $n=|V|$ nodes. A **network** assigns to every pair of nodes a capacity $C(u,v)\ge 0$, symmetric in $u,v$ and zero on the diagonal; $\{u,v\}$ is an edge when $C(u,v)>0$. For $U\subseteq V$ with complement $\bar U$, the **cut capacity** is
--   $$C(U,\bar U)=\sum_{u\in U}\sum_{v\in\bar U}C(u,v),$$
--   the total capacity of the edges linking $U$ to $\bar U$. The network is **connected** if $C(U,\bar U)>0$ for every nonempty proper $U$ (the standing assumption of p. 789).
--
--   In the **uniform multicommodity flow problem** (UMFP) every pair of distinct nodes is a commodity with unit demand. Its **min-cut** (sparsest cut) is Eq. (1),
--   $$\mathcal S=\min_{\emptyset\ne U\subsetneq V}\frac{C(U,\bar U)}{|U|\,|\bar U|}.$$
--   A **concurrent flow of fraction** $f$ routes $f$ units of every commodity simultaneously: each commodity $(s,t)$ is a nonnegative arc flow $f_{st}(i\to j)$ obeying conservation with net supply $f\cdot D(s,t)$ at $s$ and net demand $f\cdot D(s,t)$ at $t$, and for every pair $i,j$ the total flow of all commodities in both directions over $\{i,j\}$ is at most $C(i,j)$. The **max-flow** is the largest such $f\ge 0$.
--
--   Given a simple graph $G$ on $V$, the **unit-capacity network** of $G$ has $C(u,v)=1$ if $uv$ is an edge of $G$ and $0$ otherwise, so $C(U,\bar U)=|\langle U,\bar U\rangle|$ is the number of edges between $U$ and $\bar U$. The graph is a **$c$-edge-expander** if
--   $$|\langle U,\bar U\rangle|\ \ge\ c\,\min\{|U|,|\bar U|\}\qquad\text{for all }U\subseteq V.$$
--
--   These are the objects of §2.1: the max-flow and min-cut of the UMFP on a 3-regular unit-capacity expander.
--
--   **Formalization Note** Commodities are ordered pairs $(s,t)$, $s\ne t$, each with demand $1/2$ (footnote 2, p. 791: "two commodities for every pair of nodes $u$ and $v$, with 1/2 unit of flow from $u$ to $v$ and 1/2 unit of flow from $v$ to $u$"), so every unordered pair carries one unit of demand. The minimum defining $\mathcal S$ ranges over nonempty proper $U$ only: at $U=\emptyset$ or $V$ the ratio is $0/0$, which Lean evaluates to $0$; the index type is nonempty exactly when $n\ge 2$. The max-flow is the supremum (`sSup`) of the feasible fractions; the set contains $0$ and is bounded above as soon as some commodity of positive demand is separated by a cut, which holds when $n\ge 2$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 788–789 (§1.1–1.2, concurrent max-flow, min-cut, connectivity assumption), p. 791 (footnote 2), p. 792 (§1.5, Eqs. (1), (2)), p. 794 (§2.1, expansion property)

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.BadExample

/-- An undirected capacitated network. A pair is an edge precisely when its capacity is
strictly positive. Parallel edges are represented by their summed capacity. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The capacity `C(U, Ū)` of the edges crossing a cut, each undirected edge counted once. -/
noncomputable def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The standing connectedness convention of p. 789: `C(U, Ū) > 0` for every nonempty
proper `U`. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

/-- The ratio cost `C(U, Ū)/(|U||Ū|)` of a cut. Used only for nonempty proper cuts, so the
denominator is positive. -/
noncomputable def ratioCost (N : Network V) (U : Finset V) : ℝ :=
  cutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))

/-- The uniform min-cut (sparsest cut) `𝒮` of Eq. (1). The minimum ranges over nonempty
proper `U` only (at `U = ∅` or `U = V` the ratio is `0/0`, which Lean reads as `0`). The
index type is nonempty and finite exactly when `2 ≤ Fintype.card V`, which every theorem
using `minCut` assumes. -/
noncomputable def minCut (N : Network V) : ℝ :=
  ⨅ U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}, ratioCost N U.1

/-- Concurrent arc flow of fraction `lam` for the demands `D`: one commodity per ordered
pair `(s, t)`, `f s t i j ≥ 0` its flow on the arc `i → j`; conservation with net supply
`lam * D s t` at `s`; the diagonal commodities carry no flow; both directions of an
undirected edge share its capacity. -/
def IsConcurrentFlow (N : Network V) (D : V → V → ℝ)
    (f : V → V → V → V → ℝ) (lam : ℝ) : Prop :=
  (∀ s t i j, 0 ≤ f s t i j) ∧
  (∀ s t, s ≠ t → ∀ v,
    (∑ j, f s t v j) - (∑ j, f s t j v) =
      lam * D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) ∧
  (∀ s i j, f s s i j = 0) ∧
  (∀ i j, ∑ s, ∑ t, (f s t i j + f s t j i) ≤ N.C i j)

/-- The concurrent max-flow `f`. The set contains `0`; when `2 ≤ Fintype.card V`, the
network is connected and some separated commodity has positive demand, a proper cut bounds
it above (weak duality), so the supremum is the maximum. -/
noncomputable def maxFlow (N : Network V) (D : V → V → ℝ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N D f lam}

/-- Uniform demands (footnote 2, p. 791): two ordered commodities of demand `1/2` for every
unordered pair of distinct nodes, i.e. one unit of demand per unordered pair. -/
noncomputable def uniformDemand (s t : V) : ℝ := if s = t then 0 else 1 / 2

/-- The network of a simple graph with unit edge capacities: `C(u, v) = 1` if `uv` is an
edge and `0` otherwise. Its cut capacity `cutCap (unitNetwork G) U` is `|⟨U, Ū⟩|`, the
number of edges between `U` and `Ū`. -/
def unitNetwork (G : SimpleGraph V) [DecidableRel G.Adj] : Network V where
  C u v := if G.Adj u v then 1 else 0
  C_nonneg u v := by split_ifs <;> norm_num
  C_symm u v := by simp only [G.adj_comm]
  C_self u := by simp

/-- The expansion property of §2.1, p. 794: `|⟨U, Ū⟩| ≥ c · min{|U|, |Ū|}` for all
`U ⊆ V`. -/
def IsEdgeExpander (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  ∀ U : Finset V, c * ((min U.card Uᶜ.card : ℕ) : ℝ) ≤ cutCap (unitNetwork G) U

end LeightonRao.BadExample


