-- Prove2me | Definitions.Def_CycleLengthsExp_WellSpread_Setting
-- name    : CycleLengthsExp_WellSpread_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:23.75676+00:00
-- url     : https://prove2.me/theorems/b11a4bbb-a84c-433e-b23b-d2ca0781b3cc
-- title:
--   pp. 1–4 — external neighborhood, (k,α)-expander, α-expander, cycle lengths L(G), balls, contraction, tree levels
-- statement:
--   Let $G=(V,E)$ be a finite simple graph on $n=|V|$ vertices.
--
--   1. **External neighborhood.** For $U\subseteq V$, $N_G(U)=\{v\in V\setminus U : v \text{ has a neighbor in } U\}$.
--   2. **$(k,\alpha)$-expander.** For reals $k,\alpha$, $G$ is a $(k,\alpha)$-expander if $|N_G(U)|\ge \alpha|U|$ for every $U\subseteq V$ with $|U|\le k$.
--   3. **$\alpha$-expander.** $G$ is an $\alpha$-expander if $|N_G(U)|\ge\alpha|U|$ for every $U\subseteq V$ with $|U|\le\lceil n/2\rceil$.
--   4. **Cycle lengths.** $L(G)=\{\ell : G \text{ contains a cycle of length } \ell\}$, where a cycle is a closed walk of length at least $3$ with no repeated edge and no repeated vertex other than its endpoints.
--   5. **Ball.** For $v\in V$ and an integer $r\ge0$, $B_G(v,r)$ is the set of vertices joined to $v$ by a walk with at most $r$ edges, i.e. $\{w : \operatorname{dist}_G(v,w)\le r\}$ with unreachable vertices excluded.
--   6. **Contraction.** For a map $f:V\to\{1,\dots,r\}$ (a partition of $V$ into the fibres $V_i=f^{-1}(i)$), the contracted graph $G'$ on $\{1,\dots,r\}$ joins $i\ne j$ exactly when some edge of $G$ goes between $V_i$ and $V_j$.
--   7. **Levels of a rooted tree.** For a subgraph $T$ of $G$ and a root $v_0$, the level of a vertex $v$ of $T$ is $1+\operatorname{dist}_T(v_0,v)$, so $L_1=\{v_0\}$; and $T_{[j_1,j_2]}=\bigcup_{i=j_1}^{j_2}L_i$.
--
--   These are the objects in which Theorem 1 and Lemmas 2.1–2.7 are stated.
--
--   **Formalization Note.** Sizes are `Set.ncard`. The positivity of $k$ and $\alpha$ is a hypothesis of each theorem, not part of the definitions. $\lceil n/2\rceil$ is the natural-number expression $(n+1)/2$. The $(k,\alpha)$-expander predicate carries no `Fintype` instance so that it applies to induced graphs on subtypes; every use is on a finite vertex type. Tree distance is the distance in the spanning graph of $T$'s edges; on a tree containing $v_0$ and $v$ it is the distance inside $T$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, pp. 1–4: §1 (external neighborhood p. 1, Definition of α-expander and L(G) p. 2), Notation and terminology (p. 4: balls, levels T_[j1,j2]), §2 Definition of (k,α)-expander (p. 4), Lemma 2.4 (p. 6: contraction)

import Mathlib

namespace CycleLengthsExp.WellSpread

/-- External vertex neighborhood `N_G(U)`, Friedman–Krivelevich, p. 1. -/
def extNbhd {V : Type*} (G : SimpleGraph V) (U : Set V) : Set V :=
  {v | v ∉ U ∧ ∃ u ∈ U, G.Adj u v}

/-- The `(k, α)` vertex-expansion condition of p. 4. Positivity belongs to the theorems.
No `Fintype` instance is required, so that it applies to induced graphs `G.induce U` on a
subtype; every use in this mission is on a finite vertex type, where `Set.ncard` is the
cardinality. -/
def IsKAlphaExpander {V : Type*} (k α : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ U : Set V, (U.ncard : ℝ) ≤ k → α * U.ncard ≤ (extNbhd G U).ncard

/-- The p. 2 definition uses the ceiling of half the vertex count. -/
def IsAlphaExpander {V : Type*} [Fintype V] (α : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ U : Set V, U.ncard ≤ (Fintype.card V + 1) / 2 →
    α * U.ncard ≤ (extNbhd G U).ncard

/-- `L(G)`, the set of lengths of simple cycles, p. 2. -/
def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {ℓ | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = ℓ}

/-- The ball `B_G(v, r)` of p. 4: vertices joined to `v` by a walk with at most `r` edges.
Unreachable vertices are never in the ball. -/
def ball {V : Type*} (G : SimpleGraph V) (v : V) (r : ℕ) : Set V :=
  {w | ∃ p : G.Walk v w, p.length ≤ r}

/-- The graph obtained by contracting each fibre of `f : V → Fin r` to one vertex
(Lemma 2.4, p. 6): distinct parts are adjacent iff some edge of `G` joins them. -/
def contract {V : Type*} (G : SimpleGraph V) {r : ℕ} (f : V → Fin r) : SimpleGraph (Fin r) where
  Adj i j := i ≠ j ∧ ∃ u v, f u = i ∧ f v = j ∧ G.Adj u v
  symm := ⟨by
    rintro i j ⟨hij, u, v, hu, hv, huv⟩
    exact ⟨hij.symm, v, u, hv, hu, huv.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The level of `v` in a subgraph `T` rooted at `v₀`: one plus the distance from `v₀`
using edges of `T` only, so that the root is on level `1` (p. 4, Lemma 2.7). -/
noncomputable def level {V : Type*} {G : SimpleGraph V} (T : G.Subgraph) (v₀ v : V) : ℕ :=
  T.spanningCoe.dist v₀ v + 1

/-- `T_[j₁, j₂]`: the vertices of `T` on levels `j₁, …, j₂` (p. 4). -/
def levelSet {V : Type*} {G : SimpleGraph V} (T : G.Subgraph) (v₀ : V) (j₁ j₂ : ℕ) : Set V :=
  {v | v ∈ T.verts ∧ j₁ ≤ level T v₀ v ∧ level T v₀ v ≤ j₂}

end CycleLengthsExp.WellSpread


