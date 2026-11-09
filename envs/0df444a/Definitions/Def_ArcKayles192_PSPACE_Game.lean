-- Prove2me | Definitions.Def_ArcKayles192_PSPACE_Game
-- name    : ArcKayles192_PSPACE_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:29.944696+00:00
-- url     : https://prove2.me/theorems/a99c9285-3404-4da0-b675-e512654751ac
-- title:
--   Arc Kayles under normal play: positions, outcome, mex, Sprague–Grundy value, disjoint unions, graph instances and their encoding
-- statement:
--   **Arc Kayles** is played on a finite simple graph. Two players alternate; a move picks an edge $uv$ of the current graph and deletes both endpoints $u$ and $v$. Under **normal play** the first player without a legal move (the current graph is edgeless) loses.
--
--   1. **Positions.** Fix an ambient simple graph $G$ on a vertex type with decidable equality. A position is a finite set $S$ of remaining vertices; the current graph is the induced subgraph $G[S]$. A legal move from $S$ is a pair $u,v\in S$ with $uv\in E(G)$, and it leads to $S\setminus\{u,v\}$. Isolated vertices are kept in $S$; they carry no move.
--   2. **Outcome.** $\mathrm{FirstPlayerWins}(G,S)$ is defined by backward induction on $|S|$:
--   $$\mathrm{FirstPlayerWins}(G,S)\iff \exists\,u,v\in S,\ uv\in E(G),\ \neg\,\mathrm{FirstPlayerWins}(G,S\setminus\{u,v\}).$$
--   It says that the player to move has a winning strategy. $S$ is an **N-position** when it holds and a **P-position** when it fails.
--   3. **mex and Sprague–Grundy value.** For $T\subseteq\mathbb N$, $\mathrm{mex}(T)=\min\{n\in\mathbb N : n\notin T\}$ (taken as an infimum, applied only to finite $T$). The Sprague–Grundy value is
--   $$\mathrm{sg}(G,S)=\mathrm{mex}\{\mathrm{sg}(G,S\setminus\{u,v\}) : u,v\in S,\ uv\in E(G)\},$$
--   so an edgeless position has value $0$.
--   4. **Disjoint union.** For a family of graphs $G_i$ on vertex types $W_i$, $G_1\uplus\cdots\uplus G_h$ is the graph on the disjoint union $\Sigma_i W_i$ in which two vertices are adjacent iff they lie in the same summand and are adjacent there.
--   5. **The function** $g(a,b)=(a+b)\bmod 2+2\cdot(\min(a,b)\bmod 2)$ of Lemma 6.
--   6. **The decision problem.** A graph instance is a number $n$ of vertices $0,\dots,n-1$ with a symmetric, irreflexive Boolean adjacency matrix. Its encoding is $1^n\,0$ followed by the $n^2$ adjacency bits row by row (length $n^2+n+1$). The problem ARC KAYLES asks whether $\mathrm{FirstPlayerWins}(G,V(G))$ holds for the instance's graph $G$.
--
--   These objects carry the whole game layer of the mission: outcomes, values and the instance format used by both halves of Theorem 1.
--
--   **Formalization Note** The ambient vertex type need not be finite, because positions are finite sets. The `mex` is `sInf` of the complement; the option set is finite (a finite family indexed by pairs of vertices of $S$), so the complement is nonempty and the infimum is attained.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.1 (game, normal play), p.2 §2.1 (sg, mex, N-/P-positions), p.3 (isolated vertices, ⊎, ⊕), p.4 Lemma 6 (g(a,b))

import Mathlib

namespace ArcKayles192.PSPACE

/-! # Arc Kayles under normal play: positions, outcomes, Sprague–Grundy values

A position of Arc Kayles on an ambient simple graph `G` is the finite set `S` of remaining
vertices; the current graph is the induced subgraph `G[S]`. A move picks an edge `uv` with
`u, v ∈ S` and leads to `S \ {u, v}`. Isolated vertices are kept in `S`; they carry no move. -/

section Game

variable {V : Type*} [DecidableEq V]

/-- Removing two vertices, one of which lies in `S`, strictly shrinks `S`. -/
theorem card_sdiff_pair_lt {S : Finset V} {u : V} (v : V) (hu : u ∈ S) :
    (S \ {u, v}).card < S.card := by
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset, fun h => ?_⟩
  have := h hu
  simp at this

/-- **Normal play outcome.** `FirstPlayerWins G S` holds when the player to move at the position
`S` (current graph `G[S]`) has a winning strategy in Arc Kayles under normal play (the first
player without a legal move loses). Defined by backward induction on `|S|`: the player to move
wins iff some legal move `uv` (an edge of `G` with both ends in `S`) leads to a position from
which the opponent, then to move, does not win. A position with no legal move is lost for the
player to move. An N-position is one with `FirstPlayerWins`; a P-position is one without. -/
def FirstPlayerWins (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, ¬ FirstPlayerWins G (S \ {u, v})
termination_by S.card
decreasing_by all_goals (rename_i h; exact card_sdiff_pair_lt _ h.1)

/-- The minimum excluded value `mex T = min {n ∈ ℕ | n ∉ T}`. It is applied below only to finite
sets `T`, whose complement is nonempty. -/
noncomputable def mex (T : Set ℕ) : ℕ := sInf Tᶜ

/-- **Sprague–Grundy value** of the position `S`:
`sg(G[S]) = mex {sg(G[S \ {u, v}]) | uv an edge of G[S]}`. The set of option values is finite,
so the `mex` is attained; the edgeless position has value `0`. -/
noncomputable def sg (G : SimpleGraph V) (S : Finset V) : ℕ :=
  mex {x | ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, sg G (S \ {u, v}) = x}
termination_by S.card
decreasing_by all_goals (rename_i h; exact card_sdiff_pair_lt _ h.1)

end Game

/-- The disjoint union `G₁ ⊎ ⋯ ⊎ G_h` of a family of graphs, on the sigma type: two vertices are
adjacent iff they lie in the same summand and are adjacent there. -/
def sigmaGraph {ι : Type*} {W : ι → Type*} (G : ∀ i, SimpleGraph (W i)) :
    SimpleGraph (Σ i, W i) :=
  SimpleGraph.fromRel fun a b => ∃ (i : ι) (x y : W i), a = ⟨i, x⟩ ∧ b = ⟨i, y⟩ ∧ (G i).Adj x y

/-- `g(a, b) = (a + b) mod 2 + 2 · (min(a, b) mod 2)`, the value of Lemma 6. -/
def g (a b : ℕ) : ℕ := (a + b) % 2 + 2 * (min a b % 2)

/-! ## Graph instances and the decision problem ARC KAYLES -/

/-- A finite simple graph on the vertices `0, …, n-1`, given by a symmetric irreflexive
Boolean adjacency matrix. -/
structure GraphInstance : Type where
  /-- number of vertices -/
  n : ℕ
  /-- adjacency matrix -/
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irrefl : ∀ i, adj i i = false

/-- The simple graph of an instance. -/
def GraphInstance.graph (I : GraphInstance) : SimpleGraph (Fin I.n) where
  Adj i j := I.adj i j = true
  symm := ⟨fun i j (h : I.adj i j = true) => by rw [I.symm]; exact h⟩
  loopless := ⟨fun i (h : I.adj i i = true) => by rw [I.irrefl] at h; exact Bool.false_ne_true h⟩

/-- The standard binary encoding of a graph instance: `n` in unary (`n` ones), a separator `0`,
then the `n²` adjacency bits in row-major order. Its length is `n² + n + 1`. -/
def GraphInstance.enc (I : GraphInstance) : List Bool :=
  List.replicate I.n true ++ [false] ++
    (List.finRange I.n).flatMap fun i => (List.finRange I.n).map fun j => I.adj i j

/-- The decision problem ARC KAYLES: does the player to move (the first player) win Arc Kayles
under normal play on the whole graph of the instance? -/
def arcKayles (I : GraphInstance) : Prop :=
  FirstPlayerWins I.graph Finset.univ

end ArcKayles192.PSPACE


