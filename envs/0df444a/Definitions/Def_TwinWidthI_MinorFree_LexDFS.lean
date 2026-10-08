-- Prove2me | Definitions.Def_TwinWidthI_MinorFree_LexDFS
-- name    : TwinWidthI_MinorFree_LexDFS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:02.326302+00:00
-- url     : https://prove2.me/theorems/6e9439b2-258a-4ec0-a286-fa3f18b1e147
-- title:
--   p. 3:26 — DFS discovery orders, the Lex-DFS of Theorem 6.3, ancestors and minimal subtrees
-- statement:
--   Let $G$ be a finite graph on $n$ vertices. A **discovery order** lists the vertices as $v_1,\dots,v_n$; at time $k$ the vertices $v_1,\dots,v_k$ are **discovered**. The **active vertex** at time $k$ is the lastly discovered vertex which still has at least one undiscovered neighbour. A **depth-first search** (DFS) is a discovery order together with a parent map (the **DFS tree** $\mathcal T$) such that the root $v_1$ is its own parent and every later vertex $v_{k+1}$ is a neighbour of the active vertex at time $k$, which is its parent. A DFS exists only when $G$ is connected.
--
--   The **Lex-DFS** of the proof of Theorem 6.3 breaks ties as follows. At time $k$, with active vertex $v$, let $C_1,\dots,C_s$ be the connected components of $G-\{v_1,\dots,v_k\}$ meeting $N_G(v)$. The **word** of a component $C$ is $w_k(C)\in\{0,1\}^k$, whose $j$-th letter is $1$ iff $v_j$ has a neighbour in $C$. The next vertex $v_{k+1}$ must lie in a component $C_i\cap N_G(v)$ whose word is lexicographically maximal (with $0<1$):
--
--   $$
--   w_k(C_j)\le_{\mathrm{lex}} w_k(C_i)\qquad\text{for every } j\in[s].
--   $$
--
--   Informally, the search first visits the component whose neighbours appear first in the current discovery order.
--
--   In the DFS tree, $u$ is an **ancestor** of $w$ (possibly $u=w$) if $u$ is obtained from $w$ by following parents; the subtree $\mathcal T[u]$ consists of the descendants of $u$. The **minimal subtree** of $\mathcal T$ containing a set $S$ is the union of the tree paths between pairs of elements of $S$; a vertex $x$ lies on the path from $s$ to $s'$ iff $x$ is an ancestor of $s$ and a descendant of the lowest common ancestor of $s$ and $s'$.
--
--   These objects carry Lemmas 6.4–6.6 and the grid-free statement of the proof of Theorem 6.3.
--
--   **Formalization Note** The discovery order is an equivalence $\sigma:V\simeq\mathrm{Fin}\,n$ with $v_{j+1}=\sigma^{-1}(j)$ (0-indexed), and the DFS tree is a parent map with the root fixed. The components of $G-V(\mathcal T_k)$ are encoded by reachability in the graph on $V$ whose edges are the edges of $G$ between undiscovered vertices; a component meets $N_G(v)$ iff it contains an undiscovered neighbour $u$ of $v$, so the tie-break compares the word of $u$'s component with that of the new vertex's component for every such $u$. Words are `List Bool`, compared by Lean's lexicographic order with `false < true`; all compared words have length $k$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:26, proof of Theorem 6.3, "Definition of the appropriate Lex-DFS"; p. 3:27, minimal subtrees A′_i, B∗_j

import Mathlib

namespace TwinWidthI.MinorFree

variable {V : Type*}

/-- p. 3:26: at time `k` (the vertices `u` with `σ u < k` have been discovered), `u` is the
**active vertex**: the lastly discovered vertex which still has at least one undiscovered
neighbour. -/
def IsActive (G : SimpleGraph V) {n : ℕ} (σ : V ≃ Fin n) (k : ℕ) (u : V) : Prop :=
  (σ u : ℕ) < k ∧ (∃ w, k ≤ (σ w : ℕ) ∧ G.Adj u w) ∧
    ∀ u', (σ u' : ℕ) < k → (∃ w, k ≤ (σ w : ℕ) ∧ G.Adj u' w) → σ u' ≤ σ u

/-- p. 3:26: `σ` (the discovery order, `v_1, …, v_n` read as `σ⁻¹ 0, …, σ⁻¹ (n-1)`) together
with the parent map `par` (the DFS tree `𝒯`) is a depth-first search: the root `σ⁻¹ 0` is its
own parent, and every later vertex `v` is a neighbour of the vertex that is active at the moment
`v` is discovered, which is its parent in the DFS tree. -/
def IsDFSOrder (G : SimpleGraph V) {n : ℕ} (σ : V ≃ Fin n) (par : V → V) : Prop :=
  ∀ v, ((σ v : ℕ) = 0 → par v = v) ∧
    (0 < (σ v : ℕ) → IsActive G σ (σ v) (par v) ∧ G.Adj (par v) v)

/-- The graph `G − V(𝒯_k)` on the undiscovered vertices `{u | k ≤ σ u}`, kept on the vertex
type `V`: two vertices are adjacent iff both are undiscovered and adjacent in `G`. -/
def undiscGraph (G : SimpleGraph V) {n : ℕ} (σ : V ≃ Fin n) (k : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ k ≤ (σ x : ℕ) ∧ k ≤ (σ y : ℕ)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

open Classical in
/-- p. 3:26: the word `w_k(C) ∈ {0,1}^k` of the connected component `C` of `G − V(𝒯_k)`
containing the undiscovered vertex `x` (with `k = σ v` for a vertex `v`, so that `k < n`): its
`j`-th letter (`j < k`) is `true` iff the `j`-th discovered vertex `σ⁻¹ j` has a neighbour
in `C`. -/
noncomputable def compWord (G : SimpleGraph V) {n : ℕ} (σ : V ≃ Fin n) (v x : V) : List Bool :=
  List.ofFn fun j : Fin (σ v : ℕ) =>
    decide (∃ c, (σ v : ℕ) ≤ (σ c : ℕ) ∧ (undiscGraph G σ (σ v)).Reachable x c ∧
      G.Adj c (σ.symm ⟨j, j.isLt.trans (σ v).isLt⟩))

/-- p. 3:26: the Lex-DFS of the proof of Theorem 6.3. It is a DFS (`IsDFSOrder`) in which every
newly discovered vertex `v` (at time `k = σ v`, with active vertex `par v`) lies in a
component of `G − V(𝒯_k)` whose word is lexicographically maximal (`0 < 1`) among the words of
the components meeting `N_G(par v)`; a component meets `N_G(par v)` iff it contains an
undiscovered neighbour `u` of `par v`. -/
def IsLexDFSOrder (G : SimpleGraph V) {n : ℕ} (σ : V ≃ Fin n) (par : V → V) : Prop :=
  IsDFSOrder G σ par ∧
    ∀ v, 0 < (σ v : ℕ) → ∀ u, (σ v : ℕ) ≤ (σ u : ℕ) → G.Adj (par v) u →
      compWord G σ v u ≤ compWord G σ v v

/-- The DFS tree: `u` is an ancestor of `w` (possibly `u = w`) iff `u = par^[i] w` for some
`i`. `T[u] = {w | IsAncestor par u w}` is the subtree rooted at `u`. -/
def IsAncestor (par : V → V) (u w : V) : Prop := ∃ i : ℕ, par^[i] w = u

/-- pp. 3:27: the vertex set of the minimal subtree of the DFS tree containing `S`: the union of
the tree paths between two elements `s, s'` of `S`. A vertex `x` is on the path from `s` to `s'`
iff it is an ancestor of `s` (or of `s'`, by symmetry) and a descendant of every common ancestor
of `s` and `s'`, i.e. it lies between `s` and their lowest common ancestor. -/
def MinSubtree (par : V → V) (S : Set V) : Set V :=
  {x | ∃ s ∈ S, ∃ s' ∈ S, IsAncestor par x s ∧
    ∀ y, IsAncestor par y s → IsAncestor par y s' → IsAncestor par y x}

end TwinWidthI.MinorFree


