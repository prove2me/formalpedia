-- Prove2me | Definitions.Def_CircStability_Bondy_Setting
-- name    : CircStability_Bondy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:41:55.033258+00:00
-- url     : https://prove2.me/theorems/47de9f02-a535-4a10-8464-f2555e687fe5
-- title:
--   pp. 1–3, 6 — 2-connectivity, longest cycles, edges off a cycle, components of G − C, W_{n,k,c}, X_{n,c}, Y_{n,c}
-- statement:
--   All graphs are finite and simple, with vertex set $\{0,1,\dots,n-1\}$. A path or cycle of length $k$ has $k$ edges.
--
--   1. **2-connected.** A graph is 2-connected if it has at least three vertices, is connected, and remains connected after the deletion of any single vertex.
--   2. **Longest cycle.** A cycle $C$ of $G$ is a longest cycle if no cycle of $G$ has more edges than $C$. Its vertex set is $V(C)$.
--   3. **Edges off a cycle.** For a vertex set $S$ (in practice $S = V(C)$), $e(G-S)+e(G-S,S)$ is the number of edges of $G$ having at most one endpoint in $S$.
--   4. **Component of $G - S$.** A nonempty vertex set $R$ disjoint from $S$ such that $G[R]$ is connected and every neighbour of a vertex of $R$ lies in $R \cup S$.
--   5. **The graph $W_{n,k,c}$.** Take a clique $K_{c-k+1}$ and add $n-(c-k+1)$ further vertices, each joined to the same $k$ vertices of the clique and to nothing else. Concretely, the vertices $0,\dots,c-k$ form the clique, the vertices $0,\dots,k-1$ are the $k$ hubs, and the vertices $c-k+1,\dots,n-1$ are the outer vertices.
--   6. **The family $\mathcal X_{n,c}$.** A graph $H$ on $n$ vertices belongs to $\mathcal X_{n,c}$ if $V(H) = A \cup B \cup X$ (disjoint), where $H[A]$ is a clique on $\lfloor c/2\rfloor$ vertices, $B$ and $X$ are stable, every vertex of $A$ is adjacent to every vertex of $B$, and there are $a \in A$, $b \in B$ with $N_H(x) = \{a,b\}$ for every $x \in X$.
--   7. **The family $\mathcal Y_{n,c}$.** A graph $H$ on $n$ vertices belongs to $\mathcal Y_{n,c}$ if $V(H) = A \cup B \cup Y$ (disjoint), where $H[A]$ is a clique on $\lfloor c/2\rfloor$ vertices, $B$ is stable, $(A,B)$ is complete bipartite, $H[Y]$ is a nontrivial star forest (at least two stars, each with at least one edge), and there are two distinct vertices $a,b \in A$ such that every star $S$ of $H[Y]$ is $\{a,b\}$-feasible: the set of vertices outside $S$ with a neighbour in $S$ is exactly $\{a,b\}$, and if $|V(S)| \ge 3$ then every leaf of $S$ has degree $2$ in $H$ and all leaves have a common neighbour in $\{a,b\}$.
--
--   These are the objects in which the stability version of Bondy's circumference theorem and its supporting lemmas are stated. "$G \subseteq W_{n,k,c}$" means that $G$ is isomorphic to a subgraph of $W_{n,k,c}$; "$G$ is a subgraph of a member of $\mathcal X_{n,c} \cup \mathcal Y_{n,c}$" means $G \le H$ for some $H$ in one of the two families, both of which are closed under relabelling.
--
--   **Formalization Note** Graphs are `SimpleGraph (Fin n)`. 2-connectivity is defined for any finite vertex type (so that it applies to induced subgraphs) as: at least three vertices, connected, and connected after deleting any one vertex. This is vertex connectivity at least $2$, the standard definition, and excludes $K_2$ and disconnected graphs. A longest cycle is a closed walk that is a cycle and is at least as long as every cycle of $G$; no supremum of cycle lengths is used. The phrase "two vertices $a,b\in A$" in $\mathcal Y_{n,c}$ is read as two distinct vertices, and the stars of $H[Y]$ are given as an explicit partition of $Y$ with a centre in each part. The edge count and the degree in $\mathcal Y_{n,c}$ use classical decidability.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, pp. 1–3, §1 (circumference p. 1; W_{n,k,c} p. 2; X_{n,c}, Y_{n,c} and footnote 4 p. 3) and p. 6, §2.1 (notation)

import Mathlib

namespace CircStability.Bondy

open SimpleGraph Finset

/-- A finite simple graph is 2-connected when it has at least three vertices, is connected,
and stays connected after deleting any one vertex (vertex connectivity at least 2). -/
def TwoConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧ ∀ v : V, (G.induce {w : V | w ≠ v}).Connected

/-- `C` is a longest cycle of `G`: it is a cycle, and no cycle of `G` is longer. -/
def IsLongestCycle {n : ℕ} (G : SimpleGraph (Fin n)) {u : Fin n} (C : G.Walk u u) : Prop :=
  C.IsCycle ∧ ∀ (v : Fin n) (D : G.Walk v v), D.IsCycle → D.length ≤ C.length

/-- The vertex set `V(C)` of a closed walk `C`. -/
def cycleVerts {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} (C : G.Walk u u) :
    Finset (Fin n) :=
  C.support.toFinset

open Classical in
/-- `e(G − S) + e(G − S, S)`: the number of edges of `G` with at most one endpoint in `S`. -/
noncomputable def edgesOffCycle {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  #(G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∉ S))

/-- `R` is (the vertex set of) a connected component of `G − S`. -/
def IsComponentOff {n : ℕ} (G : SimpleGraph (Fin n)) (S R : Finset (Fin n)) : Prop :=
  R.Nonempty ∧ Disjoint R S ∧ (G.induce (R : Set (Fin n))).Connected ∧
    ∀ v ∈ R, ∀ w, G.Adj v w → w ∈ R ∨ w ∈ S

/-- The graph `W_{n,k,c}` on `Fin n`: the vertices `< c − k + 1` form a clique `K_{c−k+1}`,
and each of the remaining `n − (c − k + 1)` vertices is joined exactly to the `k` hub
vertices `< k`. -/
def wGraph (n k c : ℕ) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ (((v : ℕ) < c - k + 1 ∧ (w : ℕ) < c - k + 1) ∨
    ((v : ℕ) < k ∧ c - k + 1 ≤ (w : ℕ)) ∨ ((w : ℕ) < k ∧ c - k + 1 ≤ (v : ℕ)))
  symm := ⟨fun v w h => by
    refine ⟨fun e => h.1 e.symm, ?_⟩
    rcases h.2 with h2 | h2 | h2
    · exact Or.inl ⟨h2.2, h2.1⟩
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h2)⟩
  loopless := ⟨fun v h => h.1 rfl⟩

instance (n k c : ℕ) : DecidableRel (wGraph n k c).Adj := fun v w => by
  unfold wGraph; infer_instance

/-- Membership in the family `X_{n,c}` (p. 3): `V = A ∪ B ∪ X` (disjoint), `A` a clique of
size `⌊c/2⌋`, `B` and `X` stable, `(A, B)` complete bipartite, and two vertices `a ∈ A`,
`b ∈ B` with `N(x) = {a, b}` for every `x ∈ X`. -/
def IsXMember (n c : ℕ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ A B X : Finset (Fin n), Disjoint A B ∧ Disjoint A X ∧ Disjoint B X ∧ A ∪ B ∪ X = univ ∧
    #A = c / 2 ∧ (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → H.Adj a a') ∧
    (∀ b ∈ B, ∀ b' ∈ B, ¬ H.Adj b b') ∧ (∀ x ∈ X, ∀ x' ∈ X, ¬ H.Adj x x') ∧
    (∀ a ∈ A, ∀ b ∈ B, H.Adj a b) ∧
    ∃ a ∈ A, ∃ b ∈ B, ∀ x ∈ X, H.neighborSet x = {a, b}

open Classical in
/-- Membership in the family `Y_{n,c}` (p. 3): `V = A ∪ B ∪ Y` (disjoint), `A` a clique of
size `⌊c/2⌋`, `B` stable, `(A, B)` complete bipartite, `H[Y]` a nontrivial star forest (at
least two stars, each with at least one edge), and two distinct vertices `a, b ∈ A` such that
every star `S` is `{a, b}`-feasible: `N_H(S) = {a, b}`, and if `|S| ≥ 3` then every leaf of `S`
has degree 2 in `H` and all leaves share a neighbour in `{a, b}`. -/
def IsYMember (n c : ℕ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ A B Y : Finset (Fin n), Disjoint A B ∧ Disjoint A Y ∧ Disjoint B Y ∧ A ∪ B ∪ Y = univ ∧
    #A = c / 2 ∧ (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → H.Adj a a') ∧
    (∀ b ∈ B, ∀ b' ∈ B, ¬ H.Adj b b') ∧ (∀ a ∈ A, ∀ b ∈ B, H.Adj a b) ∧
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧
    ∃ P : Finset (Finset (Fin n)), 2 ≤ #P ∧ (∀ y ∈ Y, ∃! S, S ∈ P ∧ y ∈ S) ∧ (∀ S ∈ P, S ⊆ Y) ∧
      (∀ S ∈ P, ∀ S' ∈ P, S ≠ S' → ∀ y ∈ S, ∀ y' ∈ S', ¬ H.Adj y y') ∧
      ∀ S ∈ P, ∃ z ∈ S, 2 ≤ #S ∧ (∀ y ∈ S, y ≠ z → H.Adj z y) ∧
        (∀ y ∈ S, ∀ y' ∈ S, y ≠ z → y' ≠ z → ¬ H.Adj y y') ∧
        {w | w ∉ S ∧ ∃ y ∈ S, H.Adj y w} = ({a, b} : Set (Fin n)) ∧
        (3 ≤ #S → ∃ t, (t = a ∨ t = b) ∧ ∀ y ∈ S, y ≠ z → H.degree y = 2 ∧ H.Adj y t)

end CircStability.Bondy


