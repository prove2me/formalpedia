-- Prove2me | Definitions.Def_CircStability_Main_Setting
-- name    : CircStability_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:41.490926+00:00
-- url     : https://prove2.me/theorems/96b4e85a-f217-4742-87ad-06bdb9dd2e9d
-- title:
--   pp. 1–5 — 2-connectivity, longest cycles, circumference, edges on/off a cycle, W_{n,k,c}, Z_{n,k,c}, X_{n,c}, Y_{n,c}, f and h
-- statement:
--   This module fixes the objects of Ma and Ning's stability theorems for the circumference. All graphs are finite and simple, with vertex set $\{0,1,\dots,n-1\}$.
--
--   1. **2-connected.** $G$ has at least three vertices, is connected, and stays connected after deleting any single vertex.
--   2. **Longest cycle, circumference.** A cycle $C$ of $G$ is *longest* if no cycle of $G$ is longer. $G$ has *circumference* $c$ if some cycle has length $c$ and no cycle is longer. The length of a cycle is its number of edges.
--   3. **Edges off and on a vertex set.** For a vertex set $S$ (in practice $S=V(C)$), $e(G-C)+e(G-C,C)$ is the number of edges with at most one endpoint in $S$, and $e(G[C])$ is the number of edges with both endpoints in $S$.
--   4. **The graph $W_{n,k,c}$** (p. 2): a clique $K_{c-k+1}$ together with $n-(c-k+1)$ further vertices, each joined to the same $k$ vertices of the clique. Its number of edges is
--   $$
--   f(n,k,c)=\binom{c-k+1}{2}+k\,(n-c+k-1).
--   $$
--   5. **The graph $Z_{n,k,c}$** (p. 4): the union of a clique $K_{c-k+1}$ and $\frac{n-(c-k+1)}{k-1}$ cliques $K_{k+1}$, any two of the cliques sharing the same two vertices.
--   6. **The function** $h(n,k)=\binom{n-k}{2}+k(k-1)$ (p. 5); note $h(n+1,k)=e(W_{n,k,n})$.
--   7. **The family $\mathcal X_{n,c}$** (p. 3): graphs with $V=A\cup B\cup X$ (disjoint), $A$ a clique of size $\lfloor c/2\rfloor$, $B$ and $X$ stable, every vertex of $A$ adjacent to every vertex of $B$, and two vertices $a\in A$, $b\in B$ with $N(x)=\{a,b\}$ for every $x\in X$.
--   8. **The family $\mathcal Y_{n,c}$** (p. 3): graphs with $V=A\cup B\cup Y$ (disjoint), $A$ a clique of size $\lfloor c/2\rfloor$, $B$ stable, $A$ complete to $B$, $G[Y]$ a nontrivial star forest (at least two stars, each with at least one edge), and two distinct vertices $a,b\in A$ such that every star $S$ of $G[Y]$ is $\{a,b\}$-feasible: $N_G(S)=\{a,b\}$, and if $|S|\ge3$ then all leaves of $S$ have degree $2$ in $G$ and a common neighbour in $\{a,b\}$.
--
--   The graphs $W_{n,k,c}$ are the extremal graphs of Kopylov's and Woodall's edge bounds for 2-connected graphs of given circumference and minimum degree; $\mathcal X_{n,c}$, $\mathcal Y_{n,c}$ and $Z_{n,k,c}$ are the further configurations that appear in the stability versions of those bounds.
--
--   **Formalization Note.** Vertices are `Fin n`. In $W_{n,k,c}$ the clique is $\{0,\dots,c-k\}$ and the hubs are $\{0,\dots,k-1\}$ (inside the clique whenever $k\le c-k+1$, as in every use). In $Z_{n,k,c}$ the clique is $\{0,\dots,c-k\}$, the shared pair is $\{0,1\}$, and the remaining vertices are cut into consecutive blocks of $k-1$; it is the paper's $Z_{n,k,c}$ only when $k-1$ divides $n-(c-k+1)$, and every statement using it carries that divisibility. "Longest cycle" and "circumference" are stated by comparison with every cycle, never as a supremum. The edge counts use classical decidability. In $\mathcal Y_{n,c}$ the stars are given as a partition of $Y$ into vertex sets, each with a centre adjacent to its other vertices and no other edges inside; "two vertices $a,b$" is read as two distinct vertices. $f$ and $h$ are computed in $\mathbb N$; they agree with the paper's values whenever $k\le c$ and $c\le n$ (for $f$) and $k\le n$ (for $h$), which holds in every statement of the mission. The objects 1–4, 7 and 8 repeat, with identical bodies, those of the companion mission on Theorem 1.12.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, pp. 1–5 (§1: p. 1 conventions, p. 2 W_{n,k,c} and f, p. 3 X_{n,c}, Y_{n,c} and footnote 4, p. 4 Z_{n,k,c}, p. 5 h)

import Mathlib

namespace CircStability.Main

open Finset SimpleGraph

/-- 2-connected (vertex connectivity at least 2): at least three vertices, connected, and still
connected after deleting any single vertex. -/
def TwoConnected {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  3 ≤ n ∧ G.Connected ∧ ∀ v : Fin n, (G.induce {w | w ≠ v}).Connected

/-- `C` is a longest cycle of `G`: a cycle at least as long as every cycle of `G`. -/
def IsLongestCycle {n : ℕ} (G : SimpleGraph (Fin n)) {u : Fin n} (C : G.Walk u u) : Prop :=
  C.IsCycle ∧ ∀ (v : Fin n) (D : G.Walk v v), D.IsCycle → D.length ≤ C.length

/-- `G` has circumference `c`: some cycle has length `c` and no cycle is longer. -/
def HasCircumference {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  (∃ (u : Fin n) (C : G.Walk u u), C.IsCycle ∧ C.length = c) ∧
    ∀ (v : Fin n) (D : G.Walk v v), D.IsCycle → D.length ≤ c

/-- The vertex set `V(C)` of a closed walk (a cycle). -/
def cycleVerts {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} (C : G.Walk u u) : Finset (Fin n) :=
  C.support.toFinset

open Classical in
/-- `e(G − C) + e(G − C, C)`: the number of edges of `G` with at most one endpoint in `S`. -/
noncomputable def edgesOffCycle {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  #(G.edgeFinset.filter (fun e => ∃ v ∈ e, v ∉ S))

open Classical in
/-- `e(G[C])`: the number of edges of `G` with both endpoints in `S`. -/
noncomputable def edgesOnCycle {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  #(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S))

/-- `W_{n,k,c}` (p. 2): the clique on the vertices `< c − k + 1`, and every vertex `≥ c − k + 1`
joined exactly to the `k` hubs `< k`. -/
def wGraph (n k c : ℕ) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ (((v : ℕ) < c - k + 1 ∧ (w : ℕ) < c - k + 1) ∨
    ((v : ℕ) < k ∧ c - k + 1 ≤ (w : ℕ)) ∨ ((w : ℕ) < k ∧ c - k + 1 ≤ (v : ℕ)))
  symm := ⟨fun v w h => ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

instance (n k c : ℕ) : DecidableRel (wGraph n k c).Adj := fun v w => by
  unfold wGraph; infer_instance

/-- `Z_{n,k,c}` (p. 4): the clique on the vertices `< c − k + 1`; the vertices `≥ c − k + 1` split
into consecutive blocks of `k − 1`; each block together with the shared pair `{0, 1}` is a
clique `K_{k+1}`. It is the paper's `Z_{n,k,c}` only when `k − 1` divides `n − (c − k + 1)`. -/
def zGraph (n k c : ℕ) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ (((v : ℕ) < c - k + 1 ∧ (w : ℕ) < c - k + 1) ∨
    (c - k + 1 ≤ (v : ℕ) ∧ c - k + 1 ≤ (w : ℕ) ∧
      ((v : ℕ) - (c - k + 1)) / (k - 1) = ((w : ℕ) - (c - k + 1)) / (k - 1)) ∨
    (c - k + 1 ≤ (v : ℕ) ∧ (w : ℕ) < 2) ∨ (c - k + 1 ≤ (w : ℕ) ∧ (v : ℕ) < 2))
  symm := ⟨fun v w h => ⟨h.1.symm, by
    rcases h.2 with h | ⟨h1, h2, h3⟩ | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inl ⟨h2, h1, h3.symm⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

instance (n k c : ℕ) : DecidableRel (zGraph n k c).Adj := fun v w => by
  unfold zGraph; infer_instance

/-- `f(n, k, c) = C(c−k+1, 2) + k(n − c + k − 1)` (p. 2), the number of edges of `W_{n,k,c}`. -/
def fNum (n k c : ℕ) : ℕ := (c - k + 1).choose 2 + k * (n - c + k - 1)

/-- `h(n, k) = C(n−k, 2) + k(k − 1)` (p. 5). -/
def hNum (n k : ℕ) : ℕ := (n - k).choose 2 + k * (k - 1)

/-- Membership in the family `X_{n,c}` (p. 3): `V = A ∪ B ∪ X` with `A` a clique of size `⌊c/2⌋`,
`B` and `X` stable, `(A, B)` complete bipartite, and two vertices `a ∈ A`, `b ∈ B` with
`N(x) = {a, b}` for every `x ∈ X`. -/
def IsXMember (n c : ℕ) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ A B X : Finset (Fin n), Disjoint A B ∧ Disjoint A X ∧ Disjoint B X ∧ A ∪ B ∪ X = univ ∧
    #A = c / 2 ∧ (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → H.Adj a a') ∧
    (∀ b ∈ B, ∀ b' ∈ B, ¬ H.Adj b b') ∧ (∀ x ∈ X, ∀ x' ∈ X, ¬ H.Adj x x') ∧
    (∀ a ∈ A, ∀ b ∈ B, H.Adj a b) ∧
    ∃ a ∈ A, ∃ b ∈ B, ∀ x ∈ X, H.neighborSet x = {a, b}

open Classical in
/-- Membership in the family `Y_{n,c}` (p. 3): `V = A ∪ B ∪ Y` with `A` a clique of size `⌊c/2⌋`,
`B` stable, `(A, B)` complete bipartite, `H[Y]` a nontrivial star forest (at least two stars, each
with at least one edge), and two distinct vertices `a, b ∈ A` such that every star `S` of `H[Y]` is
`{a, b}`-feasible: `N_H(S) = {a, b}`, and if `|S| ≥ 3` all leaves of `S` have degree 2 in `H` and a
common neighbour in `{a, b}`. -/
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

end CircStability.Main


