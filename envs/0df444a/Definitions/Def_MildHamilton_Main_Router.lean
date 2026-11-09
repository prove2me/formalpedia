-- Prove2me | Definitions.Def_MildHamilton_Main_Router
-- name    : MildHamilton_Main_Router
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:11.087859+00:00
-- url     : https://prove2.me/theorems/1208ed61-13d6-4dcc-8b1d-89833cd4e029
-- title:
--   Hamilton routers, comparators, basic routers and subdivided cycles
-- statement:
--   Let $A,B$ be disjoint subsets of $V(S)$ with $|A|=|B|$. The graph $S$ is an **$A,B$-Hamilton-router** if, for every bijection $\phi:A\to B$, the set $V(S)$ can be partitioned into paths with endpoints in $A\times B$ such that, with $M_\phi=\{(\phi(a),a):a\in A\}$, the edges of the paths together with $M_\phi$ form a Hamilton cycle on $V(S)$. A **comparator** is a Hamilton router of order $|A|=2$.
--
--   A **basic Hamilton router of order $n$** is built on a grid $\{v_{i,j}:(i,j)\in[4]\times[n]\}$ with $A=\{v_{1,j}\}$ and $B=\{v_{4,j}\}$. For every odd $i\in[n-1]$ a comparator is added from $\{v_{1,i},v_{1,i+1}\}$ to $\{v_{2,i},v_{2,i+1}\}$, and for every even $i\in[n-1]$ one from $\{v_{3,i},v_{3,i+1}\}$ to $\{v_{4,i},v_{4,i+1}\}$. A path joins $v_{2,i}$ to $v_{3,i}$ for each $i\in[n]$. Finally $v_{3,1}$ is joined to $v_{4,1}$, and $v_{3,n}$ to $v_{4,n}$ for even $n$, or $v_{1,n}$ to $v_{2,n}$ for odd $n$.
--
--   The module also records the data of Lemma 4.5: a perfect matching $P$ of $V(C)\setminus(A\cup B)$ for a cycle $C$, the two perfect matchings $M_0\ni c_0c_1$ and $M_1\ni c_1c_2$ of $C$, and the graphs obtained from $C$ by adding, for each pair of $P$, a path between its two vertices.
--
--   Routers convert a collection of disjoint paths with an uncontrolled end-to-end bijection into one Hamilton cycle.
--
--   **Formalization Note** Routers are defined over an arbitrary edge relation $r$ on the vertices, with paths directed from $A$ to $B$; $r=$ `G.Adj` gives the undirected notion and a directed adjacency the notion of Proposition 4.2. Only the vertex set of $S$ is recorded, since a router on a subgraph of $r$ is a router for $r$. Each path runs from $a$ to $\sigma(a)$ for a bijection $\sigma$, and the single-cycle condition says that $a\mapsto\phi^{-1}(\sigma(a))$ is one cycle on $A$: this is the permutation traversed by following a path and then the matching edge back. Indices of the grid keep the printed 1-based parity. The boundary connections may be paths of any length, as the proof of Lemma 4.7 requires, and each piece meets the rest of the construction only in its own grid terminals.
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Definition 4.1 and Remark, p. 7; Definition 4.3, p. 8; Lemma 4.5 and its proof, pp. 8–9

import Mathlib

namespace MildHamilton.Main

/-- The list `l` is a path from `u` to `v` along the relation `r`: its vertices are distinct, it starts
at `u`, ends at `v`, and consecutive vertices are related by `r`. -/
def IsRPath {V : Type*} (r : V → V → Prop) (u v : V) (l : List V) : Prop :=
  l.IsChain r ∧ l.Nodup ∧ l.head? = some u ∧ l.getLast? = some v

/-- The internal vertices of a path written as a list. -/
def interior {V : Type*} (l : List V) : List V := l.tail.dropLast

/-- The list `l` is a Hamilton cycle of the directed graph with edge relation `r`: it lists each vertex
exactly once, consecutive vertices are related by `r`, and so are the last and the first. -/
def IsRHamiltonCycle {V : Type*} (r : V → V → Prop) (l : List V) : Prop :=
  l ≠ [] ∧ l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain r ∧
    ∀ x y, l.getLast? = some x → l.head? = some y → r x y

/-- Definition 4.1 (Muyesser, STOC 2027 submission #233, p. 7): `W` is the vertex set of an
`A, B`-Hamilton-router inside the (directed) graph with edge relation `r`. `A`, `B` are disjoint subsets
of `W` with `|A| = |B|`, and for every bijection `ϕ : A → B` the set `W` is partitioned by paths, one from
each `a ∈ A` to `σ a ∈ B` with `σ` a bijection, such that these paths together with the matching
`{(ϕ a, a)}` form one cycle through all of `W`: following a path and then the matching edge back from
`B` to `A` is the permutation `a ↦ ϕ⁻¹ (σ a)`, which must be a single cycle on `A`.
With `r := G.Adj` this is the undirected definition; a router on a subgraph `S` of `r` is a router
for `r`, so only the vertex set of `S` is recorded. -/
def IsHamiltonRouter {V : Type*} (r : V → V → Prop) (W A B : Finset V) : Prop :=
  A ⊆ W ∧ B ⊆ W ∧ Disjoint A B ∧ A.card = B.card ∧
    ∀ ϕ : A ≃ B, ∃ (σ : A ≃ B) (path : A → List V),
      (∀ a : A, IsRPath r (a : V) (σ a : V) (path a)) ∧
      (∀ v, v ∈ W ↔ ∃ a : A, v ∈ path a) ∧
      (∀ a a' : A, a ≠ a' → List.Disjoint (path a) (path a')) ∧
      Equiv.Perm.IsCycleOn (σ.trans ϕ.symm) (Set.univ : Set A)

/-- A comparator (Muyesser, STOC 2027 submission #233, Remark, p. 7): a Hamilton router of order 2. -/
def IsComparator {V : Type*} (r : V → V → Prop) (W A B : Finset V) : Prop :=
  IsHamiltonRouter r W A B ∧ A.card = 2

/-- The data of Definition 4.3 (Muyesser, STOC 2027 submission #233, p. 8), with the printed 1-based
indices: `v i j` is `v_{i,j}` for `(i, j) ∈ [4] × [n]`, and values of `v` outside that range are never
used. `oddComp i` and `evenComp i` are the vertex sets of `S_i^{odd}` and `S_i^{even}`, `link i` is the path
from `v_{2,i}` to `v_{3,i}`, `first` joins `v_{3,1}` to `v_{4,1}`, and `last` is the connection at the last
column. -/
structure BasicRouterData (V : Type*) where
  /-- The grid `v_{i,j}`. -/
  v : ℕ → ℕ → V
  /-- The vertex set of `S_i^{odd}`. -/
  oddComp : ℕ → Finset V
  /-- The vertex set of `S_i^{even}`. -/
  evenComp : ℕ → Finset V
  /-- The path from `v_{2,i}` to `v_{3,i}`. -/
  link : ℕ → List V
  /-- The connection from `v_{3,1}` to `v_{4,1}`. -/
  first : List V
  /-- The connection from `v_{3,n}` to `v_{4,n}` (`n` even) or from `v_{1,n}` to `v_{2,n}` (`n` odd). -/
  last : List V

/-- The pieces added to the grid in Definition 4.3. -/
inductive BasicPiece
  | odd (i : ℕ)
  | even (i : ℕ)
  | link (i : ℕ)
  | first
  | last
  deriving DecidableEq

/-- The pieces that exist in a router of order `n`: comparators at the odd and the even `i ∈ [n − 1]`
(the printed parity), a link at every column `i ∈ [n]`, and the two boundary connections. -/
def BasicPiece.Active (n : ℕ) : BasicPiece → Prop
  | .odd i => i ∈ Finset.Icc 1 (n - 1) ∧ Odd i
  | .even i => i ∈ Finset.Icc 1 (n - 1) ∧ Even i
  | .link i => i ∈ Finset.Icc 1 n
  | .first => True
  | .last => True

/-- The grid `{v_{i,j} : (i, j) ∈ [4] × [n]}`. -/
def BasicRouterData.grid {V : Type*} [DecidableEq V] (D : BasicRouterData V) (n : ℕ) : Finset V :=
  (Finset.Icc 1 4 ×ˢ Finset.Icc 1 n).image fun ij => D.v ij.1 ij.2

/-- The vertices of a piece other than its grid terminals: a comparator without its four terminals, a
path without its two ends. -/
def BasicRouterData.privateVerts {V : Type*} [DecidableEq V] (D : BasicRouterData V) :
    BasicPiece → Finset V
  | .odd i => D.oddComp i \ {D.v 1 i, D.v 1 (i + 1), D.v 2 i, D.v 2 (i + 1)}
  | .even i => D.evenComp i \ {D.v 3 i, D.v 3 (i + 1), D.v 4 i, D.v 4 (i + 1)}
  | .link i => (interior (D.link i)).toFinset
  | .first => (interior D.first).toFinset
  | .last => (interior D.last).toFinset

/-- Definition 4.3 (Muyesser, STOC 2027 submission #233, p. 8): `W`, `A`, `B` arise from the construction
of a basic Hamilton router of order `n ≥ 1` inside the (directed) graph with edge relation `r`. The two
boundary connections may be paths of any length, as the proof of Lemma 4.7 (p. 11) requires; a single edge
is the printed case. Every piece meets the rest of the construction only in its own grid terminals, and `W` is
the union of the grid and the pieces. -/
structure IsBasicRouterConstruction {V : Type*} [DecidableEq V] (r : V → V → Prop) (n : ℕ)
    (W A B : Finset V) (D : BasicRouterData V) : Prop where
  order_pos : 1 ≤ n
  /-- The grid vertices are distinct. -/
  grid_injective : Set.InjOn (fun ij : ℕ × ℕ => D.v ij.1 ij.2)
    (↑(Finset.Icc 1 4 ×ˢ Finset.Icc 1 n : Finset (ℕ × ℕ)))
  A_eq : A = (Finset.Icc 1 n).image (D.v 1)
  B_eq : B = (Finset.Icc 1 n).image (D.v 4)
  /-- For every odd `i ∈ [n − 1]`, a comparator from `{v_{1,i}, v_{1,i+1}}` to `{v_{2,i}, v_{2,i+1}}`. -/
  odd_comparator : ∀ i ∈ Finset.Icc 1 (n - 1), Odd i →
    IsComparator r (D.oddComp i) {D.v 1 i, D.v 1 (i + 1)} {D.v 2 i, D.v 2 (i + 1)}
  /-- For every even `i ∈ [n − 1]`, a comparator from `{v_{3,i}, v_{3,i+1}}` to `{v_{4,i}, v_{4,i+1}}`. -/
  even_comparator : ∀ i ∈ Finset.Icc 1 (n - 1), Even i →
    IsComparator r (D.evenComp i) {D.v 3 i, D.v 3 (i + 1)} {D.v 4 i, D.v 4 (i + 1)}
  /-- For every `i ∈ [n]`, a path from `v_{2,i}` to `v_{3,i}`. -/
  link_path : ∀ i ∈ Finset.Icc 1 n, IsRPath r (D.v 2 i) (D.v 3 i) (D.link i)
  /-- The connection from `v_{3,1}` to `v_{4,1}`. -/
  first_path : IsRPath r (D.v 3 1) (D.v 4 1) D.first
  /-- The connection at the last column: `v_{3,n}` to `v_{4,n}` for even `n`, `v_{1,n}` to `v_{2,n}` for odd `n`. -/
  last_even : Even n → IsRPath r (D.v 3 n) (D.v 4 n) D.last
  last_odd : Odd n → IsRPath r (D.v 1 n) (D.v 2 n) D.last
  /-- Non-terminal vertices of pieces are not grid vertices. -/
  private_off_grid : ∀ x : BasicPiece, x.Active n → Disjoint (D.privateVerts x) (D.grid n)
  /-- Distinct pieces have disjoint non-terminal vertices. -/
  private_disjoint : ∀ x y : BasicPiece, x.Active n → y.Active n → x ≠ y →
    Disjoint (D.privateVerts x) (D.privateVerts y)
  /-- `W` is the union of the grid and the pieces. -/
  W_eq : ∀ u, u ∈ W ↔ u ∈ D.grid n ∨ ∃ x : BasicPiece, x.Active n ∧ u ∈ D.privateVerts x

/-- `W` is the vertex set of a basic Hamilton router of order `n` with terminals `A`, `B` inside the
(directed) graph with edge relation `r`. -/
def IsBasicHamiltonRouter {V : Type*} [DecidableEq V] (r : V → V → Prop) (n : ℕ)
    (W A B : Finset V) : Prop :=
  ∃ D : BasicRouterData V, IsBasicRouterConstruction r n W A B D

/-- The edges of the cycle `c_0 c_1 ⋯ c_{k-1} c_0` on the labels `Fin k`. -/
def cycleAdj {k : ℕ} (x y : Fin k) : Prop :=
  (x.val + 1) % k = y.val ∨ (y.val + 1) % k = x.val

/-- `P` is a perfect matching of `V(C) \ (A ∪ B)` for the cycle `C` on `Fin k`: its pairs have distinct
ends outside `A ∪ B`, and each vertex outside `A ∪ B` lies in exactly one pair.
Each pair is recorded once, in an arbitrary orientation. -/
def IsCyclePairing {k : ℕ} (A B : Finset (Fin k)) (P : Finset (Fin k × Fin k)) : Prop :=
  (∀ e ∈ P, e.1 ≠ e.2 ∧ e.1 ∉ A ∧ e.1 ∉ B ∧ e.2 ∉ A ∧ e.2 ∉ B) ∧
    ∀ x, x ∉ A → x ∉ B → ∃! e, e ∈ P ∧ (e.1 = x ∨ e.2 = x)

/-- The graph on the cycle's vertices whose edges are the pairs of `P`. -/
def pairGraph {k : ℕ} (P : Finset (Fin k × Fin k)) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun x y => (x, y) ∈ P

/-- The perfect matching `M_0 = {c_0c_1, c_2c_3, …}` of the cycle on `Fin k`, `k` even. -/
def matchingM0 (k : ℕ) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun x y => x.val / 2 = y.val / 2

/-- The perfect matching `M_1 = {c_1c_2, c_3c_4, …, c_{k-1}c_0}` of the cycle on `Fin k`, `k` even. -/
def matchingM1 (k : ℕ) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun x y => ((x.val + 1) % k) / 2 = ((y.val + 1) % k) / 2

/-- Consecutive vertices of the list `l`, in either order. -/
def IsListEdge {V : Type*} (l : List V) (u v : V) : Prop :=
  (u, v) ∈ l.zip l.tail ∨ (v, u) ∈ l.zip l.tail

/-- Property 2 of Lemma 4.5 (Muyesser, STOC 2027 submission #233, p. 9): the graph `S` on `V` is the `k`-cycle
`c` together with, for every pair `e ∈ P`, a path `Q e` between the two ends of `e`, the added paths being
pairwise vertex-disjoint and each meeting the cycle exactly in its two ends. The edges of `S` are exactly those
of the cycle and of the paths, and every vertex lies on the cycle or on a path. -/
structure IsSubdividedCycle {k : ℕ} (P : Finset (Fin k × Fin k)) {V : Type*} (S : SimpleGraph V)
    (c : Fin k → V) (Q : Fin k × Fin k → List V) : Prop where
  c_injective : Function.Injective c
  path : ∀ e ∈ P, IsRPath S.Adj (c e.1) (c e.2) (Q e)
  interior_off_cycle : ∀ e ∈ P, ∀ x ∈ interior (Q e), x ∉ Set.range c
  paths_disjoint : ∀ e ∈ P, ∀ e' ∈ P, e ≠ e' → List.Disjoint (Q e) (Q e')
  spanning : ∀ u, u ∈ Set.range c ∨ ∃ e ∈ P, u ∈ Q e
  adj_iff : ∀ u w, S.Adj u w ↔
    (∃ x y, cycleAdj x y ∧ u = c x ∧ w = c y) ∨ ∃ e ∈ P, IsListEdge (Q e) u w

end MildHamilton.Main


