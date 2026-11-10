-- Prove2me | Definitions.Def_ApproxCactus_Main_Separations
-- name    : ApproxCactus_Main_Separations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:00:26.220928+00:00
-- url     : https://prove2.me/theorems/1bffcf17-12be-4b41-b1a8-972583c7e84b
-- title:
--   Separations, order, breadth, closeness, nesting, edit-distance, unbreakability and narrowness
-- statement:
--   Let $G$ be a finite simple graph. A **separation** of $G$ is a pair $(A,B)$ of vertex sets with $A\cup B=V(G)$ and no edge of $G$ between $A\setminus B$ and $B\setminus A$; its **separator** is $\mathrm{sep}(A,B)=A\cap B$, its **order** $|A\cap B|$, its **breadth** $\min\{|A\setminus B|,|B\setminus A|\}$ ($b$-broad means breadth $\ge b$), it is **proper** if both $A\setminus B$ and $B\setminus A$ are nonempty, and its **inverse** is $(B,A)$ (Lean: `Prod.swap`). A set of separations is **symmetric** if it is closed under inversion.
--
--   For $\varepsilon\in\mathbb N$: $X\subseteq_\varepsilon Y$ means $|X\setminus Y|\le\varepsilon$; $(A,B)\le_\varepsilon(C,D)$ means $A\subseteq_\varepsilon C$ and $D\subseteq_\varepsilon B$; $(A,B)$ and $(C,D)$ are **$\varepsilon$-close** if $(A,B)\le_\varepsilon(C,D)$ and $(C,D)\le_\varepsilon(A,B)$; they are **$\varepsilon$-nested** if $(A,B)\le_\varepsilon(C,D)$ after possibly swapping $A$ with $B$ and/or $C$ with $D$, and otherwise they **$\varepsilon$-cross**; "cross" is $0$-cross. They have **edit-distance $\le d$** if $|A\triangle C|\le d$ and $|B\triangle D|\le d$.
--
--   $G$ is **$(q,k-1)$-unbreakable** if every separation of order $<k$ has breadth $\le q$ (vacuous for $k=0$). For $X\subseteq V(G)$, a **component of $G-X$** is the vertex set of a connected component of $G[V\setminus X]$; $N(K)$ is the set of vertices outside $K$ with a neighbour in $K$. A separation $(A,B)$ is **narrow** if every component of $G-(A\cap B)$ has neighbourhood exactly $A\cap B$, and $G$ is **$(b,k)$-narrow** if every $b$-broad separation of order exactly $k$ is narrow. A set $S$ **$\varepsilon$-approximates** $S'$ if every $\varepsilon$-broad $s'\in S'$ is $\varepsilon$-close to some $s\in S$. A set $\sigma$ is a **star** if $s\le t^*$ for all distinct $s,t\in\sigma$, i.e. $A\subseteq D$ and $C\subseteq B$ for $s=(A,B)$, $t=(C,D)$.
--
--   Formalization note: separations are encoded as pairs of `Finset V` with the predicate `IsSep G`; all functions (order, breadth, …) are defined on arbitrary pairs.
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), pp. 1–3, 13, 21–22, 36 (PDF 4–6, 16, 24–25, 39), §2.2, §3.1–3.2, §4.3

import Mathlib

namespace ApproxCactus.Main

/-- A **separation** of the finite simple graph `G` (§3.1, p. 21): an ordered pair `(A, B)` of
vertex sets with `G[A] ∪ G[B] = G`, i.e. `A ∪ B = V(G)` and no edge of `G` joins `A ∖ B` to
`B ∖ A`. Separations are encoded as plain pairs `Finset V × Finset V`; this predicate says which
pairs are separations of `G`. The inverse `s∗ = (B, A)` is `Prod.swap s`. -/
def IsSep {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (s : Finset V × Finset V) : Prop :=
  s.1 ∪ s.2 = Finset.univ ∧ ∀ u v : V, G.Adj u v → u ∈ s.1 \ s.2 → v ∉ s.2 \ s.1

/-- The **separator** `sep(s) = A ∩ B` of `s = (A, B)`. -/
def sep {V : Type*} [DecidableEq V] (s : Finset V × Finset V) : Finset V := s.1 ∩ s.2

/-- The **order** `|A ∩ B|` of `s = (A, B)`. A `k`-separation has order exactly `k`, a
`(⩽ k)`-separation order `⩽ k`, a `(< k)`-separation order `< k`. -/
def order {V : Type*} [DecidableEq V] (s : Finset V × Finset V) : ℕ := (s.1 ∩ s.2).card

/-- The **breadth** `min{|A ∖ B|, |B ∖ A|}` of `s = (A, B)`; `s` is `b`-broad iff `b ≤ breadth s`,
and `(> q)`-broad iff `q < breadth s`. -/
def breadth {V : Type*} [DecidableEq V] (s : Finset V × Finset V) : ℕ :=
  min (s.1 \ s.2).card (s.2 \ s.1).card

/-- `s = (A, B)` is **proper** if both `A ∖ B` and `B ∖ A` are nonempty. -/
def IsProper {V : Type*} [DecidableEq V] (s : Finset V × Finset V) : Prop :=
  (s.1 \ s.2).Nonempty ∧ (s.2 \ s.1).Nonempty

/-- A set `S` of separations is **symmetric** if `s∗ ∈ S` whenever `s ∈ S`. -/
def IsSymmetric {V : Type*} (S : Set (Finset V × Finset V)) : Prop :=
  ∀ s ∈ S, s.swap ∈ S

/-- `X ⊆ε Y`: all but at most `ε` vertices of `X` lie in `Y`, i.e. `|X ∖ Y| ≤ ε` (p. 36). -/
def SubsetEps {V : Type*} [DecidableEq V] (ε : ℕ) (X Y : Finset V) : Prop :=
  (X \ Y).card ≤ ε

/-- `(A, B) ⩽ε (C, D)` iff `A ⊆ε C` and `B ⊇ε D` (i.e. `D ⊆ε B`) (p. 36). For `ε = 0` this is the
usual order `(A, B) ⩽ (C, D)` iff `A ⊆ C` and `D ⊆ B`. -/
def LeEps {V : Type*} [DecidableEq V] (ε : ℕ) (s t : Finset V × Finset V) : Prop :=
  SubsetEps ε s.1 t.1 ∧ SubsetEps ε t.2 s.2

/-- `s` and `t` are **`ε`-close**: `s ⩽ε t` and `t ⩽ε s`, i.e. the four sets `A ∖ C`, `C ∖ A`,
`B ∖ D`, `D ∖ B` all have size `≤ ε` (p. 36). -/
def Close {V : Type*} [DecidableEq V] (ε : ℕ) (s t : Finset V × Finset V) : Prop :=
  LeEps ε s t ∧ LeEps ε t s

/-- `s` and `t` are **`ε`-nested**: after possibly swapping the sides of `s` and/or of `t`,
`s ⩽ε t` (p. 36). `0`-nested is nested. -/
def NestedEps {V : Type*} [DecidableEq V] (ε : ℕ) (s t : Finset V × Finset V) : Prop :=
  LeEps ε s t ∨ LeEps ε s.swap t ∨ LeEps ε s t.swap ∨ LeEps ε s.swap t.swap

/-- `s` and `t` **`ε`-cross**: they are not `ε`-nested. -/
def CrossEps {V : Type*} [DecidableEq V] (ε : ℕ) (s t : Finset V × Finset V) : Prop :=
  ¬ NestedEps ε s t

/-- `s` and `t` **cross**: they are not nested (`0`-cross). -/
def Crosses {V : Type*} [DecidableEq V] (s t : Finset V × Finset V) : Prop :=
  CrossEps 0 s t

/-- `(A, B)` and `(C, D)` have **edit-distance `⩽ d`**: `|A △ C| ≤ d` and `|B △ D| ≤ d`
(pp. 2, 36). -/
def EditDistLe {V : Type*} [DecidableEq V] (d : ℕ) (s t : Finset V × Finset V) : Prop :=
  (symmDiff s.1 t.1).card ≤ d ∧ (symmDiff s.2 t.2).card ≤ d

/-- `G` is **`(q, k − 1)`-unbreakable**: every separation of order `< k` (i.e. of order at most
`k − 1`) has breadth `≤ q` (pp. 3, 13). Stated with `order s < k`, so for `k = 0` it is vacuous;
there is no truncated subtraction `k - 1`. -/
def IsUnbreakableBelow {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (q k : ℕ) : Prop :=
  ∀ s : Finset V × Finset V, IsSep G s → order s < k → breadth s ≤ q

/-- `K ⊆ V` is the vertex set of a **component of `G − X`**: of a connected component of the
subgraph of `G` induced on `V ∖ X`. -/
def IsComponentOf {V : Type*} (G : SimpleGraph V) (X : Finset V) (K : Set V) : Prop :=
  ∃ c : (G.induce {v : V | v ∉ X}).ConnectedComponent, K = Subtype.val '' c.supp

/-- The **neighbourhood** `N(K)` of a vertex set `K`: the vertices outside `K` adjacent to some
vertex of `K`. -/
def nbhd {V : Type*} (G : SimpleGraph V) (K : Set V) : Set V :=
  {v | v ∉ K ∧ ∃ u ∈ K, G.Adj u v}

/-- `s = (A, B)` is **narrow** if every component of `G − (A ∩ B)` has neighbourhood equal to
`A ∩ B` (p. 22). -/
def IsNarrow {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s : Finset V × Finset V) : Prop :=
  ∀ K : Set V, IsComponentOf G (s.1 ∩ s.2) K → nbhd G K = ↑(s.1 ∩ s.2)

/-- `G` is **`(b, k)`-narrow** if every `b`-broad `k`-separation of `G` is narrow (p. 22). -/
def IsNarrowGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (b k : ℕ) : Prop :=
  ∀ s : Finset V × Finset V, IsSep G s → order s = k → b ≤ breadth s → IsNarrow G s

/-- `S` **`ε`-approximates** `S'`: every `ε`-broad `s' ∈ S'` is `ε`-close to some separation in
`S` (p. 13). -/
def Approximates {V : Type*} [DecidableEq V] (ε : ℕ) (S S' : Set (Finset V × Finset V)) : Prop :=
  ∀ s' ∈ S', ε ≤ breadth s' → ∃ s ∈ S, Close ε s' s

/-- `σ` is a **star**: `s ⩽ t∗` for all distinct `s, t ∈ σ`, i.e. for `s = (A, B)` and
`t = (C, D)`: `A ⊆ D` and `C ⊆ B` (p. 22). -/
def IsStar {V : Type*} (σ : Set (Finset V × Finset V)) : Prop :=
  ∀ s ∈ σ, ∀ t ∈ σ, s ≠ t → s.1 ⊆ t.2 ∧ t.1 ⊆ s.2

end ApproxCactus.Main


