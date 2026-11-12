-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Graph
-- name    : MinCostArbPacking_Main_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:08.767211+00:00
-- url     : https://prove2.me/theorems/2f09a469-d9cd-41df-ab02-8c4b9df950b7
-- title:
--   Directed multigraphs, forests, $\mathcal G^k$-independence, arborescence packings and tight blocks
-- statement:
--   A **directed multigraph** $G$ consists of a finite vertex set $V$, a finite arc set $E$ and maps $\mathrm{tail},\mathrm{head}:E\to V$. Parallel arcs are distinct elements of $E$, and loops ($\mathrm{tail}(e)=\mathrm{head}(e)$) are allowed.
--
--   1. A **cycle** of an arc set $F$ in the underlying undirected multigraph is a sequence of $l\ge1$ distinct arcs $e_0,\dots,e_{l-1}\in F$ and distinct vertices $v_0,\dots,v_{l-1}$ such that $e_i$ joins $v_i$ and $v_{i+1 \bmod l}$; a loop is a cycle of length $1$ and two parallel arcs form a cycle of length $2$. A **forest** is an arc set without cycles. For a forest $F$ and an arc $e$ whose ends are connected in $F$, an arc $f\in F$ **lies on the $F$-path** of $e$ when removing $f$ disconnects the ends of $e$.
--   2. A **forest decomposition** of $X\subseteq E$ is a partition $X=F_1\,\dot\cup\cdots\dot\cup\,F_k$ into forests, and $X$ is **independent in $\mathcal G^k$** (the union of $k$ copies of the graphic matroid) if it has one. A **circuit** of $\mathcal G^k$ is a minimal dependent set, and $e\notin I$ is **free** for $I$ if $I+e$ is independent. A **basis** of $Y$ is an independent subset of $Y$ of maximum cardinality.
--   3. $\deg^{in}_X(v)$ is the number of arcs of $X$ with head $v$, $\deg^{in}_X(S)$ the number entering $S$ from $V\setminus S$, and $X[S]$ the set of arcs of $X$ with both ends in $S$.
--   4. An **$r$-arborescence** is an arc set $A$ such that no arc of $A$ enters $r$, every $v\ne r$ has exactly one entering arc in $A$, and every vertex is reachable from $r$ along arcs of $A$. A **packing** is a $k$-tuple of pairwise disjoint $r$-arborescences; its cost is $\sum_i c(A_i)$ with $c(X)=\sum_{e\in X}c(e)$.
--   5. A nonempty $T\subseteq V$ is **$I$-tight** if $|I[T]|=k(|T|-1)$; the **tight blocks** are the inclusion-maximal tight sets, $t=|\mathcal T(I)|$ is their number, and $\mathrm{block}(v)$ is the union of all tight sets containing $v$. An arc is **internal** if both ends lie in one block and **crossing** otherwise; $I^{cr}$ is the set of crossing arcs of $I$. The **contracted graph** replaces every vertex by its block.
--   6. The **deficiency** is $\mathrm{def}_I(v)=k-\deg^{in}_I(v)$ for $v\ne r$, $\mathrm{def}_I(r)=0$, and $\mathrm{def}_I(S)=\sum_{v\in S}\mathrm{def}_I(v)$.
--   7. $\log x=\max\{1,\log_2 x\}$. An **instance** of Theorem 1.1 is $(n,m,k,r,\mathrm{tail},\mathrm{head},c)$ with vertices $\{0,\dots,n-1\}$, arcs $\{0,\dots,m-1\}$ and real costs $c$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Deficiencies are integers, so no natural-number truncation occurs. `blockOf` agrees with the tight block containing $v$ whenever $I$ is independent (the maximal tight sets then partition $V$).
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §1, p.1; §3.1, p.7; §3.2, pp.7–8

import Mathlib

set_option autoImplicit false

/-!
# Directed multigraphs, forests, the k-fold graphic matroid, arborescence packings and tight blocks

Zhaienhe Zhou, *Minimum-Cost k-Arborescence Packing in Õ(km + k⁴n) Time*, STOC 2027 submission
#1416 (October 2026), §1 (p.1) and §§3.1–3.2 (pp.7–8).

A directed multigraph has a vertex type `V` and an arc type `E` with maps `tail head : E → V`; parallel
arcs are distinct elements of `E` and loops (`tail e = head e`) are allowed. Independence in the
k-fold graphic matroid `𝒢^k` is the existence of a partition into `k` forests of the underlying
undirected multigraph, where a loop is a cycle of length one and two parallel arcs form a cycle of
length two.
-/

noncomputable section
open Classical

namespace MinCostArbPacking.Main

/-- A directed multigraph: arcs `E`, vertices `V`, and the two ends of every arc. -/
structure Digraph (V E : Type) where
  tail : E → V
  head : E → V

variable {V E : Type}

namespace Digraph

/-- The arc `e` joins `x` and `y` in the underlying undirected multigraph. -/
def Joins (G : Digraph V E) (e : E) (x y : V) : Prop :=
  (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x)

/-- `F` contains a cycle of the underlying undirected multigraph: distinct arcs `es 0, …, es (l-1)`
and distinct vertices `vs 0, …, vs (l-1)` with `es i` joining `vs i` and `vs (i+1 mod l)`.
For `l = 1` this is a loop, for `l = 2` a pair of parallel arcs. -/
def HasCycle (G : Digraph V E) (F : Finset E) : Prop :=
  ∃ (l : ℕ) (hl : 0 < l) (es : Fin l → E) (vs : Fin l → V),
    Function.Injective es ∧ Function.Injective vs ∧
    ∀ i : Fin l, es i ∈ F ∧ G.Joins (es i) (vs i) (vs ⟨(i.val + 1) % l, Nat.mod_lt _ hl⟩)

/-- A forest of the underlying undirected multigraph: an arc set without cycles. -/
def IsForest (G : Digraph V E) (F : Finset E) : Prop := ¬ G.HasCycle F

/-- `x` and `y` are connected using arcs of `F` (in either direction). -/
def Conn (G : Digraph V E) (F : Finset E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ F, G.Joins e a b) x y

/-- For a forest `F`: the ends of `e` are connected in `F` and `f ∈ F` lies on the `F`-path between
them (removing `f` disconnects them). -/
def OnPath (G : Digraph V E) (F : Finset E) (e f : E) : Prop :=
  f ∈ F ∧ G.Conn F (G.tail e) (G.head e) ∧ ¬ G.Conn (F.erase f) (G.tail e) (G.head e)

/-- `F` is a spanning tree of the vertex set `T`: its arcs have both ends in `T`, it is a forest,
and it connects all of `T`. -/
def IsSpanningTreeOn (G : Digraph V E) (F : Finset E) (T : Finset V) : Prop :=
  (∀ e ∈ F, G.tail e ∈ T ∧ G.head e ∈ T) ∧ G.IsForest F ∧
    ∀ x ∈ T, ∀ y ∈ T, G.Conn F x y

/-- A forest decomposition `X = F 0 ∪̇ ⋯ ∪̇ F (k-1)`. -/
def ForestDecomp (G : Digraph V E) (k : ℕ) (X : Finset E) (F : Fin k → Finset E) : Prop :=
  (∀ i, G.IsForest (F i)) ∧ (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ X = Finset.univ.biUnion F

/-- Independence in `𝒢^k`, the union of `k` copies of the graphic matroid: a union of `k` forests. -/
def IndepK (G : Digraph V E) (k : ℕ) (X : Finset E) : Prop := ∃ F, G.ForestDecomp k X F

/-- A circuit of `𝒢^k`: a minimal dependent set. -/
def IsCircuitK (G : Digraph V E) (k : ℕ) (C : Finset E) : Prop :=
  ¬ G.IndepK k C ∧ ∀ D, D ⊂ C → G.IndepK k D

/-- `e ∉ I` is free for `I` if `I + e` is independent in `𝒢^k`. -/
def Free (G : Digraph V E) (k : ℕ) (I : Finset E) (e : E) : Prop :=
  e ∉ I ∧ G.IndepK k (insert e I)

/-- `deg^in_X(v)`: the number of arcs of `X` with head `v`. -/
def inDeg (G : Digraph V E) (X : Finset E) (v : V) : ℕ := (X.filter (fun e => G.head e = v)).card

/-- `deg^in_X(S)`: the number of arcs of `X` entering `S` from outside `S`. -/
def inDegSet (G : Digraph V E) (X : Finset E) (S : Finset V) : ℕ :=
  (X.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S)).card

/-- `X[S]`: the arcs of `X` with both ends in `S`. -/
def induced (G : Digraph V E) (X : Finset E) (S : Finset V) : Finset E :=
  X.filter (fun e => G.tail e ∈ S ∧ G.head e ∈ S)

/-- `v` is reachable from `x` along arcs of `A`, respecting their directions. -/
def Reach (G : Digraph V E) (A : Finset E) (x v : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ A, G.tail e = a ∧ G.head e = b) x v

/-- An `r`-arborescence (a spanning tree with all arcs directed away from `r`): no arc enters `r`,
every other vertex has exactly one entering arc, and every vertex is reachable from `r`. -/
def IsArborescence (G : Digraph V E) (r : V) (A : Finset E) : Prop :=
  (∀ e ∈ A, G.head e ≠ r) ∧ (∀ v, v ≠ r → G.inDeg A v = 1) ∧ ∀ v, G.Reach A r v

/-- A packing of `k` arc-disjoint `r`-arborescences. -/
def IsPacking (G : Digraph V E) (r : V) (k : ℕ) (P : Fin k → Finset E) : Prop :=
  (∀ i, G.IsArborescence r (P i)) ∧ ∀ i j, i ≠ j → Disjoint (P i) (P j)

/-- `T` is `I`-tight: nonempty with `|I[T]| = k(|T| - 1)`. -/
def IsTight (G : Digraph V E) (k : ℕ) (I : Finset E) (T : Finset V) : Prop :=
  T.Nonempty ∧ (G.induced I T).card = k * (T.card - 1)

/-- A tight block: an inclusion-maximal `I`-tight set (a member of `𝒯(I)`). -/
def IsTightBlock (G : Digraph V E) (k : ℕ) (I : Finset E) (T : Finset V) : Prop :=
  G.IsTight k I T ∧ ∀ T', G.IsTight k I T' → T ⊆ T' → T' = T

/-- The union of all `I`-tight sets containing `v`; for independent `I` this is the tight block
containing `v` (the maximal tight sets partition `V`). -/
def blockOf [Fintype V] [DecidableEq V] (G : Digraph V E) (k : ℕ) (I : Finset E) (v : V) :
    Finset V :=
  (Finset.univ.filter (fun T : Finset V => G.IsTight k I T ∧ v ∈ T)).sup id

/-- The number `t = |𝒯(I)|` of tight blocks. -/
def numBlocks [Fintype V] (G : Digraph V E) (k : ℕ) (I : Finset E) : ℕ :=
  (Finset.univ.filter (fun T : Finset V => G.IsTightBlock k I T)).card

/-- An arc is internal if both ends lie in one tight block. -/
def IsInternal (G : Digraph V E) (k : ℕ) (I : Finset E) (e : E) : Prop :=
  ∃ T, G.IsTightBlock k I T ∧ G.tail e ∈ T ∧ G.head e ∈ T

/-- An arc is crossing if it is not internal. -/
def IsCrossing (G : Digraph V E) (k : ℕ) (I : Finset E) (e : E) : Prop := ¬ G.IsInternal k I e

/-- `I^cr`: the arcs of `I` whose ends lie in different tight blocks. -/
def crossingPart (G : Digraph V E) (k : ℕ) (I : Finset E) : Finset E :=
  I.filter (fun e => G.IsCrossing k I e)

/-- Deficiency `def_I(v) = k - deg^in_I(v)` for `v ≠ r` and `def_I(r) = 0` (integer valued). -/
def defi (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (v : V) : ℤ :=
  if v = r then 0 else (k : ℤ) - (G.inDeg I v : ℤ)

/-- `def_I(S) = Σ_{v ∈ S} def_I(v)`. -/
def defiSet (G : Digraph V E) (k : ℕ) (r : V) (I : Finset E) (S : Finset V) : ℤ :=
  ∑ v ∈ S, G.defi k r I v

/-- The contracted graph: every vertex is replaced by its tight block (vertices of the contracted
graph are the blocks; other finsets of vertices are isolated). -/
def contract [Fintype V] [DecidableEq V] (G : Digraph V E) (k : ℕ) (I : Finset E) :
    Digraph (Finset V) E :=
  ⟨fun e => G.blockOf k I (G.tail e), fun e => G.blockOf k I (G.head e)⟩

/-- A basis of `Y` in `𝒢^k`: an independent subset of `Y` of maximum cardinality. -/
def IsBasisOf (G : Digraph V E) (k : ℕ) (B Y : Finset E) : Prop :=
  B ⊆ Y ∧ G.IndepK k B ∧ ∀ X, X ⊆ Y → G.IndepK k X → X.card ≤ B.card

end Digraph

/-- Total cost `c(X) = Σ_{e ∈ X} c(e)`. -/
def cost {α : Type} (c : α → ℝ) (X : Finset α) : ℝ := ∑ e ∈ X, c e

/-- The cost of a packing: the total cost of its arborescences. -/
def packingCost {k : ℕ} (c : E → ℝ) (P : Fin k → Finset E) : ℝ := ∑ i, cost c (P i)

/-- The paper's logarithm `log x = max{1, log₂ x}` (§3.1, p.7). -/
def logL (x : ℝ) : ℝ := max 1 (Real.logb 2 x)

/-- An input of Theorem 1.1: `n` vertices `Fin n`, `m` arcs `Fin m` with tails and heads, a root
`r`, an integer `k`, and real arc costs `c`. -/
structure Instance where
  n : ℕ
  m : ℕ
  k : ℕ
  r : Fin n
  tail : Fin m → Fin n
  head : Fin m → Fin n
  c : Fin m → ℝ

/-- The digraph of an instance. -/
def Instance.G (X : Instance) : Digraph (Fin X.n) (Fin X.m) := ⟨X.tail, X.head⟩

/-- The instance has a packing of `k` arc-disjoint `r`-arborescences. -/
def Instance.HasPacking (X : Instance) : Prop := ∃ P : Fin X.k → Finset (Fin X.m), X.G.IsPacking X.r X.k P

end MinCostArbPacking.Main


