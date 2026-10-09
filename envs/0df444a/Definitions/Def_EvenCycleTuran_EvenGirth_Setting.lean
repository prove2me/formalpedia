-- Prove2me | Definitions.Def_EvenCycleTuran_EvenGirth_Setting
-- name    : EvenCycleTuran_EvenGirth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:21.057494+00:00
-- url     : https://prove2.me/theorems/4edd36c9-901a-4acc-91bf-bd4c337eb3d9
-- title:
--   pp. 2–5, 20–21 — 𝒞_A-free graphs, ex(n, H, 𝒞_A), paths of length l, fat pairs and fat C₂ₗ's, the greedy multiplicity procedure, theta graphs
-- statement:
--   All graphs are finite and simple. For a graph $H$ and a graph $G$, a **copy** of $H$ in $G$ is a subgraph of $G$ isomorphic to $H$; $\mathcal N(H,G)$ is the number of copies (unlabelled copies). $C_a$ ($a\ge 3$) is the cycle of length $a$ and $P_l$ is the path on $l$ vertices, of length $l-1$.
--
--   1. **Forbidden cycle families.** For a set $A$ of integers, each at least $3$, write $\mathcal C_A=\{C_a : a\in A\}$. A graph is $\mathcal C_A$-free if it contains no $C_a$ with $a\in A$ as a (not necessarily induced) subgraph.
--   2. **Generalized Turán number.** For a graph $H$,
--   $$\mathrm{ex}(n,H,\mathcal C_A)=\max\{\mathcal N(H,G) : G \text{ a } \mathcal C_A\text{-free graph on } n \text{ vertices}\}.$$
--   3. **Paths of length $l$.** A path of $l$ edges from $a$ to $b$ is a sequence of $l+1$ distinct vertices $a=q_0,q_1,\dots,q_l=b$ with $q_{i-1}q_i$ an edge for every $i$. For distinct $a,b$, $f_l(a,b)$ is the number of such paths (paths, not walks).
--   4. **Fat pairs and fat cycles.** A pair $\{u,v\}$ is **fat** if $f_l(u,v)\ge 4l^2$. A copy of $C_{2l}$ is **fat** if all $l$ of its pairs of opposite vertices are fat. We also use the number of fat copies of $C_{2l}$ and the number of copies of $C_{2l}$ that are not fat.
--   5. **Multiplicity.** List the fat copies of $C_{2l}$ of $G$ in an arbitrary order, each exactly once. Go through them one by one, and from each pick one of its $2l$ subpaths of length $l-1$, always one that has been picked the smallest number of times so far. The **multiplicity** $m(Q)$ of a path $Q$ of length $l-1$ is the number of times it was picked.
--   6. **Theta graphs.** The $(l,t)$-theta-graph joins two vertices $x,y$ by $t$ internally disjoint paths of length $l$. For a simple graph $F$ the theta-$(n,F,l)$ graph replaces every edge of $F$ by an $(l,t)$-theta graph with $t=\lfloor (n-|V(F)|)/(|E(F)|(l-1))\rfloor$, and adds $n-(t|E(F)|(l-1)+|V(F)|)$ isolated vertices. We use $F=C_m$ for $m\ge3$ and $F=K_2$ for $m=2$.
--
--   These are the objects of Theorem 14 and of its proof in §5 of the paper.
--
--   **Formalization Note.** Graphs are `SimpleGraph (Fin n)` (or on a finite type `V`), copies are counted by Mathlib's `copyCount` (unlabelled), and $C_a$, $P_l$ are Mathlib's `cycleGraph a` and `pathGraph l`. `exCyc n H A` is the `sSup` of the set of copy counts of $\mathcal C_A$-free graphs on `Fin n`; this set is finite and, when every element of $A$ is at least $3$, contains the count of the empty graph, so the `sSup` is a true maximum. $f_l(a,b)$ is `pathCount G l a b`, the number of injective maps $q:\{0,\dots,l\}\to V$ with $q(0)=a$, $q(l)=b$ and consecutive vertices adjacent; for $a\ne b$ this is the number of paths, each read from $a$ to $b$. A cycle copy is a subgraph $C$ with an isomorphism $C_{r}\cong C$; a fat cycle is one with an isomorphism $e: C_{2l}\cong C$ under which every pair $e(i), e(i+l)$ is fat. A path of length $l-1$ inside a cycle $C$ is a subgraph $P\le C$ isomorphic to $P_l$, so subpaths are taken up to reversal. A greedy run is a list `cyc` of all fat copies of $C_{2l}$ without repetition together with the picks `pick t`, each a path of length $l-1$ of `cyc t` picked before at most as often as any other path of length $l-1$ of `cyc t`. `thetaCycle n m l` lives on `Fin n`: the vertices $0,\dots,m-1$ are the vertices of $F$, the edges of $F$ are $\{j,(j+1)\bmod m\}$ for $j<m$ (one edge $\{0,1\}$ when $m=2$), and the $l-1$ internal vertices of each of the $t$ paths are numbered consecutively from $m$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 2 (𝒞_A), p. 3 (ex(n, H, 𝓕)), p. 5 (Constructions: theta graphs), p. 20 (fat pairs, fat C_{2l}), p. 21 (greedy procedure, multiplicity m(Q)), p. 22 (f_l(a, b))

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting

namespace EvenCycleTuran.EvenGirth

open SimpleGraph Finset

/-- `q` is a path of `l` edges (on `l + 1` distinct vertices) from `a` to `b` in `G`. -/
def IsPathOfLength {V : Type*} (G : SimpleGraph V) (l : ℕ) (a b : V)
    (q : Fin (l + 1) → V) : Prop :=
  Function.Injective q ∧ q 0 = a ∧ q (Fin.last l) = b ∧
    ∀ i : Fin l, G.Adj (q i.castSucc) (q i.succ)

/-- f_l(a, b): the number of paths of `l` edges between `a` and `b` (paths, not walks; for
`a ≠ b` each path is counted once, as its vertex sequence read from `a` to `b`). -/
noncomputable def pathCount {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (a b : V) : ℕ := by
  classical exact Fintype.card {q : Fin (l + 1) → V // IsPathOfLength G l a b q}

/-- A pair `{u, v}` is fat if there are at least `4 l²` paths of length `l` between them. -/
def IsFatPair {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (u v : V) : Prop :=
  4 * l ^ 2 ≤ pathCount G l u v

/-- The subgraph `C` of `G` is a copy of the cycle `C_r`. -/
def IsCycleCopy {V : Type*} (G : SimpleGraph V) (r : ℕ) (C : G.Subgraph) : Prop :=
  Nonempty (cycleGraph r ≃g C.coe)

/-- A copy `C` of `C_{2l}` is fat if all its `l` pairs of opposite vertices are fat. -/
def IsFatCycle {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) (C : G.Subgraph) : Prop :=
  ∃ e : cycleGraph (2 * l) ≃g C.coe,
    ∀ i j : Fin (2 * l), j.val = i.val + l → IsFatPair G l (e i : V) (e j : V)

/-- `P` is a path of length `l - 1` (a copy of the path `P_l` on `l` vertices) inside `C`. -/
def IsSubpath {V : Type*} {G : SimpleGraph V} (l : ℕ) (C P : G.Subgraph) : Prop :=
  P ≤ C ∧ Nonempty (pathGraph l ≃g P.coe)

/-- Number of fat copies of `C_{2l}` in `G`. -/
noncomputable def fatCycleCount {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) : ℕ := by
  classical exact #{C : G.Subgraph | IsFatCycle G l C}

/-- Number of copies of `C_{2l}` in `G` that are not fat. -/
noncomputable def nonFatCycleCount {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ) : ℕ := by
  classical exact #{C : G.Subgraph | IsCycleCopy G (2 * l) C ∧ ¬ IsFatCycle G l C}

/-- In a run of the greedy procedure with picks `pick : Fin N → G.Subgraph`, the number of
steps before step `t` at which the path `P` was picked. -/
noncomputable def pickedBefore {V : Type*} {G : SimpleGraph V} {N : ℕ}
    (pick : Fin N → G.Subgraph) (t : Fin N) (P : G.Subgraph) : ℕ := by
  classical exact #{s : Fin N | s < t ∧ pick s = P}

/-- The multiplicity m(Q): the number of steps of the run at which the path `Q` was picked. -/
noncomputable def multiplicity {V : Type*} {G : SimpleGraph V} {N : ℕ}
    (pick : Fin N → G.Subgraph) (Q : G.Subgraph) : ℕ := by
  classical exact #{s : Fin N | pick s = Q}

/-- The greedy procedure of §5.2 (p. 21): `cyc` lists every fat copy of `C_{2l}` of `G` exactly
once, in an arbitrary order; at step `t` one path `pick t` of length `l - 1` of `cyc t` is
picked, and it is one that had been picked the smallest number of times before, among the
paths of length `l - 1` of `cyc t`. -/
structure IsGreedyRun {V : Type*} [Fintype V] (G : SimpleGraph V) (l N : ℕ)
    (cyc pick : Fin N → G.Subgraph) : Prop where
  cyc_injective : Function.Injective cyc
  cyc_fat : ∀ t, IsFatCycle G l (cyc t)
  cyc_surjective : ∀ C : G.Subgraph, IsFatCycle G l C → ∃ t, cyc t = C
  pick_subpath : ∀ t, IsSubpath l (cyc t) (pick t)
  pick_greedy : ∀ t, ∀ P : G.Subgraph, IsSubpath l (cyc t) P →
    pickedBefore pick t (pick t) ≤ pickedBefore pick t P

/-- Number of edges of the base graph `F` of the theta construction: `F = K₂` (one edge) when
`m = 2`, and `F = C_m` (`m` edges) when `m ≥ 3`. -/
def thetaBaseEdges (m : ℕ) : ℕ := if m = 2 then 1 else m

/-- `t = ⌊(n − |V(F)|) / (|E(F)| (l − 1))⌋`, the number of paths replacing each edge of `F`. -/
def thetaT (n m l : ℕ) : ℕ := (n - m) / (thetaBaseEdges m * (l - 1))

/-- Vertex label of the `i`-th vertex (`0 ≤ i ≤ l`) of the `p`-th path replacing the `j`-th
edge `{j, (j + 1) mod m}` of `F`: the endpoints are the vertices `j` and `(j + 1) mod m` of `F`,
and the `l - 1` internal vertices are fresh labels `≥ m`, numbered consecutively. -/
def thetaLabel (m l t j p i : ℕ) : ℕ :=
  if i = 0 then j
  else if i = l then (j + 1) % m
  else m + ((j * t + p) * (l - 1) + (i - 1))

/-- The theta-(n, C_m, l) graph (for `m ≥ 3`) and the theta-(n, K₂, l) graph (for `m = 2`) on
the vertex set `Fin n`: the vertices `0, …, m - 1` are the vertices of `F`, every edge of `F` is
replaced by `t = thetaT n m l` internally disjoint paths of length `l`, and the remaining
`n − (t |E(F)| (l − 1) + m)` vertices are isolated. -/
def thetaCycle (n m l : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v =>
    ∃ j < thetaBaseEdges m, ∃ p < thetaT n m l, ∃ i < l,
      u.val = thetaLabel m l (thetaT n m l) j p i ∧
        v.val = thetaLabel m l (thetaT n m l) j p (i + 1)

instance (n m l : ℕ) : DecidableRel (thetaCycle n m l).Adj := fun u v => by
  unfold thetaCycle
  rw [SimpleGraph.fromRel_adj]
  infer_instance

end EvenCycleTuran.EvenGirth


