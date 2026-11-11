-- Prove2me | Definitions.Def_ImprovedSteinerForest_Main_Instance
-- name    : ImprovedSteinerForest_Main_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:26:44.576783+00:00
-- url     : https://prove2.me/theorems/08139632-94f1-4a4f-b690-7f288ed26a41
-- title:
--   Steiner Forest instances (multigraph, labelled demand pairs), feasibility, forests, opt, contraction G/𝒮, signatures and forest rows
-- statement:
--   A **Steiner Forest instance** consists of a finite undirected network on the vertices $V=\{0,\dots,n-1\}$, given as a list of edges $f=(u_f,v_f,c_f)$ with endpoints $u_f,v_f\in V$ and nonnegative rational costs $c_f\ge 0$, and a list of labelled demand pairs $(s_p,t_p)$, $p\in P$. Parallel edges, loops, repeated pairs and pairs with $s_p=t_p$ are allowed; list positions are the fixed orders on edges and demand labels used to break ties. For an edge set $F$, $c(F)=\sum_{f\in F}c_f$.
--
--   - $F$ is **feasible** if, for every demand $p$, $s_p$ and $t_p$ lie in one connected component of $(V,F)$; the instance is feasible if the set of all edges is feasible.
--   - $F$ is a **forest** if no edge of $F$ is a loop and no edge of $F$ joins two vertices already connected by the other edges of $F$.
--   - $\mathrm{opt}$ is the minimum of $c(F)$ over feasible edge sets $F$:
--   $$\mathrm{opt}=\min\{c(F): F\subseteq E_G \text{ feasible}\}.$$
--   - For a collection $\mathcal S$ of vertex sets, $F$ is a **feasible solution of $G/\mathcal S$** if every demand is connected in the graph with the edges of $F$ in which, in addition, all vertices of each $S\in\mathcal S$ are identified (overlapping sets transitively).
--   - $\delta(U)$-membership: an edge **crosses** $U$ if exactly one endpoint lies in $U$; the **demand signature** $\sigma(U)$ is the set of demands with exactly one endpoint in $U$.
--   - The **endpoints** of the demand list are the distinct vertices $s_p,t_p$; $F$ **connects** a vertex set $T$ if all of $T$ lies in one component of $(V,F)$, and $F$ is a **Steiner tree** on $T$ if it is a forest connecting $T$ each of whose edges lies in the component of $T$.
--   - For a forest $F$ and an edge $f$, the **row** $w_f\in\mathbb F_2^P$ has $w_f(p)=1$ exactly when $f$ lies on the path of $p$ in $F$, i.e. $s_p,t_p$ are connected in $F$ but not in $F\setminus\{f\}$. For a label set $K\subseteq P$, $\mathbb F_2^K$ is identified with the vectors of $\mathbb F_2^P$ that vanish outside $K$.
--
--   These are the objects of §1 and §2.1 and the rows of §5.1.
--
--   **Formalization Note.** Vertices are `Fin n`; edges and demands are indexed by their list positions (`Fin edges.length`, `Fin pairs.length`). Costs are in `ℚ`. `opt` is a genuine minimum over the finite nonempty family of feasible edge sets whenever the instance is feasible; on an infeasible instance it is `0`, a value never used (every statement assumes feasibility). Connectivity is reachability in a `SimpleGraph` built from the edges (loops ignored).
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 4, §1; p. 13, §2.1; p. 26, §5.1; p. 42, App. A.2

import Mathlib
set_option autoImplicit false

namespace ImprovedSteinerForest.Main

/-- A **Steiner Forest instance** (Cheshm Jahan et al., p. 4 and p. 13, §2.1): a finite undirected
network on the vertices `Fin n`, given as an edge list whose entries `(u, v, c)` are edges with
endpoints `u, v` and nonnegative rational cost `c`, and a list of labelled demand pairs `(s, t)`.
Parallel edges, loops, repeated pairs and pairs with `s = t` are allowed (contraction, p. 13,
produces parallel edges; demands with equal endpoints keep distinct labels). The list positions are
the fixed orders on edges and demand labels used to break ties (p. 13). -/
structure Instance where
  n : ℕ
  edges : List (Fin n × Fin n × ℚ)
  pairs : List (Fin n × Fin n)
  cost_nonneg : ∀ e ∈ edges, 0 ≤ e.2.2

namespace Instance

variable (I : Instance)

/-- Edge labels `E_G`. -/
abbrev Edge := Fin I.edges.length
/-- Demand labels `P`. -/
abbrev Pair := Fin I.pairs.length

/-- First endpoint of edge `f`. -/
def eu (f : I.Edge) : Fin I.n := (I.edges.get f).1
/-- Second endpoint of edge `f`. -/
def ev (f : I.Edge) : Fin I.n := (I.edges.get f).2.1
/-- Cost `c_f` of edge `f`. -/
def c (f : I.Edge) : ℚ := (I.edges.get f).2.2
/-- First endpoint `s_p` of demand `p`. -/
def s (p : I.Pair) : Fin I.n := (I.pairs.get p).1
/-- Second endpoint `t_p` of demand `p`. -/
def t (p : I.Pair) : Fin I.n := (I.pairs.get p).2

/-- `c(F) = Σ_{f ∈ F} c_f`. -/
def cost (F : Finset I.Edge) : ℚ := ∑ f ∈ F, I.c f

/-- The graph on `Fin n` whose adjacency is given by the edges of `F` (loops ignored). -/
def graph (F : Finset I.Edge) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel (fun x y => ∃ f ∈ F, I.eu f = x ∧ I.ev f = y)

/-- `x` and `y` lie in one connected component of `(V, F)`. -/
def Connected (F : Finset I.Edge) (x y : Fin I.n) : Prop := (I.graph F).Reachable x y

/-- `F` is **feasible**: it connects `s_p` and `t_p` for every demand `p` (p. 4). -/
def Feasible (F : Finset I.Edge) : Prop := ∀ p : I.Pair, I.Connected F (I.s p) (I.t p)

/-- `F` is a **forest**: no edge of `F` is a loop, and no edge of `F` joins two vertices already
connected by the other edges of `F` (multigraph acyclicity). -/
def IsForest (F : Finset I.Edge) : Prop :=
  ∀ f ∈ F, I.eu f ≠ I.ev f ∧ ¬ I.Connected (F.erase f) (I.eu f) (I.ev f)

/-- The instance is **feasible**: some edge set connects every demand pair (equivalently, the set
of all edges does). -/
def IsFeasibleInst : Prop := I.Feasible Finset.univ

open scoped Classical in
/-- The feasible edge sets. -/
noncomputable def feasibleSets : Finset (Finset I.Edge) :=
  Finset.univ.filter (fun F => I.Feasible F)

open scoped Classical in
/-- `opt`, the minimum cost of a feasible edge set (p. 4), a genuine minimum over the finitely many
feasible edge sets whenever the instance is feasible. On an infeasible instance (never used) the
value is `0`. -/
noncomputable def opt : ℚ :=
  if h : I.feasibleSets.Nonempty then I.feasibleSets.inf' h I.cost else 0

/-- Graph on `Fin n` with the edges of `F` and, for every set `S ∈ 𝒮`, all pairs of vertices
of `S` joined: the graph `G/𝒮` before identifying (chains of overlapping sets become one vertex,
p. 13). -/
def graphMod (𝒮 : Finset (Finset (Fin I.n))) (F : Finset I.Edge) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel (fun x y => (∃ f ∈ F, I.eu f = x ∧ I.ev f = y) ∨ ∃ S ∈ 𝒮, x ∈ S ∧ y ∈ S)

/-- `F` is a feasible solution of the contracted instance `G/𝒮` (p. 13): after identifying the
vertices of each set of `𝒮`, `F` connects both endpoints of every demand. -/
def FeasibleMod (𝒮 : Finset (Finset (Fin I.n))) (F : Finset I.Edge) : Prop :=
  ∀ p : I.Pair, (I.graphMod 𝒮 F).Reachable (I.s p) (I.t p)

/-- Edge `f` crosses `U` (`f ∈ δ(U)`): exactly one endpoint of `f` belongs to `U` (p. 13). -/
def Crosses (f : I.Edge) (U : Finset (Fin I.n)) : Prop :=
  (I.eu f ∈ U ∧ I.ev f ∉ U) ∨ (I.eu f ∉ U ∧ I.ev f ∈ U)

/-- `U` separates demand `p`: exactly one of `s_p, t_p` belongs to `U`. -/
def Separates (U : Finset (Fin I.n)) (p : I.Pair) : Prop :=
  (I.s p ∈ U ∧ I.t p ∉ U) ∨ (I.s p ∉ U ∧ I.t p ∈ U)

open scoped Classical in
/-- The demand signature `σ(U) = {p ∈ P : exactly one of s_p, t_p ∈ U}` (p. 13). -/
noncomputable def sigma (U : Finset (Fin I.n)) : Finset I.Pair :=
  Finset.univ.filter (fun p => I.Separates U p)

open scoped Classical in
/-- The distinct endpoints `{s_p, t_p : p ∈ P}` of the demand pairs. -/
noncomputable def endpoints : Finset (Fin I.n) := Finset.univ.image I.s ∪ Finset.univ.image I.t

/-- `F` connects every vertex of `T` to every other (a connector of `T`). -/
def ConnectsSet (F : Finset I.Edge) (T : Finset (Fin I.n)) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, I.Connected F u v

/-- `F` is a **Steiner tree** on `T`: a forest connecting all of `T`, each of whose edges lies in the
component of `T` (so its edges form a single tree when `T` is nonempty). -/
def IsSteinerTree (F : Finset I.Edge) (T : Finset (Fin I.n)) : Prop :=
  I.IsForest F ∧ I.ConnectsSet F T ∧ ∀ f ∈ F, ∃ v ∈ T, I.Connected F (I.eu f) v

open scoped Classical in
/-- The **row** `w_f ∈ F₂^P` of edge `f` in the forest `F` (§5.1, p. 26): `w_f(p) = 1` iff `f` lies on
the path of `p` in `F`, i.e. `s_p, t_p` are connected in `F` but not in `F \ {f}`. -/
noncomputable def row (F : Finset I.Edge) (f : I.Edge) : I.Pair → ZMod 2 :=
  fun p => if I.Connected F (I.s p) (I.t p) ∧ ¬ I.Connected (F.erase f) (I.s p) (I.t p) then 1 else 0

/-- The vectors of `F₂^P` supported on the label set `K` (vectors of `F₂^K` extended by zero). -/
def supportedOn (K : Finset I.Pair) : Submodule (ZMod 2) (I.Pair → ZMod 2) where
  carrier := {x | ∀ p, p ∉ K → x p = 0}
  add_mem' := by
    intro x y hx hy p hp
    simp [hx p hp, hy p hp]
  zero_mem' := by
    intro p _
    rfl
  smul_mem' := by
    intro a x hx p hp
    simp [hx p hp]

end Instance

end ImprovedSteinerForest.Main


