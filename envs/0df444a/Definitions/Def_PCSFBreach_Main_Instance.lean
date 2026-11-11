-- Prove2me | Definitions.Def_PCSFBreach_Main_Instance
-- name    : PCSFBreach_Main_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:55:47.020999+00:00
-- url     : https://prove2.me/theorems/a203559a-5b51-458f-b6b5-5a6f11a76ce4
-- title:
--   Prize-Collecting Steiner Forest instances, forests, the objective c(F) + π(D̄(F)) and OPT
-- statement:
--   An instance of **Prize-Collecting Steiner Forest** (PCSF) consists of a vertex set $V=\{0,\dots,n-1\}$, a list of undirected edges $e=(u_e,v_e)$ with costs $c_e\ge 0$, and a list of demand pairs $i=\{s_i,t_i\}$ with penalties $\pi_i\ge 0$ (real numbers). Parallel edges, loops, repeated pairs and pairs with $s_i=t_i$ are allowed.
--
--   An edge set $F\subseteq E$ is a **forest** if no edge of $F$ is a loop and no edge of $F$ joins two vertices that are already connected by the other edges of $F$. For an edge set $F$, $D(F)$ is the set of pairs whose endpoints lie in the same connected component of $(V,F)$ and $\bar D(F)=D\setminus D(F)$. The objective is
--   $$\mathrm{cost}(F)=c(F)+\pi(\bar D(F))=\sum_{e\in F}c_e+\sum_{i\in\bar D(F)}\pi_i ,$$
--   and $\mathrm{OPT}=\min\{\mathrm{cost}(F): F\text{ a forest}\}$, a minimum over finitely many forests ($\emptyset$ is one).
--
--   The file also defines $\mathrm{sep}(U)=\{i: |U\cap\{s_i,t_i\}|=1\}$, $\delta(U)$ (edges with exactly one endpoint in $U$), $d_F(U)=|F\cap\delta(U)|$, "$F$ connects every pair of $P$", an **inclusion-wise minimal** subset $\hat F\subseteq F$ connecting $P$ (no proper subset of $\hat F$ connects $P$), and the instance $I|_P$ with the same graph and the pair set restricted to $P$ (its edge sets are edge sets of $I$).
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Edges and pairs are indexed by their positions in the lists; costs are real, rational data enter only through `RatInstance` for the algorithmic statements.
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 1, §1 (problem and objective); p. 4, §1.3 (sep, d_F)

import Mathlib
set_option autoImplicit false

namespace PCSFBreach.Main

/-- A **Prize-Collecting Steiner Forest instance** (Bosch-Calvo–Grandoni–Mátravölgyi, p. 1, §1;
p. 4, §1.3): vertices `Fin n`; an edge list, each edge `(u, v, c)` an undirected edge with
endpoints `u, v` and cost `c ≥ 0`; a list of demand pairs, each `(s, t, π)` a pair `{s, t}` with
penalty `π ≥ 0`. Costs and penalties are real numbers; the algorithmic statements take rational data
(`RatInstance`, Appendix B, p. 47). Parallel edges, loops, repeated pairs and `s = t` are allowed. -/
structure Instance where
  n : ℕ
  edges : List (Fin n × Fin n × ℝ)
  pairs : List (Fin n × Fin n × ℝ)
  edge_cost_nonneg : ∀ e ∈ edges, 0 ≤ e.2.2
  penalty_nonneg : ∀ p ∈ pairs, 0 ≤ p.2.2

namespace Instance

variable (I : Instance)

/-- Edge indices `E`. -/
abbrev Edge := Fin I.edges.length
/-- Pair indices `D`. -/
abbrev Pair := Fin I.pairs.length

/-- First endpoint of edge `e`. -/
def eu (e : I.Edge) : Fin I.n := (I.edges.get e).1
/-- Second endpoint of edge `e`. -/
def ev (e : I.Edge) : Fin I.n := (I.edges.get e).2.1
/-- Edge cost `c_e`. -/
def c (e : I.Edge) : ℝ := (I.edges.get e).2.2
/-- First endpoint `s_i` of pair `i`. -/
def s (i : I.Pair) : Fin I.n := (I.pairs.get i).1
/-- Second endpoint `t_i` of pair `i`. -/
def t (i : I.Pair) : Fin I.n := (I.pairs.get i).2.1
/-- Penalty `π_i` of pair `i`. -/
def pen (i : I.Pair) : ℝ := (I.pairs.get i).2.2

/-- The graph on `Fin n` whose adjacency is given by the edges of `F` (loops ignored). -/
def graph (F : Finset I.Edge) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel (fun x y => ∃ e ∈ F, I.eu e = x ∧ I.ev e = y)

/-- `x` and `y` lie in the same tree of the edge set `F`. -/
def Connected (F : Finset I.Edge) (x y : Fin I.n) : Prop := (I.graph F).Reachable x y

/-- `F` is a **forest**: no edge of `F` is a loop, and no edge of `F` joins two vertices already
connected by the other edges of `F` (multigraph acyclicity). -/
def IsForest (F : Finset I.Edge) : Prop :=
  ∀ e ∈ F, I.eu e ≠ I.ev e ∧ ¬ I.Connected (F.erase e) (I.eu e) (I.ev e)

/-- Edge `e` crosses the vertex set `U` (`e ∈ δ(U)`). -/
def Crosses (e : I.Edge) (U : Finset (Fin I.n)) : Prop :=
  (I.eu e ∈ U ∧ I.ev e ∉ U) ∨ (I.eu e ∉ U ∧ I.ev e ∈ U)

/-- Pair `i` is separated by `U`: `|U ∩ {s_i, t_i}| = 1`. -/
def Separates (U : Finset (Fin I.n)) (i : I.Pair) : Prop :=
  (I.s i ∈ U ∧ I.t i ∉ U) ∨ (I.s i ∉ U ∧ I.t i ∈ U)

open scoped Classical in
/-- `sep(U) = {i ∈ D : |U ∩ {s_i, t_i}| = 1}` (p. 4). -/
noncomputable def sep (U : Finset (Fin I.n)) : Finset I.Pair :=
  Finset.univ.filter (fun i => I.Separates U i)

open scoped Classical in
/-- `d_F(U) = |F ∩ δ(U)|` (p. 4). -/
noncomputable def dF (F : Finset I.Edge) (U : Finset (Fin I.n)) : ℕ :=
  (F.filter (fun e => I.Crosses e U)).card

open scoped Classical in
/-- `D(F)`: the pairs whose endpoints are in the same tree of `F`. -/
noncomputable def connectedPairs (F : Finset I.Edge) : Finset I.Pair :=
  Finset.univ.filter (fun i => I.Connected F (I.s i) (I.t i))

open scoped Classical in
/-- `D̄(F) = D \ D(F)`. -/
noncomputable def disconnectedPairs (F : Finset I.Edge) : Finset I.Pair :=
  Finset.univ.filter (fun i => ¬ I.Connected F (I.s i) (I.t i))

/-- `c(F) = Σ_{e ∈ F} c_e`. -/
def edgeCost (F : Finset I.Edge) : ℝ := ∑ e ∈ F, I.c e

/-- `π(P) = Σ_{i ∈ P} π_i`. -/
def penaltyOf (P : Finset I.Pair) : ℝ := ∑ i ∈ P, I.pen i

/-- The PCSF objective `cost(F) = c(F) + π(D̄(F))` (p. 1). -/
noncomputable def cost (F : Finset I.Edge) : ℝ := I.edgeCost F + I.penaltyOf (I.disconnectedPairs F)

open scoped Classical in
/-- All forests of the instance (a finite, nonempty family: `∅` is one). -/
noncomputable def forests : Finset (Finset I.Edge) := Finset.univ.filter (fun F => I.IsForest F)

/-- `∅` is a forest. -/
theorem empty_mem_forests : (∅ : Finset I.Edge) ∈ I.forests := by
  classical
  unfold forests
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun e he => absurd he (Finset.notMem_empty e)⟩

/-- `OPT(I) = min { cost(F) : F a forest of I }`, a genuine minimum over the finitely many forests. -/
noncomputable def OPT : ℝ := I.forests.inf' ⟨∅, I.empty_mem_forests⟩ I.cost

/-- `F` connects every pair of `P`. -/
def ConnectsAll (F : Finset I.Edge) (P : Finset I.Pair) : Prop :=
  ∀ i ∈ P, I.Connected F (I.s i) (I.t i)

/-- `F̂` is an inclusion-wise minimal subset of `F` connecting every pair of `P`. -/
def IsMinimalConnecting (Fhat : Finset I.Edge) (P : Finset I.Pair) (F : Finset I.Edge) : Prop :=
  Fhat ⊆ F ∧ I.ConnectsAll Fhat P ∧ ∀ F' ⊂ Fhat, ¬ I.ConnectsAll F' P

/-- The instance with the same graph and costs and pair set restricted to `P` (in the original
order); its edge indices are those of `I`. -/
def restrictPairs (P : Finset I.Pair) : Instance where
  n := I.n
  edges := I.edges
  pairs := ((List.finRange I.pairs.length).filter (fun i => decide (i ∈ P))).map I.pairs.get
  edge_cost_nonneg := I.edge_cost_nonneg
  penalty_nonneg := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
    exact I.penalty_nonneg _ (List.get_mem _ _)

/-- An edge set of a restricted instance, read as an edge set of `I` (same edge list). -/
def liftEdges (P : Finset I.Pair) (F : Finset (I.restrictPairs P).Edge) : Finset I.Edge := F

end Instance

end PCSFBreach.Main


