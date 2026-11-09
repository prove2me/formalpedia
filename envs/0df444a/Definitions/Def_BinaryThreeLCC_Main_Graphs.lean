-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_Graphs
-- name    : BinaryThreeLCC_Main_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:10.012647+00:00
-- url     : https://prove2.me/theorems/28035e8c-ec2e-4a59-92b9-b3d6f187144b
-- title:
--   Directed expansion, coloured multigraphs, cycles and local variance
-- statement:
--   Start with the published finite multigraph skeleton: each labelled edge copy has two endpoints. Read the endpoints in order for directed graphs and disregard their order for undirected graphs. Incoming and outgoing degrees count directed loops once each. Eulerian means equality of these degrees at every vertex. Cut density means
--
--   $$e_D(S,V\setminus S)\ge\lambda|S|\,|V\setminus S|\quad(S\subseteq V).$$
--
--   Subgraphs select vertex and edge subsets and retain endpoints. A coloured graph adds an arbitrary palette map on edge copies. Undirected degree counts a loop twice. Cycles have distinct vertices and edge identities, with loops of length one and parallel-edge cycles of length two allowed. Unique-colour, odd-coloured and rainbow cycle predicates are distinct. Colour degree counts used colours. All finite averages are uniform, and
--
--   $$\mathcal V=\frac1{|V|}\sum_v\frac1k\sum_i\left(d_i(v)-\frac{d(v)}k\right)^2.$$
--
--   The relevant theorem hypotheses make averaging sets nonempty; unused palette colours are retained.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Definition 3.1, printed pp.8–9, PDF pp.10–11; Definitions 3.3 and 3.5, printed p.9, PDF p.11; Equation (2), printed p.14, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Mathlib
import Definitions.Def_ContPatrol_Multigraph

set_option autoImplicit false

namespace BinaryThreeLCC.Main

open ContPatrol

noncomputable def average {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

noncomputable def outDegree {V E : Type} [Fintype E] (G : Multigraph V E) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => G.src e = v)).card

noncomputable def inDegree {V E : Type} [Fintype E] (G : Multigraph V E) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => G.tgt e = v)).card

def Eulerian {V E : Type} [Fintype E] (G : Multigraph V E) : Prop :=
  ∀ v, inDegree G v = outDegree G v

def NoParallel {V E : Type} (G : Multigraph V E) : Prop :=
  Function.Injective (fun e => (G.src e, G.tgt e))

noncomputable def directedCut {V E : Type} [Fintype E]
    (G : Multigraph V E) (S T : Finset V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => G.src e ∈ S ∧ G.tgt e ∈ T)).card

noncomputable def CutDense {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (lam : ℝ) : Prop := by
  classical
  exact ∀ S : Finset V, (directedCut G S (Finset.univ \ S) : ℝ) ≥
    lam * S.card * (Finset.univ \ S).card

structure DirectedSubgraph {V E : Type} (G : Multigraph V E) where
  vertices : Finset V
  edges : Finset E
  endpoints : ∀ e ∈ edges, G.src e ∈ vertices ∧ G.tgt e ∈ vertices

def DirectedSubgraph.graph {V E : Type} {G : Multigraph V E} (D : DirectedSubgraph G) :
    Multigraph D.vertices D.edges where
  src e := ⟨G.src e.val, (D.endpoints e.val e.property).1⟩
  tgt e := ⟨G.tgt e.val, (D.endpoints e.val e.property).2⟩

def nextIndex {l : ℕ} (i : Fin l) : Fin l :=
  ⟨(i.val + 1) % l, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- Simple closed directed cycle, including a loop as a cycle of length one. -/
def DirectedCycle {V E : Type} (G : Multigraph V E) (l : ℕ)
    (v : Fin l → V) (e : Fin l → E) : Prop :=
  0 < l ∧ Function.Injective v ∧ Function.Injective e ∧
    ∀ i, G.src (e i) = v i ∧ G.tgt (e i) = v (nextIndex i)

/-- The orientation of each edge is bookkeeping, not a restriction on an undirected edge. -/
structure ColouredGraph (V E I : Type) where
  graph : Multigraph V E
  colour : E → I

noncomputable def colourDegree {V E I : Type} [Fintype E]
    (G : ColouredGraph V E I) (v : V) (i : I) : ℕ := by
  classical
  exact ∑ e : E, ((if G.colour e = i ∧ G.graph.src e = v then 1 else 0) +
    (if G.colour e = i ∧ G.graph.tgt e = v then 1 else 0))

noncomputable def totalDegree {V E I : Type} [Fintype E]
    (G : ColouredGraph V E I) (v : V) : ℕ := by
  classical
  exact G.graph.deg v

noncomputable def numberOfColours {V E I : Type} [Fintype E] [Fintype I]
    (G : ColouredGraph V E I) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => 0 < colourDegree G v i)).card

/-- Edge copies cannot repeat. Two different parallel copies may form a length-two cycle. -/
def UndirectedCycle {V E : Type} (G : Multigraph V E) (l : ℕ)
    (v : Fin l → V) (d : Fin l → E × Bool) : Prop :=
  0 < l ∧ Function.Injective v ∧ Function.Injective (fun i => (d i).1) ∧
    ∀ i, G.tail (d i) = v i ∧ G.head (d i) = v (nextIndex i)

noncomputable def cycleColourCount {V E I : Type} (G : ColouredGraph V E I)
    {l : ℕ} (d : Fin l → E × Bool) (i : I) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => G.colour (d j).1 = i)).card

def NoUniqueColourCycle {V E I : Type} (G : ColouredGraph V E I) : Prop :=
  ∀ (l : ℕ) (v : Fin l → V) (d : Fin l → E × Bool),
    UndirectedCycle G.graph l v d → ∀ i, cycleColourCount G d i ≠ 1

def NoOddColourCycle {V E I : Type} (G : ColouredGraph V E I) : Prop :=
  ∀ (l : ℕ) (v : Fin l → V) (d : Fin l → E × Bool),
    UndirectedCycle G.graph l v d → ∀ i, Even (cycleColourCount G d i)

def RainbowCycle {V E I : Type} (G : ColouredGraph V E I) (l : ℕ)
    (v : Fin l → V) (d : Fin l → E × Bool) : Prop :=
  UndirectedCycle G.graph l v d ∧ Function.Injective (fun j => G.colour (d j).1)

noncomputable def localVariance {V E I : Type} [Fintype V] [Fintype E] [Fintype I]
    (G : ColouredGraph V E I) : ℝ :=
  average (fun v => average (fun i =>
    ((colourDegree G v i : ℝ) - (totalDegree G v : ℝ) / Fintype.card I) ^ 2))

end BinaryThreeLCC.Main


