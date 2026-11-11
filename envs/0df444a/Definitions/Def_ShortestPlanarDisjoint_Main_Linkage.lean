-- Prove2me | Definitions.Def_ShortestPlanarDisjoint_Main_Linkage
-- name    : ShortestPlanarDisjoint_Main_Linkage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:00.933217+00:00
-- url     : https://prove2.me/theorems/8f44830d-94bb-47b3-a2be-ab9f7799b203
-- title:
--   Linkages, prescribed pairings and the original objective
-- statement:
--   Let $G$ be a finite undirected simple graph on $\{0,\ldots,n-1\}$. Its $2k$
--   terminal vertices are distinct, and a fixed-point-free involution $M$ pairs their
--   labels. Each pair is represented once by its smaller label. A linkage consists
--   of a simple graph path for every such pair, with the full vertex supports of
--   different paths disjoint. There is no requirement that an individual path be
--   shortest between its endpoints.
--
--   For nonnegative integer costs $w$ on unordered vertex pairs, define
--
--   $$\operatorname{cost}_w(L)=\sum_{P\in L}\sum_{e\in E(P)}w(e).$$
--
--   An optimal linkage has cost no larger than every other linkage. The optimum-value
--   relation distinguishes infeasibility, represented by no value, from an attained
--   value of zero. Costs on nonedges are unused. This definition supplies the objective
--   independently of any algorithm and permits disconnected graphs, zero-cost edges
--   and an empty terminal family. The graph and its walks are Mathlib objects; the
--   paper-specific layer only adds terminal pairing, disjointness and the objective.
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Sections 1–2 (linkage and objective), p. 4 (PDF p. 6)

import Mathlib

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- A perfect pairing of the terminal labels, without an orientation choice. -/
structure TerminalPairing (k : ℕ) where
  mate : Fin (2 * k) → Fin (2 * k)
  involutive : Function.Involutive mate
  no_fixed : ∀ i, mate i ≠ i

/-- Each unordered pair is represented once, by its smaller label. -/
def TerminalPairing.starts {k : ℕ} (M : TerminalPairing k) :=
  {i : Fin (2 * k) // i < M.mate i}

/-- The graph is Mathlib's general simple graph; costs are on unordered vertex pairs.
Only costs on actual edges are used or encoded. No embedding is part of this input. -/
structure RoutingInput (n k : ℕ) where
  graph : SimpleGraph (Fin n)
  terminal : Fin (2 * k) → Fin n
  terminals_distinct : Function.Injective terminal
  pairing : TerminalPairing k
  weight : Sym2 (Fin n) → ℕ

/-- One ordinary simple path per prescribed unordered pair. Disjointness concerns
all support vertices, including endpoints. No minimum-path condition is imposed. -/
structure Linkage {n k : ℕ} (I : RoutingInput n k) where
  path : ∀ i : I.pairing.starts,
    I.graph.Walk (I.terminal i.val) (I.terminal (I.pairing.mate i.val))
  simple : ∀ i, (path i).IsPath
  disjoint : ∀ i j, i ≠ j → List.Disjoint (path i).support (path j).support

noncomputable section

/-- The actual finite edge set, used for independent perturbations. -/
def RoutingInput.Edge {n k : ℕ} (I : RoutingInput n k) :=
  {e : Sym2 (Fin n) // e ∈ I.graph.edgeSet}

instance {n k : ℕ} (I : RoutingInput n k) : Fintype I.Edge := by
  unfold RoutingInput.Edge
  exact Fintype.ofFinite _
instance {k : ℕ} (M : TerminalPairing k) : Fintype M.starts := by
  unfold TerminalPairing.starts
  exact Fintype.ofFinite _

/-- Sum of edge costs along all the paths, with each prescribed pair counted once. -/
def Linkage.costWith {n k : ℕ} {I : RoutingInput n k} (L : Linkage I)
    (w : Sym2 (Fin n) → ℕ) : ℕ :=
  ∑ i : I.pairing.starts, ((L.path i).edges.map w).sum

def Linkage.cost {n k : ℕ} {I : RoutingInput n k} (L : Linkage I) : ℕ :=
  L.costWith I.weight

/-- The original objective, including attainment, with no empty-family default. -/
def Linkage.IsOptimal {n k : ℕ} {I : RoutingInput n k} (L : Linkage I) : Prop :=
  ∀ L' : Linkage I, L.cost ≤ L'.cost

/-- A minimum for an arbitrary weight assignment, used only for isolation. -/
def Linkage.IsMinimumFor {n k : ℕ} {I : RoutingInput n k} (w : Sym2 (Fin n) → ℕ)
    (L : Linkage I) : Prop := ∀ L' : Linkage I, L.costWith w ≤ L'.costWith w

/-- A zero-aware specification of optimum value: None means no linkage, while
Some 0 means an attained zero-cost linkage. It is independent of any algorithm. -/
def OptimumValue {n k : ℕ} (I : RoutingInput n k) (v : Option ℕ) : Prop :=
  match v with
  | none => IsEmpty (Linkage I)
  | some d => ∃ L : Linkage I, L.cost = d ∧ L.IsOptimal

end
end ShortestPlanarDisjoint.Main


