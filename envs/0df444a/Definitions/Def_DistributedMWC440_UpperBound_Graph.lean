-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Graph
-- name    : DistributedMWC440_UpperBound_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:23:31.289375+00:00
-- url     : https://prove2.me/theorems/3ac83262-29c1-434d-9ff3-abca537ce9ca
-- title:
--   Weighted networks, simple cycles, and finite or infinite distances
-- statement:
--   The graph carrier is the published weighted simple graph. Cycles are nonempty closed Mathlib walks with no repeated edge or internal vertex. Their objective is the sum of actual traversed lengths. The extended optimum is infinity when there is no cycle; unrestricted and hop-bounded distances are infima of actual walks in the extended nonnegative reals. The input layer records connectedness, positive integer edge weights, polynomial weight and ID bounds, and arbitrary local port orders. Segment and visibility definitions follow the cycle edges. Parent trees are required only on finite-labelled vertices. This supplies the common graph and distance interface.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, §§1, 3–7, printed pp. 1–43 / PDF pp. 3–45.

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_WeightedGraph

open scoped ENNReal

noncomputable section

namespace DistributedMWC440.UpperBound

abbrev WGraph := OuterplanarL1Tan.Linear.WeightedGraph

/-- Sum over traversed edges, including repeated traversals. -/
abbrev walkWeight {V : Type} (W : WGraph V) {u v : V} (P : W.graph.Walk u v) : ℝ :=
  OAI.PlanarL1.walkLength W.length P

structure Cycle {V : Type} (W : WGraph V) where
  root : V
  walk : W.graph.Walk root root
  simple : walk.IsCycle

abbrev Cycle.weight {V : Type} {W : WGraph V} (C : Cycle W) := walkWeight W C.walk

def IsMinimum {V : Type} {W : WGraph V} (C : Cycle W) : Prop :=
  ∀ C' : Cycle W, C.weight ≤ C'.weight

/-- Infimum in the extended nonnegative reals: empty cycle family has value infinity. -/
def optimum {V : Type} (W : WGraph V) : ℝ≥0∞ :=
  ⨅ C : Cycle W, ENNReal.ofReal C.weight

/-- Infinite on unreachable pairs, and the published weighted walk-distance otherwise. -/
def edist {V : Type} (W : WGraph V) (u v : V) : ℝ≥0∞ :=
  ⨅ p : W.graph.Walk u v, ENNReal.ofReal (walkWeight W p)

abbrev dist {V : Type} (W : WGraph V) := W.distance

def setDist {V : Type} (W : WGraph V) (v : V) (R : Finset V) : ℝ :=
  sInf {a | ∃ r ∈ R, a = dist W v r}

/-- The network graph and length structure are reused, rather than redefined. -/
structure Network (n : ℕ) (q idExponent : ℕ) where
  W : WGraph (Fin n)
  connected : W.graph.Connected
  weight : Fin n → Fin n → ℕ
  weight_eq : ∀ u v, W.graph.Adj u v → W.length u v = (weight u v : ℝ)
  weight_pos : ∀ u v, W.graph.Adj u v → 0 < weight u v
  weight_bound : ∀ u v, W.graph.Adj u v → weight u v ≤ n ^ q
  id : Fin n → ℕ
  id_injective : Function.Injective id
  id_bound : ∀ v, id v < (max 2 n) ^ idExponent
  /-- A private port order. Knowing a port does not reveal a neighbor ID. -/
  ports : (v : Fin n) → Fin (W.graph.neighborSet v).ncard ≃ W.graph.neighborSet v

/-- Unweighted graph distance, maximized over the finite vertex pairs. -/
def diameter {n q b : ℕ} (I : Network n q b) : ℝ :=
  sSup {a | ∃ u v : Fin n, a = (I.W.graph.dist u v : ℝ)}

/-- A segment follows cycle edges, has distinct skeleton endpoints and no internal skeleton nodes. -/
def IsSegment {V : Type} {W : WGraph V} (C : Cycle W) (R : Finset V)
    {u v : V} (P : W.graph.Walk u v) : Prop :=
  u ∈ R ∧ v ∈ R ∧ u ≠ v ∧ P.IsPath ∧
  (∀ e ∈ P.edges, e ∈ C.walk.edges) ∧
  ∀ z ∈ P.support.tail.dropLast, z ∉ R

def SegmentBound {V : Type} {W : WGraph V} (C : Cycle W) (R : Finset V) (L : ℝ) : Prop :=
  ∀ u v (P : W.graph.Walk u v), IsSegment C R P → (P.length : ℝ) ≤ L

def Visible {V : Type} {W : WGraph V} (C : Cycle W) (q : V)
    {u v : V} (P : W.graph.Walk u v) (radius : ℝ) : Prop :=
  ∃ r, (r = u ∨ r = v) ∧ ∃ Q : W.graph.Walk q r,
    Q.IsPath ∧ (∀ e ∈ Q.edges, e ∈ C.walk.edges) ∧
    (∀ e ∈ P.edges, e ∈ Q.edges) ∧ walkWeight W Q ≤ radius

/-- The unrestricted and h-hop distances are extended values even on disconnected auxiliaries. -/
def hopDist {V : Type} (W : WGraph V) (x v : V) (h : ℕ) : ℝ≥0∞ :=
  ⨅ (P : W.graph.Walk x v) (_ : P.length ≤ h), ENNReal.ofReal (walkWeight W P)

def HopApprox {V : Type} (W : WGraph V) (x : V) (h : ℕ) (ε : ℝ)
    (label : V → ℝ≥0∞) : Prop :=
  ∀ v, edist W x v ≤ label v ∧ label v ≤ ENNReal.ofReal (1 + ε) * hopDist W x v h

/-- Depth and parent pointers certify an actual rooted tree on the finite-labelled vertices. -/
structure HopTree {V : Type} (W : WGraph V) (x : V) where
  label : V → ℝ≥0∞
  parent : V → V
  depth : V → ℕ
  root_label : label x = 0
  root_parent : parent x = x
  root_depth : depth x = 0
  edge : ∀ v, v ≠ x → label v ≠ ⊤ → W.graph.Adj (parent v) v
  finite_parent : ∀ v, v ≠ x → label v ≠ ⊤ → label (parent v) ≠ ⊤
  descent : ∀ v, v ≠ x → label v ≠ ⊤ →
    label (parent v) + ENNReal.ofReal (W.length (parent v) v) ≤ label v
  depth_step : ∀ v, v ≠ x → label v ≠ ⊤ → depth (parent v) + 1 = depth v
  zero_depth : ∀ v, label v ≠ ⊤ → depth v = 0 → v = x

def HopTree.heightBound {V : Type} {W : WGraph V} {x : V}
    (T : HopTree W x) (H : ℝ) : Prop :=
  ∀ v, T.label v ≠ ⊤ → (T.depth v : ℝ) ≤ H

end DistributedMWC440.UpperBound


