-- Prove2me | Definitions.Def_ChenCapacityTerminals_Exact_Network
-- name    : ChenCapacityTerminals_Exact_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:23.826516+00:00
-- url     : https://prove2.me/theorems/8a2c7285-dd5e-402c-a894-40c027c59ad0
-- title:
--   Arc-record networks, entering cuts, restrictions and flow answers
-- statement:
--   A directed network consists of a finite vertex carrier and an ordered list of arc records, each with an original tail, head and finite real capacity. Valid networks have nonnegative capacities and endpoints in the carrier. The underlying incidence structure is the published directed multigraph; this layer supplies arc-list input, capacities and entering-shore conventions.
--
--   For vertex sets $A,C$, let $w(A,C)$ sum the capacities of records from $A$ into $C$. The entering-cut function and a vertex mass are
--   $$f(X)=w(V\setminus X,X),\qquad b(X)=\sum_{v\in X}b(v).$$
--   Rooted shores are nonempty sets excluding the root, pair shores also contain the terminal, and global shores are nonempty proper subsets. Optimality compares against every admissible shore. Restriction identifies the exterior with the root, drops loops and root-entering records and coalesces parallel records. Conditioning at rate $\eta$ means $f(X)\ge\eta b(X)$ for every nonroot subset, including the empty set.
--
--   The file also defines the exact coefficient $C_d=4d(3+\lceil\log_2 n\rceil)$, the weighted threshold, normalized masses and network sizes, and the augmented enclosure network. A fixed-pair answer includes an arc-indexed feasible flow and a shore with equal cut value. No optimizer is part of a network’s input data.
--
--   **Formalization Note** These mathematical definitions specify the objects that machine computations must realize; coalescing and restriction are not free machine instructions.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 1–10, PDF p. 2–11, §§1–4.1; Eqs. (2)–(3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=2–11

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

set_option autoImplicit false

namespace ChenCapacityTerminals.Exact

/-- Arc records retain their order and multiplicity. Labels are original natural-number labels. -/
structure Arc where
  tail : ℕ
  head : ℕ
  capacity : ℝ
  deriving Inhabited

/-- A finite directed network; validity is a separate predicate, not a conclusion in the data. -/
structure Network where
  vertices : Finset ℕ
  arcs : List Arc

/-- The published general directed multigraph, indexed by original arc positions. The list
is its arc-record I/O layer; capacities and the finite vertex carrier are separate data. -/
def Network.incidence (G : Network) : CombOpt.MinCostFlow.Digraph ℕ (Fin G.arcs.length) :=
  ⟨fun i => (G.arcs.get i).tail, fun i => (G.arcs.get i).head⟩

def Network.Valid (G : Network) : Prop :=
  ∀ e ∈ G.arcs, e.tail ∈ G.vertices ∧ e.head ∈ G.vertices ∧ 0 ≤ e.capacity

def Network.size (G : Network) : ℕ := G.vertices.card + G.arcs.length

def weight (G : Network) (A C : Finset ℕ) : ℝ :=
  (G.arcs.map fun e => if e.tail ∈ A ∧ e.head ∈ C then e.capacity else 0).sum

def cut (G : Network) (X : Finset ℕ) : ℝ := weight G (G.vertices \ X) X

def RootSide (G : Network) (r : ℕ) (X : Finset ℕ) : Prop :=
  X ⊆ G.vertices ∧ X.Nonempty ∧ r ∉ X

def PairSide (G : Network) (r t : ℕ) (X : Finset ℕ) : Prop :=
  RootSide G r X ∧ t ∈ X

def GlobalSide (G : Network) (X : Finset ℕ) : Prop :=
  X ⊆ G.vertices ∧ X.Nonempty ∧ X ≠ G.vertices

def OptimalRoot (G : Network) (r : ℕ) (X : Finset ℕ) : Prop :=
  RootSide G r X ∧ ∀ Y, RootSide G r Y → cut G X ≤ cut G Y

def OptimalPair (G : Network) (r t : ℕ) (X : Finset ℕ) : Prop :=
  PairSide G r t X ∧ ∀ Y, PairSide G r t Y → cut G X ≤ cut G Y

def OptimalGlobal (G : Network) (X : Finset ℕ) : Prop :=
  GlobalSide G X ∧ ∀ Y, GlobalSide G Y → cut G X ≤ cut G Y

/-- Equivalent to L ≤ λ without choosing an optimizer or using a default-valued infimum. -/
def RootLowerBound (G : Network) (r : ℕ) (L : ℝ) : Prop :=
  ∀ X, RootSide G r X → L ≤ cut G X

def mass (b : ℕ → ℕ) (X : Finset ℕ) : ℕ := ∑ v ∈ X, b v

def indegree (G : Network) (v : ℕ) : ℕ := (G.arcs.filter fun e => e.head = v).length

def Conditioned (G : Network) (r : ℕ) (b : ℕ → ℕ) (η : ℝ) : Prop :=
  ∀ X ⊆ G.vertices \ {r}, η * (mass b X : ℝ) ≤ cut G X

/-- Coalescing is specified mathematically here; no operation in the machine evaluates this
function for free. Zero records, loops and arcs entering the designated root disappear. -/
noncomputable def coalesce (G : Network) (r : ℕ) : Network := by
  classical
  exact ⟨G.vertices,
    ((G.vertices.product G.vertices).toList.filter fun p =>
      p.1 ≠ p.2 ∧ p.2 ≠ r ∧ 0 < weight G {p.1} {p.2}).map fun p =>
        ⟨p.1, p.2, weight G {p.1} {p.2}⟩⟩

/-- Only subsets of the retained region keep their cuts. The root remains an original label. -/
noncomputable def restrict (G : Network) (r : ℕ) (C : Finset ℕ) : Network :=
  coalesce ⟨insert r C, G.arcs.map fun e =>
    ⟨if e.tail ∈ C then e.tail else r,
     if e.head ∈ C then e.head else r, e.capacity⟩⟩ r

def reverseNetwork (G : Network) : Network :=
  ⟨G.vertices, G.arcs.map fun e => ⟨e.head, e.tail, e.capacity⟩⟩

def PositiveReachable (G : Network) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => ∃ e ∈ G.arcs,
    e.tail = a ∧ e.head = c ∧ 0 < e.capacity) u v

/-- Section 2's preprocessed, positive rooted orientation. No minimum value is supplied. -/
def Prepared (G : Network) (r : ℕ) : Prop :=
  G.Valid ∧ r ∈ G.vertices ∧ 2 ≤ G.vertices.card ∧
  (∀ e ∈ G.arcs, e.tail ≠ e.head ∧ e.head ≠ r ∧ 0 < e.capacity) ∧
  (G.arcs.map fun e => (e.tail, e.head)).Nodup ∧
  ∀ v ∈ G.vertices, PositiveReachable G r v

def ceilLog₂ (n : ℕ) : ℕ := Nat.log2 n + if n = 2 ^ Nat.log2 n then 0 else 1

def terminalCoefficient (n d : ℕ) : ℕ := 4 * d * (3 + ceilLog₂ n)

def separatorThreshold (G : Network) (d : ℕ) : ℕ :=
  (G.size * d + G.vertices.card - 1) / G.vertices.card

def indegreeMass (G : Network) (r v : ℕ) : ℕ :=
  if v = r then 1 else 1 + indegree G v

def normalizedMass (G : Network) (r v : ℕ) : ℕ :=
  if v = r then 1 else
    1 + (G.vertices.card * indegree G v + G.size - 1) / G.size

noncomputable def normalizedSize (n M : ℕ) (H : Network) : ℝ :=
  (H.vertices.card : ℝ) + (n : ℝ) / M * H.arcs.length

def enclosureObjective (G : Network) (J X : Finset ℕ) (U : ℝ) : ℝ :=
  cut G X - U * (J ∩ X).card

def Enclosure (G : Network) (r : ℕ) (J : Finset ℕ) (U : ℝ) (B : Finset ℕ) : Prop :=
  B ⊆ G.vertices \ {r} ∧ ∀ X ⊆ G.vertices \ {r},
    enclosureObjective G J B U ≤ enclosureObjective G J X U

/-- z must be fresh. A minimum r--z shore, with z removed, is an enclosure. -/
noncomputable def enclosureNetwork (G : Network) (J : Finset ℕ) (U : ℝ) (z : ℕ) : Network :=
  ⟨insert z G.vertices, G.arcs ++ J.toList.map fun t => ⟨t, z, U⟩⟩

/-- A flow is indexed by arc positions, so parallel and antiparallel arcs stay distinct. -/
def divergence (G : Network) (flow : ℕ → ℝ) (v : ℕ) : ℝ :=
  ∑ i : Fin G.arcs.length,
    ((if G.incidence.tail i = v then flow i else 0) -
     (if G.incidence.head i = v then flow i else 0))

def FlowCutAnswer (G : Network) (s t : ℕ) (flow : ℕ → ℝ) (X : Finset ℕ) : Prop :=
  G.Valid ∧ s ∈ G.vertices ∧ t ∈ G.vertices ∧ s ≠ t ∧ PairSide G s t X ∧
  (∀ i < G.arcs.length, 0 ≤ flow i ∧ flow i ≤ G.arcs[i]!.capacity) ∧
  (∀ v ∈ G.vertices, v ≠ s → v ≠ t → divergence G flow v = 0) ∧
  divergence G flow s = cut G X

end ChenCapacityTerminals.Exact


