-- Prove2me | Definitions.Def_DistributedMWC440_UpperBound_Clustering
-- name    : DistributedMWC440_UpperBound_Clustering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:24:23.924221+00:00
-- url     : https://prove2.me/theorems/c96c6385-807c-4de3-81ea-e730411136f4
-- title:
--   Exponential shifts, capture, approximate clusters, and parity candidates
-- statement:
--   The real shift law is the finite product of exponential distributions of rate log(|S|)/(kd), with truncation at (k+1+k/log(|S|))d. Capture and safety use the source strict inequalities. The augmented graph has the source edge weight 2 deltaMax minus the truncated shift. An LDD output consists of finite labels and a rooted tree whose paths certify the lower bound and whose labels satisfy approximate upper bounds. Basic candidates are actual fundamental cycles with the computed local-label estimate. Fresh independent bits on unordered non-forest edges define the doubled graph. A patch candidate is a genuine simple cycle in the union of the projected parent path and local tree path; infinite patch labels give no candidate. These definitions do not assume a successful detection event.
-- source:
--   Yi-Jun Chang, Yanyu Chen, Dipan Dey, Yonggang Jiang, Gopinath Mishra, Hung Thuan Nguyen, Mingyang Yang, The Complexity of Distributed Minimum Weight Cycle Approximation, STOC 2027 submission #440 (October 2026), citation basis published; papers/stoc2027-440/source.pdf, §§1, 3–7, printed pp. 1–43 / PDF pp. 3–45.

import Definitions.Def_DistributedMWC440_UpperBound_Graph

open scoped ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

namespace DistributedMWC440.UpperBound

variable {V : Type} [Fintype V] [DecidableEq V]

def rate (S : Finset V) (k d : ℝ) := Real.log S.card / (k*d)
def deltaMax (S : Finset V) (k d : ℝ) := (k+1+k / Real.log S.card)*d
abbrev Shifts (S : Finset V) := S → ℝ

def shiftLaw (S : Finset V) (β : ℝ) : Measure (Shifts S) :=
  Measure.pi (fun _ => expMeasure β)

def trunc (S : Finset V) (k d : ℝ) (δ : Shifts S) (s : S) :=
  min (δ s) (deltaMax S k d)

def ValidShifts (S : Finset V) (k d : ℝ) (δ : Shifts S) : Prop :=
  ∀ s, 0 ≤ trunc S k d δ s

def Captures (W : WGraph V) (S R : Finset V) (k d : ℝ) (δ : Shifts S) (s : S) : Prop :=
  ∀ s' : S, s' ≠ s →
    setDist W s.val R - trunc S k d δ s < setDist W s'.val R - trunc S k d δ s' - d

def Safe (W : WGraph V) (S : Finset V) (k d ε : ℝ) (δ : Shifts S) (s : S) (v : V) : Prop :=
  ∀ s' : S, s' ≠ s →
    dist W s.val v - trunc S k d δ s <
      dist W s'.val v - trunc S k d δ s' - 2*ε*deltaMax S k d

/-- The super-source is none. Every real edge has its original length, and
none--some s has length 2 deltaMax minus the truncated shift. -/
def augmentedGraph (W : WGraph V) (S : Finset V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun a b => match a,b with
    | some u, some v => W.graph.Adj u v
    | none, some v => v ∈ S
    | some u, none => u ∈ S
    | none, none => False

def augmentedLength (W : WGraph V) (S : Finset V) (k d : ℝ)
    (δ : Shifts S) : Option V → Option V → ℝ
  | some u, some v => W.length u v
  | none, some v => if h : v ∈ S then 2*deltaMax S k d - trunc S k d δ ⟨v,h⟩ else 0
  | some v, none => if h : v ∈ S then 2*deltaMax S k d - trunc S k d δ ⟨v,h⟩ else 0
  | none, none => 0

/-- The data returned by any tree-like approximate SSSP routine, with real finite labels.
This is a distance/tree interface, not an algorithm or a correctness assumption for MWC. -/
structure LDDTree (W : WGraph V) (S : Finset V) (k d ε : ℝ) (δ : Shifts S) where
  label : Option V → ℝ
  parent : Option V → Option V
  depth : Option V → ℕ
  root_label : label none = 0
  root_parent : parent none = none
  root_depth : depth none = 0
  nonnegative : ∀ v, 0 ≤ label v
  edge : ∀ v : V, (augmentedGraph W S).Adj (parent (some v)) (some v)
  depth_step : ∀ v : V, depth (parent (some v)) + 1 = depth (some v)
  descent : ∀ v : V,
    label (parent (some v)) + augmentedLength W S k d δ (parent (some v)) (some v) ≤ label (some v)
  /-- Quantifying over actual augmented walks avoids default real distances on unreachable pairs. -/
  approximate : ∀ v : V, ∀ P : (augmentedGraph W S).Walk none (some v),
    label (some v) ≤ (1+ε) * OAI.PlanarL1.walkLength (augmentedLength W S k d δ) P

abbrev LDDTree.center {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (v : V) : Option V :=
  T.parent^[T.depth (some v) - 1] (some v)

def LDDTree.localLabel {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (v : V) : ℝ :=
  T.label (some v) - T.label (T.center v)

def LDDTree.treeEdge {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (u v : V) : Prop :=
  T.parent (some u) = some v ∨ T.parent (some v) = some u

/-- Basic detection enumerates each intra-cluster non-tree edge and its fundamental cycle. -/
def BasicCandidate {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (C : Cycle W) (estimate : ℝ) : Prop :=
  ∃ u v, W.graph.Adj u v ∧ T.center u = T.center v ∧ ¬T.treeEdge u v ∧
    s(u,v) ∈ C.walk.edges ∧
    (∀ a b, s(a,b) ∈ C.walk.edges → T.treeEdge a b ∨ s(a,b) = s(u,v)) ∧
    estimate = T.localLabel u + T.localLabel v + W.length u v

def BasicSuccess {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (bound : ℝ) : Prop :=
  ∃ (C : Cycle W) (estimate : ℝ), BasicCandidate T C estimate ∧ estimate ≤ bound

/-- A parity bit is indexed by an unordered edge, so the two endpoints share its value. -/
abbrev Parities (V : Type) := Sym2 V → Bool

def parityLaw : Measure (Parities V) :=
  Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)

def edgeParity {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (χ : Parities V) (u v : V) : Bool :=
  by classical exact if T.treeEdge u v then false else χ s(u,v)

def doubledGraph {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (χ : Parities V) : SimpleGraph (V × Bool) :=
  SimpleGraph.fromRel fun a b =>
    W.graph.Adj a.1 b.1 ∧ b.2 = Bool.xor a.2 (edgeParity T χ a.1 b.1)

/-- The doubled graph may be disconnected. The finite-label parent tree convention is essential. -/
def doubled {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (χ : Parities V) : WGraph (V × Bool) where
  graph := doubledGraph T χ
  length a b := W.length a.1 b.1
  symmetric a b := W.symmetric a.1 b.1
  nonnegative a b h := W.nonnegative _ _ (by
    rcases h with ⟨_, h | h⟩
    · exact h.1
    · exact h.1.symm)

/-- All patch computations are actual hop-bounded distance/tree outputs, not a fast SSSP oracle. -/
structure PatchOutputs {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    (T : LDDTree W S k d ε δ) (χ : Parities V) (L : ℕ) where
  tree : (r : S) → HopTree (doubled T χ) (r.val,false)
  approximate : ∀ r, HopApprox (doubled T χ) (r.val,false) L ε (tree r).label

/-- Project the selected patch parent path, and combine it with the local tree path.
A candidate is a genuine simple cycle in this union, not an odd closed walk. -/
def PatchCandidate {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    {T : LDDTree W S k d ε δ} {χ : Parities V} {L : ℕ}
    (P : PatchOutputs T χ L) (C : Cycle W) (estimate : ℝ) : Prop :=
  ∃ r r' : S, r ≠ r' ∧ T.center r.val = T.center r'.val ∧
    (P.tree r).label (r'.val,true) ≠ ⊤ ∧
    (∃ Q : W.graph.Walk r.val r'.val,
      Q.IsPath ∧ (∀ u v, s(u,v) ∈ Q.edges → T.treeEdge u v) ∧
      ∃ U : (doubled T χ).graph.Walk (r.val,false) (r'.val,true),
        U.IsPath ∧ (∀ a ∈ U.support, (P.tree r).label a ≠ ⊤) ∧
        (∀ a b, s(a,b) ∈ U.edges →
          (P.tree r).parent a = b ∨ (P.tree r).parent b = a) ∧
        (∀ u v, s(u,v) ∈ C.walk.edges → s(u,v) ∈ Q.edges ∨
          ∃ a b, s(a,b) ∈ U.edges ∧ s(u,v) = s(a.1,b.1))) ∧
    estimate = T.localLabel r.val + T.localLabel r'.val +
      ((P.tree r).label (r'.val,true)).toReal

def ExtendedSuccess {W : WGraph V} {S : Finset V} {k d ε : ℝ} {δ : Shifts S}
    {T : LDDTree W S k d ε δ} {χ : Parities V} {L : ℕ}
    (P : PatchOutputs T χ L) (bound : ℝ) : Prop :=
  ∃ (C : Cycle W) (estimate : ℝ),
    (BasicCandidate T C estimate ∨ PatchCandidate P C estimate) ∧ estimate ≤ bound

end DistributedMWC440.UpperBound


