-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P45
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:22:56.177194+00:00
-- url     : https://prove2.me/theorems/244aa597-3362-4dd2-9bf7-e4d8f73bd08c
-- title:
--   Definitions for Routing entanglement in the quantum internet
-- statement:
--   The objects the formalized statements of *Routing entanglement in the quantum internet* (arXiv:1708.07142) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `iidMass`: PDF p.4: joint mass of independent homogeneous success flags. Each index is one attempt. For `0 ≤ p ≤ 1` this is a probability mass function.
--   - `bernoulliFlagEvent`: PDF p.4: event probability computed from independent physical attempts.
--   - `retainedLinkProbability`: PDF p.4: at most one ebit is retained, iff some parallel attempt succeeds.
--   - `chainProbability`: PDF p.4: unconditional success of a fixed chain, requiring all `k` external links and all `k-1` prescribed BSMs. Pairings precede outcomes.
--   - `latticeDistance`: PDF pp.4–5: Manhattan adjacency for physical grid edges. This is not the local protocol's Euclidean distance used in choosing neighbors.
--   - `GridNetwork`: PDF pp.4–5: distinct sites of a finite square-grid network. Physical edges are all nearest-neighbor pairs; successful subgraphs can delete edges.
--   - `Edge`: PDF p.4: an edge label, canonically ordered to avoid double counting.
--   - `edgeKey`: PDF p.4: one undirected physical-edge label, in either orientation.
--   - `physicalEdges`: PDF pp.4–5: the network's physical edges, each with at most one usable pair.
--   - `endpointDegree`: PDF p.4: the physical degree of a terminal.
--   - `PortTrailEncoding`: PDF pp.4–5: finite candidate trail encoding. `r.1.val` counts its BSMs, and `r.1.val+1` counts its external edges. An edge-simple trail has at most `N*N` edges, so the bound loses none. Validity is imposed separately.
--   - `routeLength`: PDF p.4: the number of external edges in a candidate trail.
--   - `routeEdge`: PDF p.4: the undirected physical edge traversed at a trail step.
--   - `routeEdges`: PDF pp.4–5: physical memories consumed by the trail, as edge labels.
--   - `ValidRoute`: PDF pp.4–5: trail in a successful external graph. Distinct edges impose one use per memory, while permitting repeated repeater vertices on different ports. Neither terminal may be an internal repeater of its own flow.
--   - `candidateRoutes`: PDF p.5: admissible trails computed from the successful external graph.
--   - `FeasibleFamily`: PDF p.5: a simultaneous one-slot BSM schedule for the designated flow. Shared repeater vertices are allowed; shared physical memories are not. The schedule is selected from external flags before BSM outcomes.
--   - `InternalFlags`: PDF p.4: BSM flags indexed by each selected trail's internal positions. Unselected coordinates are ignored. In a feasible family selected coordinates are distinct physical BSMs because they consume distinct incident memories.
--   - `deliveredCount`: PDF p.4: the actual integer number of delivered ebits in one slot. Feasibility requires the selected external links to have succeeded already.
--   - `conditionalYield`: PDF p.5: conditional expected yield, after external flags and before BSM flags. Each selected trail contributes `q^(length-1)`; the sum uses linearity of expectation, rather than multiplying path-success probabilities.
--   - `feasibleFamilies`: PDF p.5: finite set of all feasible schedules, including the empty one.
--   - `shortestRoute`: PDF p.5: select a shortest surviving route, with a minimizing tie choice fixed independently of future BSM outcomes. A shortest trail is a simple path.
--   - `greedySteps`: PDF p.5: shortest-path greedy, deleting physical edges after every choice. An initial physical-edge count of fuel suffices because every route consumes at least one remaining edge. No schedule depends on future BSM flags.
--   - `greedyFamily`: PDF p.5: the complete prescribed greedy schedule in a successful graph.
--   - `conditionalOptimum`: PDF p.5: the actual finite optimum over one-slot BSM schedules, computed from the successful graph. This is not a free function constrained by the desired bound. Randomizing schedules cannot improve a finite maximum.
--   - `externalMass`: PDF pp.4–5: probability of exactly a given external outcome `H`. Callers sum over subsets, so subtraction counts failures without truncation. Zero exponents express empty products, including at `p=0,1`.
--   - `greedyRate`: PDF p.5: greedy expected ebits per slot, averaging the actual protocol path-sum yield over independent external-success subsets.
--   - `optimalGlobalRate`: PDF p.5: globally optimal one-slot pairwise-swap expected yield. Only external flags are observed before selecting the optimal schedule.
-- source:
--   Routing entanglement in the quantum internet, arXiv:1708.07142v2, https://arxiv.org/abs/1708.07142v2

import Mathlib

/-!
# Routing entanglement in the quantum internet: finite one-slot results

Pant et al., arXiv:1708.07142v2, PDF pp.4–5. Only heralded loss is
represented: successful external links are perfect EPR pairs, and successful
BSMs join pairs. External attempts precede simultaneous internal attempts.
Memories last one slot and are used in at most one BSM; terminals retain their
halves. No purification, inter-slot storage, or general quantum processing is
included. Rates are expected delivered ebits per slot, not channel capacities.

A port-disjoint BSM schedule decomposes into terminal trails, other trails,
and cycles. Only trails joining the designated pair contribute. Conversely,
an edge-disjoint family below prescribes those BSMs, leaving other memories
idle. Trails may revisit a repeater on different ports, but may not reuse a
physical edge or pass internally through either terminal. Thus optimization
allows two BSMs per degree-four repeater and is not vertex-disjoint routing.
The finite maximum is computed before any future BSM flags are revealed.

Local-rule lattice claims and empirical claims are deferred in HARD.md.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P45

open scoped BigOperators

noncomputable section

/-- PDF p.4: joint mass of independent homogeneous success flags. Each index
is one attempt. For `0 ≤ p ≤ 1` this is a probability mass function. -/
def iidMass {I : Type*} [Fintype I] (p : ℝ) (flags : I → Bool) : ℝ :=
  ∏ i, if flags i then p else 1 - p

/-- PDF p.4: event probability computed from independent physical attempts. -/
def bernoulliFlagEvent {I : Type*} [Fintype I] (p : ℝ) (event : (I → Bool) → Prop) : ℝ := by
  classical
  exact ∑ flags : I → Bool, if event flags then iidMass p flags else 0

/-- PDF p.4: at most one ebit is retained, iff some parallel attempt succeeds. -/
def retainedLinkProbability (S : ℕ) (p0 : ℝ) : ℝ :=
  bernoulliFlagEvent (I := Fin S) p0 (fun flags => ∃ i, flags i = true)

/-- PDF p.4: unconditional success of a fixed chain, requiring all `k`
external links and all `k-1` prescribed BSMs. Pairings precede outcomes. -/
def chainProbability (k : ℕ) (p q : ℝ) : ℝ := by
  classical
  exact ∑ external : Fin k → Bool, ∑ internal : Fin (k - 1) → Bool,
    if (∀ i, external i = true) ∧ (∀ j, internal j = true) then
      iidMass p external * iidMass q internal else 0

/-- PDF pp.4–5: Manhattan adjacency for physical grid edges. This is not
the local protocol's Euclidean distance used in choosing neighbors. -/
def latticeDistance (a b : ℤ × ℤ) : ℕ :=
  (a.1 - b.1).natAbs + (a.2 - b.2).natAbs

/-- PDF pp.4–5: distinct sites of a finite square-grid network. Physical
edges are all nearest-neighbor pairs; successful subgraphs can delete edges. -/
structure GridNetwork (N : ℕ) where
  position : Fin N → ℤ × ℤ
  injective_position : Function.Injective position

/-- PDF p.4: an edge label, canonically ordered to avoid double counting. -/
abbrev Edge (N : ℕ) := Fin N × Fin N

/-- PDF p.4: one undirected physical-edge label, in either orientation. -/
def edgeKey {N : ℕ} (a b : Fin N) : Edge N :=
  (min a b, max a b)

/-- PDF pp.4–5: the network's physical edges, each with at most one usable pair. -/
def physicalEdges {N : ℕ} (G : GridNetwork N) : Finset (Edge N) := by
  classical
  exact Finset.univ.filter (fun e => e.1 < e.2 ∧
    latticeDistance (G.position e.1) (G.position e.2) = 1)

/-- PDF p.4: the physical degree of a terminal. -/
def endpointDegree {N : ℕ} (G : GridNetwork N) (a : Fin N) : ℕ := by
  classical
  exact ((physicalEdges G).filter (fun e => e.1 = a ∨ e.2 = a)).card

/-- PDF pp.4–5: finite candidate trail encoding. `r.1.val` counts its BSMs,
and `r.1.val+1` counts its external edges. An edge-simple trail has at most
`N*N` edges, so the bound loses none. Validity is imposed separately. -/
abbrev PortTrailEncoding (N : ℕ) := Σ k : Fin (N * N), Fin (k.val + 2) → Fin N

/-- PDF p.4: the number of external edges in a candidate trail. -/
def routeLength {N : ℕ} (r : PortTrailEncoding N) : ℕ := r.1.val + 1

/-- PDF p.4: the undirected physical edge traversed at a trail step. -/
def routeEdge {N : ℕ} (r : PortTrailEncoding N) (i : Fin (r.1.val + 1)) : Edge N :=
  edgeKey (r.2 ⟨i.val, by omega⟩) (r.2 ⟨i.val + 1, by omega⟩)

/-- PDF pp.4–5: physical memories consumed by the trail, as edge labels. -/
def routeEdges {N : ℕ} (r : PortTrailEncoding N) : Finset (Edge N) := by
  classical
  exact Finset.univ.image (routeEdge r)

/-- PDF pp.4–5: trail in a successful external graph. Distinct edges impose
one use per memory, while permitting repeated repeater vertices on different
ports. Neither terminal may be an internal repeater of its own flow. -/
def ValidRoute {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) (r : PortTrailEncoding N) : Prop :=
  r.2 0 = a ∧ r.2 (Fin.last (r.1.val + 1)) = b ∧
  Function.Injective (routeEdge r) ∧ routeEdges r ⊆ H ∧
  ∀ i : Fin r.1.val,
    r.2 ⟨i.val + 1, by omega⟩ ≠ a ∧ r.2 ⟨i.val + 1, by omega⟩ ≠ b

/-- PDF p.5: admissible trails computed from the successful external graph. -/
def candidateRoutes {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) :
    Finset (PortTrailEncoding N) := by
  classical
  exact Finset.univ.filter (ValidRoute H a b)

/-- PDF p.5: a simultaneous one-slot BSM schedule for the designated flow.
Shared repeater vertices are allowed; shared physical memories are not.
The schedule is selected from external flags before BSM outcomes. -/
def FeasibleFamily {N : ℕ} (H : Finset (Edge N)) (a b : Fin N)
    (F : Finset (PortTrailEncoding N)) : Prop :=
  F ⊆ candidateRoutes H a b ∧
  ∀ r ∈ F, ∀ s ∈ F, r ≠ s → Disjoint (routeEdges r) (routeEdges s)

/-- PDF p.4: BSM flags indexed by each selected trail's internal positions.
Unselected coordinates are ignored. In a feasible family selected coordinates
are distinct physical BSMs because they consume distinct incident memories. -/
abbrev InternalFlags (N : ℕ) := (Σ r : PortTrailEncoding N, Fin r.1.val) → Bool

/-- PDF p.4: the actual integer number of delivered ebits in one slot.
Feasibility requires the selected external links to have succeeded already. -/
def deliveredCount {N : ℕ} (F : Finset (PortTrailEncoding N)) (flags : InternalFlags N) : ℕ := by
  classical
  exact (F.filter (fun r => ∀ i : Fin r.1.val, flags ⟨r, i⟩ = true)).card

/-- PDF p.5: conditional expected yield, after external flags and before BSM
flags. Each selected trail contributes `q^(length-1)`; the sum uses linearity
of expectation, rather than multiplying path-success probabilities. -/
def conditionalYield {N : ℕ} (q : ℝ) (F : Finset (PortTrailEncoding N)) : ℝ :=
  ∑ r ∈ F, q ^ r.1.val

/-- PDF p.5: finite set of all feasible schedules, including the empty one. -/
def feasibleFamilies {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) :
    Finset (Finset (PortTrailEncoding N)) := by
  classical
  exact Finset.univ.filter (FeasibleFamily H a b)

/-- PDF p.5: select a shortest surviving route, with a minimizing tie choice
fixed independently of future BSM outcomes. A shortest trail is a simple path. -/
def shortestRoute {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) : Option (PortTrailEncoding N) := by
  classical
  let S := candidateRoutes H a b
  exact if h : S.Nonempty then
    some (Classical.choose (S.exists_min_image routeLength h)) else none

/-- PDF p.5: shortest-path greedy, deleting physical edges after every choice.
An initial physical-edge count of fuel suffices because every route consumes
at least one remaining edge. No schedule depends on future BSM flags. -/
def greedySteps {N : ℕ} (a b : Fin N) : ℕ → Finset (Edge N) → Finset (PortTrailEncoding N)
  | 0, _ => ∅
  | fuel + 1, H => by
      classical
      exact match shortestRoute H a b with
        | none => ∅
        | some r => insert r (greedySteps a b fuel (H \ routeEdges r))

/-- PDF p.5: the complete prescribed greedy schedule in a successful graph. -/
def greedyFamily {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) : Finset (PortTrailEncoding N) :=
  greedySteps a b H.card H

/-- PDF p.5: the actual finite optimum over one-slot BSM schedules, computed
from the successful graph. This is not a free function constrained by the
desired bound. Randomizing schedules cannot improve a finite maximum. -/
def conditionalOptimum {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) (q : ℝ) : ℝ := by
  classical
  exact (feasibleFamilies H a b).fold max 0 (conditionalYield q)

/-- PDF pp.4–5: probability of exactly a given external outcome `H`.
Callers sum over subsets, so subtraction counts failures without truncation.
Zero exponents express empty products, including at `p=0,1`. -/
def externalMass {N : ℕ} (G : GridNetwork N) (p : ℝ) (H : Finset (Edge N)) : ℝ :=
  p ^ H.card * (1 - p) ^ ((physicalEdges G).card - H.card)

/-- PDF p.5: greedy expected ebits per slot, averaging the actual protocol
path-sum yield over independent external-success subsets. -/
def greedyRate {N : ℕ} (G : GridNetwork N) (a b : Fin N) (p q : ℝ) : ℝ :=
  ∑ H ∈ (physicalEdges G).powerset,
    externalMass G p H * conditionalYield q (greedyFamily H a b)

/-- PDF p.5: globally optimal one-slot pairwise-swap expected yield. Only
external flags are observed before selecting the optimal schedule. -/
def optimalGlobalRate {N : ℕ} (G : GridNetwork N) (a b : Fin N) (p q : ℝ) : ℝ :=
  ∑ H ∈ (physicalEdges G).powerset,
    externalMass G p H * conditionalOptimum H a b q

example (p : ℝ) (flags : Fin 0 → Bool) : iidMass p flags = 1 := by
  simp [iidMass]

example {N : ℕ} (a b : Fin N) : edgeKey a b = edgeKey b a := by
  simp [edgeKey, min_comm, max_comm]

example {N : ℕ} (flags : InternalFlags N) :
    deliveredCount (∅ : Finset (PortTrailEncoding N)) flags = 0 := by
  simp [deliveredCount]

example {N : ℕ} (q : ℝ) : conditionalYield q (∅ : Finset (PortTrailEncoding N)) = 0 := by
  simp [conditionalYield]

example {N : ℕ} (a b : Fin N) :
    greedySteps a b 0 (∅ : Finset (Edge N)) = ∅ := by
  rfl

example {I : Type*} [Fintype I] (p : ℝ) :
    bernoulliFlagEvent (I := I) p (fun _ => False) = 0 := by
  simp [bernoulliFlagEvent]

example {N : ℕ} (r : PortTrailEncoding N) : 0 < routeLength r := by
  exact Nat.succ_pos _

example {N : ℕ} (H : Finset (Edge N)) (a b : Fin N) :
    FeasibleFamily H a b ∅ := by
  simp [FeasibleFamily]

example {N : ℕ} (F : Finset (PortTrailEncoding N)) :
    deliveredCount F (fun _ => true) = F.card := by
  simp [deliveredCount]

example {N : ℕ} (G : GridNetwork N) (p : ℝ) :
    externalMass G p ∅ = (1 - p) ^ (physicalEdges G).card := by
  simp [externalMass]

example {N : ℕ} (a b : Fin N) (H : Finset (Edge N))
    (fuel : ℕ) (h : shortestRoute H a b = none) :
    greedySteps a b (fuel + 1) H = ∅ := by
  simp [greedySteps, h]

end

end QAlgorithms.Papers.Independent.Intakethird100.P45


