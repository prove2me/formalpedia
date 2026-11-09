-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Instance
-- name    : HardCoreLocalSampling_Local_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:57.876936+00:00
-- url     : https://prove2.me/theorems/76a3b84b-28a6-43ea-9ae1-f523de7ede0c
-- title:
--   Local sampler inputs and the exact-output predicate
-- statement:
--   An input of the local sampler is a finite simple undirected graph whose vertices are their labels, natural numbers ordered as usual, with adjacency lists in arbitrary order and a tri-state pinning. Labels occupy $O(\log(n+2))$ bits, $n=|V|$, with implied constant $\kappa$. The oracle answers only adjacency-list random access and pin queries. A valid input has maximum degree at most $\Delta$ and a feasible pinning; feasibility is a promise.
--
--   The vertices removed by a pinning are the pinned unoccupied vertices, the occupied vertices, and the neighbors of occupied vertices. A query starts with its label in a register and all else zero.
--
--   A program is exact at $(G,\xi,v)$ if the event that it outputs $1$ has probability exactly the conditional unoccupied marginal, the event that it outputs $0$ the complement, and it halts almost surely.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §2, printed p.2 (PDF p.3); §5, printed p.5 (PDF p.6); Lemma 14, printed p.11 (PDF p.12)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Deletion
import Definitions.Def_HardCoreLocalSampling_Local_Machine

namespace HardCoreLocalSampling.Local

/-! The input of the local sampler, §2 (printed p.2 / PDF p.3): a finite simple graph whose
vertices are their labels, adjacency lists, a pinning; and the guarantees of Theorem 1. -/

/-- A finite simple undirected graph presented by adjacency lists in arbitrary order, with a
tri-state pinning. A vertex is its label, a natural number; the label order is the order of `ℕ`. -/
structure LocalInstance where
  /-- The set of vertex labels. Nothing is assumed about which numbers occur here, except
  through `LabelsBounded`. -/
  vertices : Finset ℕ
  /-- The graph. -/
  graph : SimpleGraph vertices
  /-- The adjacency list of each vertex, as seen by the oracle. -/
  adj : vertices → List vertices
  adj_nodup : ∀ v, (adj v).Nodup
  mem_adj : ∀ v u, u ∈ adj v ↔ graph.Adj v u
  /-- The pinning. -/
  pin : Pinning vertices

namespace LocalInstance

/-- `n = |V|`. -/
def n (I : LocalInstance) : ℕ := I.vertices.card

/-- Labels occupy `O(log(n+2))` bits, with the implied constant `κ`. -/
def LabelsBounded (I : LocalInstance) (κ : ℕ) : Prop :=
  ∀ x ∈ I.vertices, Nat.size x ≤ κ * Nat.clog 2 (I.n + 2)

/-- The code of a pin returned by the pinning oracle. -/
def pinCode : Pin → ℕ
  | .unoccupied => 0
  | .occupied => 1
  | .unpinned => 2

open Classical in
/-- The adjacency-list and pinning oracles of the instance. A number that is not a label has
no neighbors and reads as unpinned. -/
noncomputable def oracle (I : LocalInstance) : Oracle where
  neighbor x i :=
    if h : x ∈ I.vertices then ((I.adj ⟨x, h⟩)[i]?).map Subtype.val else none
  pin x := if h : x ∈ I.vertices then pinCode (I.pin ⟨x, h⟩) else 2

open Classical in
/-- The vertices removed by a pinning (§5, Lemma 14): pinned unoccupied vertices, occupied
vertices and their neighbors. The graph left over is the residual unpinned induced graph. -/
noncomputable def pinDeleted (I : LocalInstance) : Finset I.vertices :=
  Finset.univ.filter fun v =>
    I.pin v = .unoccupied ∨ I.pin v = .occupied ∨
      ∃ u, I.pin u = .occupied ∧ I.graph.Adj v u

end LocalInstance

/-- The input of one query: the label is in `L[0]`, everything else is zero. -/
def queryConfig {I : LocalInstance} (v : I.vertices) : Config :=
  { L := regsOf [v.val] }

/-- The run of `P` on query `v` with fair-bit stream `ω`: its output bit, up to almost-sure
termination, is exactly the conditional unoccupied bit at fugacity `lam`. -/
def ExactUnoccupiedBit (P : Program) (I : LocalInstance) (lam : ℚ) (v : I.vertices) : Prop :=
  MeasurableSet {ω | outcome P I.oracle ω noExt (queryConfig v) = some true} ∧
    fairMeasure {ω | outcome P I.oracle ω noExt (queryConfig v) = some true} =
      ENNReal.ofReal (conditionalUnoccupied I.graph (lam : ℝ) I.pin v) ∧
    fairMeasure {ω | outcome P I.oracle ω noExt (queryConfig v) = some false} =
      ENNReal.ofReal (1 - conditionalUnoccupied I.graph (lam : ℝ) I.pin v) ∧
    (∀ᵐ ω ∂fairMeasure, outcome P I.oracle ω noExt (queryConfig v) ≠ none)

/-- A valid input of Theorem 1: maximum degree at most `Delta` and a feasible pinning.
Feasibility is a promise, not something a program checks. -/
def ValidInput (I : LocalInstance) (Delta : ℕ) : Prop :=
  MaxDegreeLE I.graph Delta ∧ Feasible I.graph I.pin

/-- The polylogarithmic bound `C (1 + log(n+2))^a`, as an extended nonnegative real. -/
noncomputable def polylogBound (C : NNReal) (a n : ℕ) : ENNReal :=
  (C : ENNReal) * ENNReal.ofReal ((1 + Real.log ((n : ℝ) + 2)) ^ a)

end HardCoreLocalSampling.Local


