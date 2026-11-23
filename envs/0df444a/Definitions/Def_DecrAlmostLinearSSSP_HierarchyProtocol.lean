-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_HierarchyProtocol
-- name    : DecrAlmostLinearSSSP_HierarchyProtocol
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T04:25:21.67523+00:00
-- url     : https://prove2.me/theorems/c1fedff7-cfeb-410f-87fa-cde389f7089d
-- title:
--   Charged dynamic hierarchy with lazy cuts and signed extrema
-- statement:
--   This module isolates the raw charged operations supplied by a deterministic dynamic capacitated expander hierarchy and its layered rooted trees. On the normalized numerical range, the hierarchy maintains the physical graph, the most recently selected implicit fundamental cut, and implicit real vertex labels. Non-toggle operations supply the minimum-ratio guarantee; a toggle adds $\tau\mathbf 1_C$ lazily, and a vertex query actually evaluates the stored label through the RAM representation.
--
--   For detector support, the hierarchy maintains generic signed path aggregates. For an active edge $e=a\to b$, write
--   $$
--   \delta_e=u_e\bigl(y_a-y_b-b_e\bigr),
--   $$
--   where $b_e$ is its recalibration baselineansen. Charged `maximum` and `minimum` operations return an active edge attaining $\max_e\delta_e$ or $\min_e\delta_e$, together with the exact value; on an empty active set they return the zero flag. These are threshold-free navigation primitives, not the final absolute-value threshold detector. A separate charged reset recalibrates one edge.
--
--   Every primitive has an actual finite scalar-RAM execution. The run relation counts all public and private calls, and the work predicate includes each six-instruction request allowance. The semantic view grants no free maximum, potential evaluation, cut materialization, or detector scan. The subsequent compiler combines the two extrema into exact `peek`, forwards reset, and packages the raw hierarchy as the normalized tree-cut interface.
--
--   **Formalization Note** State interpretation is required only for $n>0$. Empty active edge sets are explicitly handled, while loops and parallel identifiers use the same oriented displacement formula as the public protocol.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p.9, Lemma 3.2 (adapted from van den Brand et al., Theorem 5.4), and p.10 Repair reporting; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. Operational decomposition using the deterministic dynamic tree-cut sparsifier of van den Brand et al., arXiv:2407.10830, Theorem 4.4 and Lemma 4.5, p.13: implicit fundamental cuts/lazy labels and layered-tree path aggregates. Signed extrema are the generic threshold-free primitives needed for the exact detector in the source interface.

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- Raw operations exported by a dynamic capacitated expander hierarchy and its
layered rooted trees. The two extrema operations are generic path-aggregate
navigation primitives; they do not perform the public threshold test. -/
inductive HierarchyOp (n k : ℕ)
  | call (op : CutOp n k)
  | reset (e : Fin k)
  | maximum
  | minimum

/-- The hierarchy has separate charged entry points for recalibration and the two
signed extrema. Its public operations are still raw hierarchy primitives rather
than the exact `peek` interface of `TreeImplementation`. -/
structure HierarchyImplementation where
  program : Program
  interpret : (n k : ℕ) → 0 < n → Machine → CutState n k
  resetPC : ℕ
  maximumPC : ℕ
  minimumPC : ℕ

noncomputable def HierarchyImplementation.view (impl : HierarchyImplementation)
    (n k : ℕ) [NeZero n] (c : Machine) : CutState n k :=
  impl.interpret n k (Nat.pos_of_ne_zero (NeZero.ne n)) c

def HierarchyOp.Valid {n k : ℕ} (s : CutState n k) : HierarchyOp n k → Prop
  | .call op => CutOp.Valid s op
  | .reset e => e ∈ s.physical.active
  | .maximum | .minimum => True

noncomputable def applyHierarchyPhysical {n k : ℕ} (g : Physical n k) :
    HierarchyOp n k → Physical n k
  | .call op => applyPhysical g op
  | .reset _ | .maximum | .minimum => g

/-- Raw hierarchy requests use the same request registers as the public cut
operations. Extrema use registers 12, 6 and 10 for their flag, edge and value. -/
def hierarchyRequest {n k : ℕ} (impl : HierarchyImplementation) (c : Machine) :
    HierarchyOp n k → Machine
  | .call op => cutRequest impl.program c op
  | .reset e =>
      { resume c impl.resetPC with natReg := Function.update c.natReg 6 e.val }
  | .maximum => resume c impl.maximumPC
  | .minimum => resume c impl.minimumPC

/-- The signed detector displacement maintained by layered-tree path aggregates. -/
noncomputable def detectorDisplacement {n k : ℕ} (s : CutState n k) (e : Fin k) : ℝ :=
  s.physical.u e * (s.y (s.physical.graph.tail e) -
    s.y (s.physical.graph.head e) - s.baseline e)

/-- A generic maximum query over active signed displacements. The empty-active
case returns flag zero. Otherwise the returned active identifier attains the
maximum and the value is exact. No threshold or absolute-value test is hidden
in this primitive. -/
noncomputable def MaximumTransition {n k : ℕ} (s : CutState n k)
    (c : Machine) (t : CutState n k) : Prop := by
  classical
  exact t = s ∧ reportCount c = 0 ∧
    ((c.natReg 12 = 0 ∧ s.physical.active = ∅) ∨
      (c.natReg 12 = 1 ∧ ∃ e ∈ s.physical.active,
        c.natReg 6 = e.val ∧ c.realReg 10 = detectorDisplacement s e ∧
        ∀ f ∈ s.physical.active, detectorDisplacement s f ≤ c.realReg 10))

/-- The corresponding generic minimum query. -/
noncomputable def MinimumTransition {n k : ℕ} (s : CutState n k)
    (c : Machine) (t : CutState n k) : Prop := by
  classical
  exact t = s ∧ reportCount c = 0 ∧
    ((c.natReg 12 = 0 ∧ s.physical.active = ∅) ∨
      (c.natReg 12 = 1 ∧ ∃ e ∈ s.physical.active,
        c.natReg 6 = e.val ∧ c.realReg 10 = detectorDisplacement s e ∧
        ∀ f ∈ s.physical.active, c.realReg 10 ≤ detectorDisplacement s f))

/-- Non-toggle calls retain their exact ratio, insertion-baseline and potential
query semantics. Toggles are lazy and emit no reports. The raw extrema and reset
operations are charged navigation/recalibration primitives for the wrapper. -/
noncomputable def HierarchyTransition {n k : ℕ} (K ξ : ℝ) (s : CutState n k)
    (op : HierarchyOp n k) (c : Machine) (t : CutState n k) : Prop :=
  match op with
  | .call (.toggle tau) => LazyToggleTransition s tau c t
  | .call op => CutTransition K ξ s op c t
  | .reset e => ResetTransition s e c t
  | .maximum => MaximumTransition s c t
  | .minimum => MinimumTransition s c t

/-- Actual finite online executions of raw hierarchy calls. Every private call is
counted, including both extrema later used to implement one public `peek`. -/
inductive HierarchyRun (impl : HierarchyImplementation) (n k m exponent : ℕ)
    [NeZero n] (first : Machine) : List (HierarchyOp n k) → List Machine → Prop
  | start : HierarchyRun impl n k m exponent first [] [first]
  | next {ops : List (HierarchyOp n k)} {cs : List Machine} {c d : Machine}
      (hr : HierarchyRun impl n k m exponent first ops cs)
      (hl : cs.getLast? = some c) (op : HierarchyOp n k)
      (hv : HierarchyOp.Valid (impl.view n k c) op)
      (hb : TreeNormalizedValid
        (applyHierarchyPhysical (impl.view n k c).physical op) m exponent)
      (he : Ends impl.program (hierarchyRequest impl c op) d) :
      HierarchyRun impl n k m exponent first (ops ++ [op]) (cs ++ [d])

/-- The deterministic dynamic-hierarchy contract. The extrema are exact generic
path-aggregate answers, not semantic functions available to the adapter for free:
all calls and their six-instruction request allowances are included in work. -/
def HierarchyImplements (impl : HierarchyImplementation) (m exponent : ℕ)
    (K h init ξ : ℝ) : Prop :=
  ∀ n k [NeZero n] (graph : Physical n k) (capacityBound : ℝ),
    TreeNormalizedValid graph m exponent →
    0 < capacityBound → capacityBound ≤ (max 2 m : ℝ) ^ (2 * exponent) →
    (∀ e ∈ graph.active, graph.u e ≤ capacityBound) →
    ∃ first, Ends impl.program (cutInitial impl.program graph m ξ capacityBound) first ∧
      (impl.view n k first).physical = graph ∧ (impl.view n k first).y = 0 ∧
      (impl.view n k first).baseline = 0 ∧ (impl.view n k first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧
      ∀ ops cs, HierarchyRun impl n k m exponent first ops cs →
        (∀ c, cs.getLast? = some c → ∀ op, HierarchyOp.Valid (impl.view n k c) op →
          TreeNormalizedValid
            (applyHierarchyPhysical (impl.view n k c).physical op) m exponent →
          ∃ d, Ends impl.program (hierarchyRequest impl c op) d ∧
            HierarchyTransition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (∀ (j : ℕ) c d op, cs[j]? = some c → cs[j+1]? = some d → ops[j]? = some op →
          HierarchyTransition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (∀ last, cs.getLast? = some last →
          (last.work + 6 * ops.length : ℕ) ≤ init + h * ops.length)

end DecrAlmostLinearSSSP.Decremental.NonemptyCut


