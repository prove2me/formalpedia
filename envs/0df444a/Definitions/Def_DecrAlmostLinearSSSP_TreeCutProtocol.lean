-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol
-- name    : DecrAlmostLinearSSSP_TreeCutProtocol
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:18:09.170288+00:00
-- url     : https://prove2.me/theorems/dca0727f-b010-4a01-aee5-14220c9d25df
-- title:
--   Charged lazy tree-cut and exact detector protocol
-- statement:
--   This module exposes the operational boundary between a dynamic tree-cut sparsifier and its public detector-report wrapper. The numerical range is normalized so that active capacities lie in $[1,M^{2d}]$, where $M=\max\{2,m\}$, while demands remain zero-sum and bounded by $M^d$.
--
--   A tree implementation supports the six physical, ratio, toggle and potential-query operations. A toggle updates the implicit potential lazily and emits no public report. Two additional private entry points support output-sensitive detection: `peek` either certifies that every active weighted endpoint displacement is strictly below $\xi$, or returns an actual active identifier whose displacement is at least $\xi$; `reset e` recalibrates exactly the baseline of an active identifier $e$. All other semantic fields remain unchanged by these private calls.
--
--   Every public and private step is an actual finite charged RAM execution. Amortized work is bounded by initialization plus $h$ times the total number of public and private operations. Mathematical interpretation supplies no free cut materialization, potential evaluation or detector scan.
--
--   **Formalization Note** The state view is required only for $n>0$, as in the corrected public protocol. A six-instruction request allowance is charged for private calls too. This module defines semantics only; existence of the structure and construction of the report-draining wrapper are separate obligations.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p.9, Lemma 3.2 and §3.2.1 (implicit cuts/potentials and detector reports), and p.16 (polynomial numerical range); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. Internal charged decomposition of that interface into lazy tree operations and exact peek/reset detector primitives.

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- Numerical range after the wrapper multiplies capacities by `M^exponent`.
The lower bound is one and the upper exponent doubles; demands are unchanged. -/
def TreeNormalizedValid {n k : ℕ} (g : Physical n k) (m exponent : ℕ) : Prop :=
  n ≤ m ∧ k ≤ m ∧ 0 < n ∧
  (∀ e ∈ g.active, 1 ≤ g.u e ∧ g.u e ≤ (max 2 m : ℝ) ^ (2 * exponent)) ∧
  (∑ v, g.gamma v) = 0 ∧ (∀ v, |g.gamma v| ≤ (max 2 m : ℝ) ^ exponent) ∧
  (∀ x, physicalNorm g x = 0 → ∀ v w, x v = x w)

/-- In addition to the six public calls, the tree structure exposes two internal
charged calls. `peek` returns any active edge currently above the detector threshold,
or certifies that there is none. `reset` recalibrates one active edge after the wrapper
has emitted it. Neither internal call emits a public report. -/
inductive TreeOp (n k : ℕ)
  | call (op : CutOp n k)
  | peek
  | reset (e : Fin k)

/-- A tree implementation has private entry points for the two detector primitives.
The public entry points and request layout are exactly those of the public protocol. -/
structure TreeImplementation where
  program : Program
  interpret : (n k : ℕ) → 0 < n → Machine → CutState n k
  peekPC : ℕ
  resetPC : ℕ

noncomputable def TreeImplementation.view (impl : TreeImplementation) (n k : ℕ)
    [NeZero n] (c : Machine) : CutState n k :=
  impl.interpret n k (Nat.pos_of_ne_zero (NeZero.ne n)) c

def TreeOp.Valid {n k : ℕ} (s : CutState n k) : TreeOp n k → Prop
  | .call op => CutOp.Valid s op
  | .peek => True
  | .reset e => e ∈ s.physical.active

noncomputable def applyTreePhysical {n k : ℕ} (g : Physical n k) : TreeOp n k → Physical n k
  | .call op => applyPhysical g op
  | .peek | .reset _ => g

/-- Internal calls have the same six-instruction request allowance as public calls. -/
def treeRequest {n k : ℕ} (impl : TreeImplementation) (c : Machine) : TreeOp n k → Machine
  | .call op => cutRequest impl.program c op
  | .peek => resume c impl.peekPC
  | .reset e =>
      { resume c impl.resetPC with natReg := Function.update c.natReg 6 e.val }

/-- A public toggle changes only the potential and cached tuple. Reports and their
baseline resets are performed by the wrapper through `peek` and `reset` below. -/
noncomputable def LazyToggleTransition {n k : ℕ} (s : CutState n k) (tau : ℝ)
    (c : Machine) (t : CutState n k) : Prop := by
  classical
  exact t.physical = s.physical ∧
    (∀ v, t.y v = s.y v + if v ∈ s.lastCut then tau else 0) ∧
    t.baseline = s.baseline ∧ t.hasCut = s.hasCut ∧ t.lastCut = s.lastCut ∧
    t.lastG = s.lastG ∧ t.lastU = s.lastU ∧ reportCount c = 0

/-- `peek` has an exact, output-sensitive threshold test. A positive answer supplies
an actual above-threshold active identifier and its detector value. A zero answer
certifies that no active edge is above threshold. -/
noncomputable def PeekTransition {n k : ℕ} (ξ : ℝ) (s : CutState n k)
    (c : Machine) (t : CutState n k) : Prop := by
  classical
  exact t = s ∧ reportCount c = 0 ∧
    ((c.natReg 12 = 0 ∧
        ∀ e ∈ s.physical.active,
          |s.physical.u e * (s.y (s.physical.graph.tail e) -
            s.y (s.physical.graph.head e) - s.baseline e)| < ξ) ∨
      (c.natReg 12 = 1 ∧ ∃ e ∈ s.physical.active,
        c.natReg 6 = e.val ∧
        c.realReg 10 = |s.physical.u e * (s.y (s.physical.graph.tail e) -
          s.y (s.physical.graph.head e) - s.baseline e)| ∧ ξ ≤ c.realReg 10))

/-- Recalibration after one emitted report. It changes no physical, potential or
cached-cut field; all other baselines are retained exactly. -/
noncomputable def ResetTransition {n k : ℕ} (s : CutState n k) (e : Fin k)
    (c : Machine) (t : CutState n k) : Prop := by
  classical
  exact t = { s with baseline := (Function.update s.baseline e
      (s.y (s.physical.graph.tail e) - s.y (s.physical.graph.head e))) } ∧
    reportCount c = 0

noncomputable def TreeTransition {n k : ℕ} (K ξ : ℝ) (s : CutState n k)
    (op : TreeOp n k) (c : Machine) (t : CutState n k) : Prop :=
  match op with
  | .call (.toggle tau) => LazyToggleTransition s tau c t
  | .call op => CutTransition K ξ s op c t
  | .peek => PeekTransition ξ s c t
  | .reset e => ResetTransition s e c t

/-- Actual finite online runs of public and private tree operations. Public operation
legality and the normalized post-operation numerical range are checked at every step. -/
inductive TreeRun (impl : TreeImplementation) (n k m exponent : ℕ) [NeZero n]
    (first : Machine) : List (TreeOp n k) → List Machine → Prop
  | start : TreeRun impl n k m exponent first [] [first]
  | next {ops : List (TreeOp n k)} {cs : List Machine} {c d : Machine}
      (hr : TreeRun impl n k m exponent first ops cs)
      (hl : cs.getLast? = some c) (op : TreeOp n k)
      (hv : TreeOp.Valid (impl.view n k c) op)
      (hb : TreeNormalizedValid (applyTreePhysical (impl.view n k c).physical op) m exponent)
      (he : Ends impl.program (treeRequest impl c op) d) :
      TreeRun impl n k m exponent first (ops ++ [op]) (cs ++ [d])

/-- Correctness, termination and the `m^(o(1))` amortized factor for the external
structure. Every private peek/reset is itself an operation in `ops`, so a linear scan
or an explicit potential/cut update cannot be hidden in an uncharged decoder. -/
def TreeImplements (impl : TreeImplementation) (m exponent : ℕ)
    (K h init ξ : ℝ) : Prop :=
  ∀ n k [NeZero n] (graph : Physical n k) (capacityBound : ℝ),
    TreeNormalizedValid graph m exponent →
    0 < capacityBound → capacityBound ≤ (max 2 m : ℝ) ^ (2 * exponent) →
    (∀ e ∈ graph.active, graph.u e ≤ capacityBound) →
    ∃ first, Ends impl.program (cutInitial impl.program graph m ξ capacityBound) first ∧
      (impl.view n k first).physical = graph ∧ (impl.view n k first).y = 0 ∧
      (impl.view n k first).baseline = 0 ∧ (impl.view n k first).hasCut = false ∧
      (first.work : ℝ) ≤ init ∧
      ∀ ops cs, TreeRun impl n k m exponent first ops cs →
        (∀ c, cs.getLast? = some c → ∀ op, TreeOp.Valid (impl.view n k c) op →
          TreeNormalizedValid (applyTreePhysical (impl.view n k c).physical op) m exponent →
          ∃ d, Ends impl.program (treeRequest impl c op) d ∧
            TreeTransition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (∀ (j : ℕ) c d op, cs[j]? = some c → cs[j+1]? = some d → ops[j]? = some op →
          TreeTransition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (∀ last, cs.getLast? = some last →
          (last.work + 6 * ops.length : ℕ) ≤ init + h * ops.length)

end DecrAlmostLinearSSSP.Decremental.NonemptyCut


