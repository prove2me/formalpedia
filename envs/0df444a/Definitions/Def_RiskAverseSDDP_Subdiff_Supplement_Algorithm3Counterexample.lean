-- Prove2me | Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm3Counterexample
-- name    : RiskAverseSDDP_Subdiff_Supplement_Algorithm3Counterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:32:50.782676+00:00
-- url     : https://prove2.me/theorems/c563482b-76d0-448b-afde-42a6b4c4e767
-- title:
--   Algorithm 3 — a fair repeated scenario and a zero-cost three-stage instance
-- statement:
--   Consider a three-stage tree with one first-stage node, two second-stage nodes labelled by a bit, and one leaf below each second-stage node. At stage 2 a fair bit is revealed and at stage 3 the same bit is revealed again. Each decision set is $\{0\}\subset\mathbb R$, all costs are zero, and there are no equality or inequality constraints. The random parameter $\Psi$ has distinct labels but is ignored by the zero cost. All conditions (H2) hold, for example with $\varepsilon=1$. Risk measures are conditional expectations: the two children of the first-stage node have probabilities $1/2$, and each second-stage node has its single child with probability $1$.
--
--   Draw a fair bit $\omega$ once and use that same scenario in every iteration. Each iteration has exactly the correct scenario law. The true recourse functions are zero. With zero cut slopes, the sampled second-stage node receives the zero cut, the other second-stage node remains at $-\infty$, and the first-stage approximation remains at $-\infty$. The definition `IsZeroAlgorithm3Run` records the exact specialization of (6.45), (6.47) and (6.49) to these constant functions; all decisions equal their unique feasible value zero.
--
--   **Formalization Note** `zeroData` is used only for the published deterministic predicate `Model.H2`; its product-tree recursion and probability fields do not define this dependent scenario tree. The tree and its conditional probabilities are specified separately in `ZeroNode` and `IsZeroAlgorithm3Run`. As in Algorithm 2, a startup objective identically $-\infty$ is minimized by its feasible decision; no finite epigraph minimizer is asserted. This is a concrete counterexample instance, not a general replacement definition of Algorithm 3.
--
--   The same witness is also instantiated directly as `zeroTreeModel`, `zeroTreeRules` and `zeroTreeRun` in the full node-dependent model and Algorithm 3 predicate. The counterexample theorem asserts the full `IsRun3` relation, source `H2` and `Standing`, true recourse values and failure of the actual node and first-stage limits, in addition to the reduced scalar recurrences.
-- source:
--   Guigues, arXiv:1408.4439v4, pp. 18–20, (6.43)–(6.49), Algorithm 3 and Theorem 6.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_TreeModel
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm3

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A three-stage instance for the printed sampling condition of Theorem 6.1, pp. 19–20.
Every decision set is `{0} ⊂ ℝ`, every cost is zero, and there are no equality or inequality
constraints. The two values of the random parameter `Ψ` are ignored by the cost function.
At stage 2 a fair bit is revealed; at stage 3 the same bit is revealed again. Thus the tree
has a first-stage node, two stage-2 nodes and one leaf below each stage-2 node. The law is
interstage dependent. `Model.H2` only describes the deterministic constraint/cost data;
the published product-tree recursion and `Model.Standing` are not used for this example. -/
noncomputable def zeroData : Model 3 1 2 0 0 where
  x0 := 0
  Xc := fun _ => {0}
  f := fun _ _ _ => 0
  g := fun _ _ _ _ i => i.elim0
  A := fun _ _ _ => 0
  b := fun _ _ => 0
  Φ := fun _ _ => 1 / 2
  Prisk := fun _ => {fun _ => 1}

/-- The nodes other than the fictitious root. A `middle b` has the single child `leaf b`;
the first-stage node has the two children `middle false` and `middle true`, each of
conditional probability `1/2`. The risk measures are conditional expectations. -/
inductive ZeroNode where
  | first
  | middle (b : Bool)
  | leaf (b : Bool)
  deriving DecidableEq

/-- Every true recourse function is the constant zero function. Histories contain zero
decisions, since all decision sets are singletons. -/
noncomputable def zeroTrueValue (_ : ZeroNode) : EReal := 0

/-- The sampling probability space consists of a fair bit, with its discrete sigma algebra. -/
instance zeroMeasurableSpace : MeasurableSpace Bool := ⊤

noncomputable def zeroLaw : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

/-- The underlying stochastic process. Its two scenarios are `(false,false,false)` and
`(false,true,true)` at stages 1, 2, 3. Each iteration has this exact scenario law. -/
def zeroProcess (ω : Bool) (t : ℕ) : Bool := if t = 1 then false else ω

/-- Draw once, and reuse the scenario in every iteration. Each sample has the correct law,
but the scenario samples are correlated across iterations. -/
def repeatedSample (_k : ℕ) (ω : Bool) : Bool := ω

/-- `y^k_n`: a node is selected precisely when it lies on the sampled scenario. -/
def zeroSelected (k : ℕ) (ω : Bool) : ZeroNode → ℝ
  | .first => 1
  | .middle b => if b = repeatedSample k ω then 1 else 0
  | .leaf b => if b = repeatedSample k ω then 1 else 0

/-- Values of the constant approximate recourse functions in this instance. Leaves always
have value 0. The sampled middle node receives the zero cut at iteration 1; the other one
keeps `-∞`. The first-stage node keeps `-∞`, because its expectation includes the unvisited
middle node with positive weight. All cuts have slope zero. -/
noncomputable def zeroApprox (ω : Bool) (k : ℕ) : ZeroNode → EReal
  | .leaf _ => 0
  | .middle b => if k = 0 then ⊥ else if b = ω then 0 else ⊥
  | .first => ⊥

/-- The exact reduction of Algorithm 3, (6.45), (6.47), (6.49), for these data and zero
slopes. At each node (6.45) chooses its unique feasible decision 0. At a middle node its
only child's approximate value is 0: if selected it adds the zero cut, otherwise it adds
the previous constant value as in (6.47). The first-stage node is always selected and adds
the expected child values from the previous iteration. At startup the extended-real
objective convention of `LinModel.IsCutOpt` is used: every feasible decision minimizes
the constant `-∞` objective; no finite epigraph minimizer is asserted. -/
def IsZeroAlgorithm3Run (sample : ℕ → Bool) (V : ℕ → ZeroNode → EReal) : Prop :=
  V 0 .first = ⊥ ∧
  (∀ b, V 0 (.middle b) = ⊥) ∧
  (∀ k b, V k (.leaf b) = 0) ∧
  (∀ k b, V (k + 1) (.middle b) =
    max (V k (.middle b)) (if b = sample (k + 1) then 0 else V k (.middle b))) ∧
  (∀ k, V (k + 1) .first = max (V k .first)
    (((1 / 2 : ℝ) : EReal) * V k (.middle false) +
     ((1 / 2 : ℝ) : EReal) * V k (.middle true)))

/-- The actual level types of this tree: one first-stage node, two middle nodes, two
leaves, and no nodes beyond the horizon. -/
def ZeroLevel : ℕ → Type
  | 0 => Unit
  | 1 => Bool
  | 2 => Bool
  | _ + 3 => Empty

instance zeroLevelFintype : ∀ s, Fintype (ZeroLevel s)
  | 0 => inferInstanceAs (Fintype Unit)
  | 1 => inferInstanceAs (Fintype Bool)
  | 2 => inferInstanceAs (Fintype Bool)
  | _ + 3 => inferInstanceAs (Fintype Empty)

instance zeroLevelMeasurableSpace : ∀ s, MeasurableSpace (ZeroLevel s) := fun _ => ⊤

def zeroParent : (s : ℕ) → ZeroLevel (s + 1) → ZeroLevel s
  | 0 => fun _ => ()
  | 1 => fun b => b
  | 2 => Empty.elim
  | _ + 3 => Empty.elim

/-- The same witness as a genuine instance of the full node-dependent model, with
conditional probabilities 1/2 at the branching and 1 at each middle node. -/
noncomputable def zeroTreeModel : TreeModel 3 1 0 0 ZeroLevel where
  first := ()
  first_unique := by intro ν; cases ν; rfl
  parent := zeroParent
  x0 := 0
  Xc := fun _ => {0}
  f := fun _ _ _ => 0
  g := fun _ _ _ i => i.elim0
  A := fun _ _ _ => 0
  b := fun _ _ => 0
  Φ := fun s _ _ => if s = 0 then 1 / 2 else 1
  Prisk := fun _ _ => {fun _ => 1}

def zeroPath (ω : Bool) : zeroTreeModel.Path := by
  intro i
  refine Fin.cases () (fun j => ?_) i
  refine Fin.cases ω (fun j => ?_) j
  exact Fin.cases ω (fun j => Fin.elim0 j) j

def zeroNodeAt : (s : ℕ) → ZeroLevel s → ZeroNode
  | 0, _ => .first
  | 1, b => .middle b
  | 2, b => .leaf b
  | _ + 3, e => e.elim

noncomputable def zeroTreeRules : TreeRules zeroTreeModel where
  xRule := fun _ _ _ _ => 0
  pRule := fun _ _ _ _ => 1
  πRule := fun _ _ _ _ _ => 0
  offRule := fun _ _ _ _ => 0

noncomputable def zeroTreeRun (ω : Bool) : TreeRunData 1 ZeroLevel where
  x := fun _ _ _ => 0
  θ := fun k s ν => zeroApprox ω k (zeroNodeAt s ν)
  β := fun _ _ _ => 0
  Qm := fun k s ν _ => zeroApprox ω k (zeroNodeAt s ν)

end RiskAverseSDDP.Subdiff.Supplement


