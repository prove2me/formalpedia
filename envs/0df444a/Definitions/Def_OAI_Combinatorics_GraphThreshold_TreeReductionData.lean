-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
-- name    : OAI_Combinatorics_GraphThreshold_TreeReductionData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:32:17.945017+00:00
-- url     : https://prove2.me/theorems/deb0336f-8eca-40ff-907a-0bda8c510cf3
-- title:
--   Successful target masses and the good-node predicate for simultaneous tree reduction
-- statement:
--   Let $X$ be a type with decidable equality, $B$ a finite index set, $\mu$ a finite law on $B$ (weights $\mu(b)\ge0$ summing to $1$), $(A_b)_{b\in B}$ finite labels $A_b\subseteq X$, $\rho\in\mathbb{R}$, $m\in\mathbb N$ and $W\subseteq X$ a finite set. Recall the resampling data: for a finite $Y\subseteq X$ let $Z(Y)=\sum_{b\in B:\ A_b\subseteq Y}\mu(b)\,\rho^{-|A_b|}$, and let
--   $$P_W(c,b)=\mu(c)\,\frac{\mathbf 1[A_b\subseteq W\cup A_c]\;\mu(b)\,\rho^{-|A_b|}}{Z(W\cup A_c)}\qquad(c,b\in B)$$
--   be the weight of source $c$ and target $b$ in the planted resampling transition. A pair $(c,b)$ is a *local success at capacity $m$* if $e^{-10m}\le Z(W\cup A_c)$ and $|A_b\setminus W|\le\lfloor m/2\rfloor$, and a *local failure* otherwise.
--
--   1. **Successful target mass.** $s^{(m)}_W(b)=\sum_{c\in B}\mathbf 1[(c,b)\text{ is a local success}]\;P_W(c,b)$, the weight with which the transition ends at target $b$ through a local success. It is nonnegative whenever $\rho\ge0$.
--   2. **Local failure mass.** $f^{(m)}_W=\sum_{b\in B}\sum_{c\in B}\mathbf 1[(c,b)\text{ is a local failure}]\;P_W(c,b)$, the total weight of local failures.
--   3. **Good trees.** An equal-depth probability tree over $X$ is either a leaf (depth $0$) or a node of depth $d+1$ with a finite index set $B$, a strictly positive law $\mu$ on $B$, finite labels $A_b\subseteq X$ and child trees $T_b$ of depth $d$. Let $m=(m_0,m_1,\dots)$ be a sequence of natural numbers (capacities by level). A leaf is good for $(\rho,m,W)$. A node is good for $(\rho,m,W)$ if
--   $$1-e^{-m_0}\ \le \sum_{\substack{b\in B\\ T_b\text{ good for }(\rho,\,(m_1,m_2,\dots),\,W)}} s^{(m_0)}_W(b),$$
--   where $s^{(m_0)}_W$ is computed from the node's own law $\mu$ and labels $(A_b)$.
--
--   Goodness is evaluated on the fixed input tree, with the same set $W$ and parameter $\rho$ at every node and with the local masses taken before any pruning or reweighting: a node is good when at least a $1-e^{-m_0}$ fraction of the resampling weight reaches, through local successes, children that are themselves good. Good trees are the input of the pruning-and-renormalization step of the simultaneous tree reduction, and the local failure mass enters the potential used to bound the probability that a tree is not good.
--
--   **Formalization Note** The masses are `successfulTargetMass μ A ρ m W b` and `localFailureMass μ A ρ m W`, built from `resamplingWeight`, `LocalSuccess` and `LocalFailure`; the predicate `Good ρ m W T` is defined by recursion on the depth, with the capacity sequence shifted by one level when passing to children.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeReductionData.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeReductionData.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SecondKahnKalai mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents

namespace OAI

/-! Fixed-input local masses and the deterministic good-node predicate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

section LocalMasses

variable {X B : Type*} [DecidableEq X] [Fintype B]

def successfulTargetMass (μ : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (b : B) : ℝ :=
  ∑ c, if LocalSuccess μ A ρ m W c b then resamplingWeight μ A ρ W (c, b) else 0

def localFailureMass (μ : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) : ℝ :=
  ∑ b, ∑ c, if LocalFailure μ A ρ m W c b then resamplingWeight μ A ρ W (c, b) else 0

theorem successfulTargetMass_nonneg (μ : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) (W : Finset X) (b : B) :
    0 ≤ successfulTargetMass μ A ρ m W b := by
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact resamplingWeight_nonneg μ A hρ W (c, b)
  · exact le_rfl

end LocalMasses

variable {X : Type} [DecidableEq X]

/-- Goodness is evaluated on the fixed input tree, using local nonfailure
target masses before any pruning or reweighting. -/
def Good (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ} (T : ProbabilityTree X d) : Prop :=
  match T with
  | .leaf => True
  | @ProbabilityTree.node _ _ B inst μ _hμ A child =>
      1 - Real.exp (-(m 0 : ℝ)) ≤
        ∑ b, if Good ρ (fun j => m (j + 1)) W (child b) then
          successfulTargetMass μ A ρ (m 0) W b else 0
termination_by d

end LeanBlast.SecondKahnKalai

end

end OAI


