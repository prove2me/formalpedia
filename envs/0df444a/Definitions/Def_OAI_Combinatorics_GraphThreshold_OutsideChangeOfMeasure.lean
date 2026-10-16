-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
-- name    : OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:36:01.340591+00:00
-- url     : https://prove2.me/theorems/ab8f99ff-93f8-4f95-9c72-47bbfdcb4834
-- title:
--   Target marginal of the resampling transition restricted to a density cutoff
-- statement:
--   Let $X$ be a type with decidable equality, $B$ a finite index set, $\nu$ a finite law on $B$ (weights $\nu(b)\ge0$ summing to $1$), $(A_b)_{b\in B}$ finite labels $A_b\subseteq X$, $p$ and $\delta$ real numbers, and $W\subseteq X$ a finite set. For a finite $Y\subseteq X$ let $Z(Y)=\sum_{b\in B:\ A_b\subseteq Y}\nu(b)\,p^{-|A_b|}$, and let
--   $$P_W(c,b)=\nu(c)\,\frac{\mathbf 1[A_b\subseteq W\cup A_c]\;\nu(b)\,p^{-|A_b|}}{Z(W\cup A_c)}$$
--   be the weight of source $c$ and target $b$ in the planted resampling transition with parameter $p$. The *cutoff target mass* of a target $b\in B$ is
--   $$\mathrm{cut}_{\delta}(W,b)=\sum_{c\in B}\mathbf 1\big[\delta\le Z(W\cup A_c)\big]\;P_W(c,b),$$
--   the weight of the event that the transition ends at $b$ and the density at the observed set $W\cup A_c$ is at least $\delta$.
--
--   This quantity is the object of an outside-coordinate change of measure. When $W$ is a $p$-random subset of a finite $X$ and $f\ge0$ is an observable that does not depend on the coordinates in the target label $A_b$, the expectation of $\mathrm{cut}_{\delta}(W,b)\,f(W)$ is compared with $\nu(b)$ times the expectation of $f$; with $\delta=e^{-10m}$, $0<p\le1$, a capacity bound $|A_b|\le m$ and an $a$-spread hypothesis on $(\nu,A)$ with $0\le a\le e^{-50}p$, the loss is at most a factor $e^{11m}$. The observable may depend on the same random set used at every other tree node; only its insensitivity to the fixed target's label is required, and no independence between different tree nodes is assumed.
--
--   **Formalization Note** The definition is `cutoffTargetMass ν A p δ W b`, with $Z$ given by `resamplingZ` and $P_W$ by `resamplingWeight`; the indicator is decided classically. As elsewhere, $p^{-|A_b|}$ uses Lean's inverse ($0^{-1}=0$) and a division by $Z=0$ returns $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Outside-coordinate change of measure for the actual resampling transition

The observable may depend on the same Bernoulli set used at every other tree
node.  The only locality required here is that it ignores the fixed target's
incoming label.  No independence between different tree nodes is assumed.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- Actual target marginal restricted to the event that the density is at least `δ`. -/
def cutoffTargetMass (ν : FiniteLaw B) (A : B → Finset X) (p δ : ℝ)
    (W : Finset X) (b : B) : ℝ :=
  ∑ c, if δ ≤ resamplingZ ν A p (resamplingY A W c)
    then resamplingWeight ν A p W (c, b) else 0

variable [Fintype X]

end LeanBlast.SecondKahnKalai

end

end OAI


