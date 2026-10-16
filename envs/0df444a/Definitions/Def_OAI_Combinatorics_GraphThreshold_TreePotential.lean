-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
-- name    : OAI_Combinatorics_GraphThreshold_TreePotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:37:27.228368+00:00
-- url     : https://prove2.me/theorems/41f6e4f9-b0ad-4bfa-81dc-a236d669571b
-- title:
--   The recursive bad-node potential of a probability tree and its deterministic envelope
-- statement:
--   The file defines a potential that dominates the indicator of a bad (not good) node in a probability tree, together with a deterministic bound obtained by iterating its expectation recursion.
--
--   1. **Node potential.** Let $B$ be a finite set and $m\in\mathbb N$. For a failure mass $\varphi\in\mathbb{R}$, target masses $t:B\to\mathbb{R}$ and child potentials $\pi:B\to\mathbb{R}$,
--   $$\mathrm{node}_m(\varphi,t,\pi)=\frac{\varphi+\sum_{b\in B}t(b)\,\pi(b)}{e^{-m}}=e^{m}\Big(\varphi+\sum_{b\in B}t(b)\,\pi(b)\Big).$$
--   2. **Envelope.** For $d\in\mathbb N$ and a capacity sequence $m=(m_0,m_1,\dots)$ of natural numbers,
--   $$\mathcal E_0(m)=0,\qquad \mathcal E_{d+1}(m)=e^{-8m_0}+e^{12m_0}\,\mathcal E_d(m_1,m_2,\dots).$$
--   3. **Tree potential.** Let $X$ be a finite type with decidable equality, $p\in\mathbb{R}$, $W\subseteq X$ and $m$ as above. An equal-depth probability tree over $X$ is either a leaf or a node with a finite index set $B$, a strictly positive law $\nu$ on $B$, finite labels $A_b\subseteq X$ and child trees $T_b$ of one smaller depth. At such a node consider the planted resampling transition with parameter $p$,
--   $$P_W(c,b)=\nu(c)\,\frac{\mathbf 1[A_b\subseteq W\cup A_c]\,\nu(b)\,p^{-|A_b|}}{Z(W\cup A_c)},\qquad Z(Y)=\sum_{b:\ A_b\subseteq Y}\nu(b)\,p^{-|A_b|},$$
--   call $(c,b)$ a local success if $e^{-10m_0}\le Z(W\cup A_c)$ and $|A_b\setminus W|\le\lfloor m_0/2\rfloor$ and a local failure otherwise, and let $s_W(b)=\sum_c\mathbf 1[\text{success}]\,P_W(c,b)$ and $f_W=\sum_{b,c}\mathbf 1[\text{failure}]\,P_W(c,b)$. The tree potential is $\Phi_{p,m,W}(\text{leaf})=0$ and
--   $$\Phi_{p,m,W}(T)=\mathrm{node}_{m_0}\Big(f_W,\ s_W,\ b\mapsto\Phi_{p,(m_1,m_2,\dots),W}(T_b)\Big).$$
--
--   For $p>0$, a tree that is not good (at some node the successful mass reaching good children is below $1-e^{-m_0}$) has potential greater than $1$, so for $0<p\le1$ the probability that the tree is not good is at most the expected potential when $W$ is a $p$-random subset of $X$. Under disjointness, capacity and spread hypotheses, this expectation is bounded by the envelope $\mathcal E_d(m)$, which unfolds to $\sum_{j<d}\exp\big(12\sum_{h<j}m_h-8m_j\big)$. All nodes use the same random set; the expectation argument relies on an outside-coordinate change of measure rather than on independence between nodes.
--
--   **Formalization Note** The objects are `nodePotential`, `potentialEnvelope` and `treePotential`; the latter uses `localFailureMass` and `successfulTargetMass` and is defined by recursion on the depth, with the capacity sequence shifted by one level at each child. Division by $e^{-m}$ is division by a positive real.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The bad-node potential for simultaneous tree reduction

All nodes in a reduction use the same random set. The expectation argument
uses an outside-coordinate change of measure, rather than independence of
node outcomes.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

/-- One step of the actual recursive bad-node potential. -/
def nodePotential {B : Type*} [Fintype B] (m : ℕ) (failure : ℝ)
    (target childPotential : B → ℝ) : ℝ :=
  (failure + ∑ b, target b * childPotential b) / Real.exp (-(m : ℝ))

/-- Deterministic envelope obtained by iterating the expectation recursion. -/
def potentialEnvelope : ℕ → (ℕ → ℕ) → ℝ
  | 0, _ => 0
  | d + 1, m => Real.exp (-8 * (m 0 : ℝ)) + Real.exp (12 * (m 0 : ℝ)) *
      potentialEnvelope d (fun j => m (j + 1))

section Trees

variable {X : Type} [Fintype X] [DecidableEq X]

def treePotential (p : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) : ℝ :=
  match T with
  | .leaf => 0
  | @ProbabilityTree.node _ _ B inst ν hν A child =>
      nodePotential (m 0) (localFailureMass ν A p (m 0) W)
        (successfulTargetMass ν A p (m 0) W)
        (fun b => treePotential p (fun j => m (j + 1)) W (child b))
termination_by d

end Trees

end LeanBlast.SecondKahnKalai

end

end OAI


