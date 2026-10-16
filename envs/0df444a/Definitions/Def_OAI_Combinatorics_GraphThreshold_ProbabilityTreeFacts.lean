-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
-- name    : OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:25:51.236803+00:00
-- url     : https://prove2.me/theorems/f182b4a9-0d6d-4676-9a5d-72182ef65469
-- title:
--   Full paths of equal-depth probability trees exist and carry one label per level
-- statement:
--   Fix a ground type $X$. An an *equal-depth probability tree* over $X$ is defined recursively: the only tree of depth $0$ is a leaf, and a tree of depth $d+1$ is a node consisting of a finite index set $B$, a probability law $\mu$ on $B$ that is strictly positive ($\mu(b)>0$ for all $b$, $\sum_{b}\mu(b)=1$), a finite label $A_b\subseteq X$ for each $b\in B$, and a child tree $T_b$ of depth $d$ for each $b\in B$. A *full path* of a node is a pair $(b,p)$ with $b\in B$ and $p$ a full path of $T_b$; the leaf has exactly one (empty) path. Paths are distinguished by their index histories, not by their labels. The *label list* $\mathrm{labels}_T(p)$ of a full path $p=(b_1,b_2,\dots)$ is the list of arc labels $(A_{b_1},A_{b_2},\dots)$ in root-to-leaf order.
--
--   The file records the following facts and one auxiliary choice.
--
--   1. **Nonempty branching.** If $\mu$ is a finite law on a finite set $B$ (nonnegative weights summing to $1$), then $B$ is nonempty.
--   2. **Existence of full paths.** Every equal-depth probability tree $T$ has at least one full path.
--   3. **A fixed path.** $\mathrm{choosePath}(T)$ is one full path of $T$, fixed once and for all by a choice; it is used only to resolve finite choices in later constructions.
--   4. **Length of label lists.** For every tree $T$ of depth $d$ and every full path $p$ of $T$,
--   $$\big|\mathrm{labels}_T(p)\big|=d .$$
--
--   Probability trees encode multi-level families of random labels (at each node a label is selected according to the node's law), whose covering by a random set is studied in this development. These facts ensure that path-indexed objects are never vacuous and that every full path passes through exactly one label on each of the $d$ levels.
--
--   **Formalization Note** The tree type is the inductive family `ProbabilityTree X d` with constructors `leaf` and `node`, so the depth is part of the type, and paths form the type `T.Path`. Item 1 is `branch_nonempty`, item 2 is the instance `pathNonempty`, item 3 is `choosePath` (via `Classical.choice`) and item 4 is `pathLabels_length`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/ProbabilityTreeFacts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/ProbabilityTreeFacts.lean by skeleton subtraction
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

namespace OAI

/-! Path and locality facts for the stable finite probability-tree representation. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

section Locality

variable {X β : Type*} [DecidableEq X] {S T A : Finset X} {f : Finset X → β}

end Locality

namespace ProbabilityTree

variable {X : Type}

/-- A finite law of total mass one has a nonempty underlying type. -/
theorem branch_nonempty {B : Type} [Fintype B] (law : FiniteLaw B) : Nonempty B := by
  classical
  by_contra h
  let : IsEmpty B := not_nonempty_iff.mp h
  have ht := law.total
  simp at ht

/-- Every equal-depth probability tree has at least one full path. -/
instance pathNonempty {d : ℕ} (T : ProbabilityTree X d) : Nonempty T.Path := by
  induction T with
  | leaf => exact ⟨PUnit.unit⟩
  | @node d B inst law positive label child ih =>
      let b : B := Classical.choice (branch_nonempty law)
      exact ⟨⟨b, Classical.choice (ih b)⟩⟩

/-- A fixed deterministic full path, used only to resolve finite choices. -/
def choosePath {d : ℕ} (T : ProbabilityTree X d) : T.Path := Classical.choice (pathNonempty T)

@[simp] theorem pathLabels_length {d : ℕ} (T : ProbabilityTree X d) (p : T.Path) :
    (T.pathLabels p).length = d := by
  induction T with
  | leaf => rfl
  | @node d B inst law positive label child ih =>
      rcases p with ⟨b, p⟩
      simpa [pathLabels] using congrArg Nat.succ (ih b p)

section Labels

variable [DecidableEq X]

end Labels

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI


