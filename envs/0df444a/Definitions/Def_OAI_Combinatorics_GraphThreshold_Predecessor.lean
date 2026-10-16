-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
-- name    : OAI_Combinatorics_GraphThreshold_Predecessor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:21:47.965303+00:00
-- url     : https://prove2.me/theorems/88c1152a-cd88-4af8-8426-c63a523c39fb
-- title:
--   Maximizing predecessors: the subset maximizing copy-containment probability divided by $\sigma^{|S|}$
-- statement:
--   1. **Finite maximizers.** For any finite set $I$ and any real-valued function $\phi$ on finite sets, some $S\subseteq I$ maximizes $\phi$ among all subsets of $I$, including $\emptyset$ and $I$ itself: $\phi(U)\le\phi(S)$ for every $U\subseteq I$. A fixed such maximizer, chosen once and for all, is denoted $\operatorname{argmax}_{S\subseteq I}\phi(S)$; it is defined also for $I=\emptyset$, where it is $\emptyset$.
--
--   2. **Predecessor score.** Let a finite group $G$ act on a set $X$, extended to finite subsets by $g\cdot F=\{g\cdot x:\ x\in F\}$. For a finite set $I\subseteq X$, let $\pi_I(S)$ be the probability that a uniformly random member of the set of distinct copies $\{g\cdot I:\ g\in G\}$ contains $S$. For $\sigma\in\mathbb{R}$ and a finite set $S\subseteq X$, the predecessor score is
--
--      $$\operatorname{score}_{I,\sigma}(S)=\frac{\pi_I(S)}{\sigma^{|S|}},$$
--
--      and it satisfies $\operatorname{score}_{I,\sigma}(\emptyset)=1$.
--
--   3. **Maximizing predecessor.** The maximizing predecessor of $I$ at level $\sigma$ is
--
--      $$\operatorname{pred}_\sigma(I)=\operatorname{argmax}_{S\subseteq I}\ \operatorname{score}_{I,\sigma}(S).$$
--
--   Because the predecessor $S=\operatorname{pred}_\sigma(I)$ maximizes the score, for $\sigma>0$ every $U\subseteq I$ satisfies $\pi_I(U)\le\sigma^{|U|-|S|}\,\pi_I(S)$; in particular, adding $j$ further elements of $I$ to $S$ multiplies the containment probability by at most $\sigma^{j}$. This maximality is what makes the uniform law on copies of $I$ extending a copy of the predecessor $\sigma$-spread, which drives the construction of a hierarchy of predecessors and a spread tree of nested copies.
--
--   **Formalization Note** The members are `exists_powerset_max`, `maximizingSubset I score` (a choice via `Classical.choose`), `predecessorScore G I σ S` (defined with `containmentProb`), `maximizingPredecessor G I σ` and `predecessorScore_empty`. Lean's division convention $x/0=0$ applies: if $\sigma=0$, every nonempty $S$ has score $0$, while $\sigma^0=1$ keeps the score of $\emptyset$ equal to $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean by skeleton subtraction
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

namespace OAI

/-!
# Maximizing predecessors

The predecessor is chosen by maximization over the actual finite powerset,
including its empty member.  The graph application uses distinct group-orbit
copies and the actual containment probability, not labeled embeddings.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

section FiniteMaximum

variable {X : Type*}

 theorem exists_powerset_max (I : Finset X) (score : Finset X → ℝ) :
    ∃ S ∈ I.powerset, ∀ U ∈ I.powerset, score U ≤ score S :=
  Finset.exists_max_image I.powerset score ⟨∅, by simp⟩

/-- A deterministic classical choice of a maximizer over all subsets of `I`.
The empty set is included, so this definition also applies to empty `I`. -/
def maximizingSubset (I : Finset X) (score : Finset X → ℝ) : Finset X :=
  (exists_powerset_max I score).choose

end FiniteMaximum

section OrbitPredecessor

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

def predecessorScore (I : Finset X) (σ : ℝ) (S : Finset X) : ℝ :=
  containmentProb G I S / σ ^ S.card

/-- The actual maximizing predecessor; the finite choice includes the empty set. -/
def maximizingPredecessor (I : Finset X) (σ : ℝ) : Finset X :=
  maximizingSubset I (predecessorScore G I σ)

@[simp]
theorem predecessorScore_empty (I : Finset X) (σ : ℝ) :
    predecessorScore G I σ ∅ = 1 := by
  simp [predecessorScore]

end OrbitPredecessor

end LeanBlast.SecondKahnKalai

end

end OAI


