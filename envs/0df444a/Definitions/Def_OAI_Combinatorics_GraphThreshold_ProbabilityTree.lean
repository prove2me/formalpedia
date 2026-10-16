-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
-- name    : OAI_Combinatorics_GraphThreshold_ProbabilityTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:19:21.397718+00:00
-- url     : https://prove2.me/theorems/ec6a6743-f58d-4d6b-ad7f-e750423d10eb
-- title:
--   Probability trees with set-labelled arcs: paths, coverage, disjointness, spread and capacities
-- statement:
--   Fix a set $X$. A finite law on a finite set $B$ is a weight function $\mu:B\to\mathbb{R}$ with $\mu(b)\ge 0$ and $\sum_b\mu(b)=1$. A **probability tree** of depth $d\in\mathbb{N}$ over $X$ is defined recursively: a tree of depth $0$ is a single leaf, and a tree of depth $d+1$ is a node consisting of a finite set $B$ of children, a finite law $\mu$ on $B$ that is strictly positive ($\mu(b)>0$ for every $b$), a finite label $L(b)\subseteq X$ on the arc to each child $b$, and a probability tree $T_b$ of depth $d$ for each $b\in B$. All leaves therefore lie at depth $d$, and every node has at least one child. For such a tree $T$ the file defines:
--
--   1. **Paths.** A full path is a root-to-leaf sequence of choices: a leaf has exactly one (empty) path, and a path of a node is a pair $(b,\gamma)$ with $b\in B$ and $\gamma$ a path of $T_b$. Different choice sequences are different paths even if their labels coincide; there are finitely many paths. Along a path $\gamma=(b_1,\dots,b_d)$ the labels form the list $(L_1,\dots,L_d)$ in root-to-leaf order, and their union is $U(\gamma)=L_1\cup\dots\cup L_d$.
--
--   2. **Support.** $\operatorname{supp}(T)$ is the union of all arc labels anywhere in $T$; it is empty for a leaf.
--
--   3. **Disjointness.** $T$ is disjoint if at every node each label $L(b)$ is disjoint from $\operatorname{supp}(T_b)$. Since every node has a child, this says that along every full path the labels are pairwise disjoint.
--
--   4. **Spread.** For a real sequence $a=(a_0,a_1,\dots)$, $T$ has spread $a$ if at every node of depth $i$ (the root has depth $0$) the labels are $a_i$-spread under the node's law: for every nonempty finite $J\subseteq X$,
--
--      $$\mu\bigl(\{b\in B:\ J\subseteq L(b)\}\bigr)\le a_i^{|J|} .$$
--
--   5. **Capacities.** For a sequence $m=(m_0,m_1,\dots)$ of natural numbers, $T$ has capacities $m$ if every label on an arc leaving a node of depth $i$ has at most $m_i$ elements.
--
--   6. **Coverage.** A finite set $W\subseteq X$ covers $T$ if $U(\gamma)\subseteq W$ for some full path $\gamma$. A tree of depth $0$ is covered by every $W$.
--
--   7. **Locality of set functions.** For finite $S,A\subseteq X$ and a function $f$ on finite subsets of $X$ with values in any set: $f$ depends only on $S$ if $f(W)=f(W')$ whenever $W\cap S=W'\cap S$, and $f$ depends only on the coordinates outside $A$ if $f(W)=f(W')$ whenever $W\setminus A=W'\setminus A$.
--
--   A probability tree records a multi-stage random construction of a set: walking from the root and sampling each child from its law collects the labels along a random path. In the threshold argument, one shows that a $p$-random subset of $X$ covers a disjoint tree with suitable spread and capacities with good probability; the locality notions allow Bernoulli expectations to be factored over disjoint sets of coordinates.
--
--   **Formalization Note** `ProbabilityTree X d` is an inductive family (constructors `leaf` and `node`) for `X : Type`; the derived notions are `Path` (a dependent sigma type, with `Fintype` instance `pathFintype`), `pathLabels`, `pathUnion`, `support`, `IsDisjoint`, `HasSpread` (built from `IsSpread`), `HasCapacities`, `CoveredBy`, `DependsOnlyOn` and `DependsOutside`. The spread and capacity sequences are shifted by one index at each level of the recursion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/ProbabilityTree.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/ProbabilityTree.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

/-- Equal-depth trees carrying an actual strictly positive child law at every branch. -/
inductive ProbabilityTree (X : Type) : ℕ → Type 1
  | leaf : ProbabilityTree X 0
  | node {d : ℕ} (B : Type) [Fintype B] (law : FiniteLaw B)
      (positive : law.IsPositive) (label : B → Finset X)
      (child : B → ProbabilityTree X d) : ProbabilityTree X (d + 1)

/-- A function inspects only the indicated coordinates of its input subset. -/
def DependsOnlyOn {X β : Type*} [DecidableEq X] (S : Finset X)
    (f : Finset X → β) : Prop :=
  ∀ W V, W ∩ S = V ∩ S → f W = f V

/-- A function is unchanged by modifications inside the indicated coordinates. -/
def DependsOutside {X β : Type*} [DecidableEq X] (A : Finset X)
    (f : Finset X → β) : Prop :=
  ∀ W V, W \ A = V \ A → f W = f V

namespace ProbabilityTree

variable {X : Type}

/-- Full root-to-leaf paths, retaining distinct child-index histories. -/
def Path : {d : ℕ} → ProbabilityTree X d → Type
  | _, .leaf => PUnit
  | _, @node _ _ B _ _ _ _ child => Σ b : B, Path (child b)

/-- The list of arc labels along a full path, in root-to-leaf order. -/
def pathLabels : {d : ℕ} → (T : ProbabilityTree X d) → T.Path → List (Finset X)
  | _, .leaf => fun _ => []
  | _, @node _ _ _B _ _ _ label child => fun p =>
      label p.1 :: pathLabels (child p.1) p.2

/-- Every path family is finite; no quotient by labels is taken. -/
instance pathFintype : {d : ℕ} → (T : ProbabilityTree X d) → Fintype T.Path
  | _, .leaf => inferInstanceAs (Fintype PUnit)
  | _, @node _ _ B _ _ _ _ child => by
      letI : ∀ b : B, Fintype (Path (child b)) := fun b => pathFintype (child b)
      exact inferInstanceAs (Fintype (Σ b : B, Path (child b)))

section Labels

variable [DecidableEq X]

/-- Union of all arc labels along a specified full path. -/
def pathUnion : {d : ℕ} → (T : ProbabilityTree X d) → T.Path → Finset X
  | _, .leaf => fun _ => ∅
  | _, @node _ _ _B _ _ _ label child => fun p =>
      label p.1 ∪ pathUnion (child p.1) p.2

/-- All coordinates used by any arc anywhere in the tree. -/
def support : {d : ℕ} → ProbabilityTree X d → Finset X
  | _, .leaf => ∅
  | _, @node _ _ B inst _ _ label child =>
      (@Finset.univ B inst).biUnion fun b => label b ∪ support (child b)

/-- A recursive form of disjointness, equivalent to pairwise disjoint labels on every full path. -/
def IsDisjoint : {d : ℕ} → ProbabilityTree X d → Prop
  | _, .leaf => True
  | _, @node _ _ _ _ _ _ label child =>
      (∀ b, Disjoint (label b) (support (child b))) ∧ ∀ b, IsDisjoint (child b)

/-- Per-level spread conditions, starting with index zero at the root. -/
def HasSpread : {d : ℕ} → ProbabilityTree X d → (ℕ → ℝ) → Prop
  | _, .leaf, _ => True
  | _, @node _ _ _ _ law _ label child, a =>
      IsSpread law label (a 0) ∧ ∀ b, HasSpread (child b) (fun j => a (j + 1))

/-- The event that some full path is covered by a given set. -/
def CoveredBy {d : ℕ} (T : ProbabilityTree X d) (W : Finset X) : Prop :=
  ∃ p : T.Path, T.pathUnion p ⊆ W

end Labels

/-- Per-level cardinality capacities, starting with index zero at the root. -/
def HasCapacities : {d : ℕ} → ProbabilityTree X d → (ℕ → ℕ) → Prop
  | _, .leaf, _ => True
  | _, @node _ _ _ _ _ _ label child, m =>
      (∀ b, (label b).card ≤ m 0) ∧ ∀ b, HasCapacities (child b) (fun j => m (j + 1))

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI


