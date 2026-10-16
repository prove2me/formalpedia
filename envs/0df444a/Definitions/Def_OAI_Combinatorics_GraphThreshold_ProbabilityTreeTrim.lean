-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
-- name    : OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:26:57.264745+00:00
-- url     : https://prove2.me/theorems/746948a2-2f8a-46bb-8087-837a3168dac2
-- title:
--   Removing initial levels of a probability tree along fixed child choices
-- statement:
--   Let $X$ be a ground type; an *equal-depth probability tree* over $X$ is defined recursively: the only tree of depth $0$ is a leaf, and a tree of depth $d+1$ is a node consisting of a finite index set $B$, a probability law $\mu$ on $B$ that is strictly positive ($\mu(b)>0$ for all $b$, $\sum_{b}\mu(b)=1$), a finite label $A_b\subseteq X$ for each $b\in B$, and a child tree $T_b$ of depth $d$ for each $b\in B$. A *full path* is a root-to-leaf sequence of child indices. The *support* of a tree is the union of all its labels; a tree is *disjoint* if at every node each label $A_b$ is disjoint from the support of $T_b$; it *has capacities* $m=(m_0,m_1,\dots)$ if every label at level $i$ (the root is level $0$) has at most $m_i$ elements; and it *has spread* $a=(a_0,a_1,\dots)$ if every node at level $i$ satisfies $\mu\{b:\ J\subseteq A_b\}\le a_i^{|J|}$ for every nonempty finite $J\subseteq X$.
--
--   At every node one index $b^{\ast}\in B$ is fixed once and for all (it exists because $B$ is nonempty). The file defines:
--
--   1. **First child and first label.** For a tree $T$ of depth $d+1$, $\mathrm{first}(T)=T_{b^{\ast}}$ (a tree of depth $d$) and $\mathrm{firstLabel}(T)=A_{b^{\ast}}$; the map $p\mapsto(b^{\ast},p)$ turns a full path of $T_{b^{\ast}}$ into a full path of $T$.
--   2. **Dropping $k$ levels.** For a tree $T$ of depth $d+k$, $\mathrm{drop}_k(T)$ is the tree of depth $d$ obtained by applying $\mathrm{first}$ $k$ times: $\mathrm{drop}_0(T)=T$ and $\mathrm{drop}_{k+1}(T)=\mathrm{drop}_k(\mathrm{first}(T))$. A full path of $\mathrm{drop}_k(T)$ is lifted to a full path of $T$ by prepending the $k$ fixed arcs.
--   3. **Prefix union.** The union of the labels on those $k$ fixed arcs:
--   $$\mathrm{prefixUnion}_0(T)=\varnothing,\qquad \mathrm{prefixUnion}_{k+1}(T)=\mathrm{firstLabel}(T)\cup\mathrm{prefixUnion}_k\big(\mathrm{first}(T)\big).$$
--   4. **Depth recasting and truncation.** Along an equality of depths $d=e$, a tree of depth $d$ is regarded as a tree of depth $e$ without changing any data, with the identity correspondence between full paths; this recasting preserves the support, disjointness, capacities $m$ and spread $a$. For $k\le d$, $\mathrm{dropPrefix}(T,k)$ is the tree of depth $d-k$ obtained from $T$ by dropping its first $k$ levels as in item 2, together with the corresponding lift of its full paths to full paths of $T$.
--
--   The purpose of the construction is to discard leading levels whose capacity is zero: if $m_0=\dots=m_{k-1}=0$, all labels on the first $k$ levels are empty, so the choice of the retained child loses nothing and a lifted path has the same label union as the path it comes from. This keeps an exact correspondence with paths of the original tree while shortening it.
--
--   **Formalization Note** The fixed index is `Classical.choice` applied to the nonemptiness of the node's index type (`firstChild`, `firstLabel`, `prependChosen`). Dropping is defined for trees of depth `d + k` (`drop`, `liftDropPath`, `prefixUnion`) to avoid truncated subtraction; the wrappers `dropPrefix` and `liftDropPrefixPath` take a proof of `k ≤ d` and go through `castDepth` and `castPath`. The simp lemmas `support_castDepth`, `isDisjoint_castDepth`, `hasCapacities_castDepth` and `hasSpread_castDepth` are the preservation statements of item 4.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/ProbabilityTreeTrim.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/ProbabilityTreeTrim.lean by skeleton subtraction
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

namespace OAI

/-! Deterministic removal of initial zero-capacity levels. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai.ProbabilityTree

variable {X : Type}

/-- Choose one child deterministically from the actual nonempty child law. -/
def firstChild : {d : ℕ} → ProbabilityTree X (d + 1) → ProbabilityTree X d
  | _, @node _ _ _ _ law _ _ child => child (Classical.choice (branch_nonempty law))

def firstLabel : {d : ℕ} → ProbabilityTree X (d + 1) → Finset X
  | _, @node _ _ _ _ law _ label _ => label (Classical.choice (branch_nonempty law))

/-- Prepend the chosen incoming arc to a path of the chosen child. -/
def prependChosen : {d : ℕ} → (T : ProbabilityTree X (d + 1)) →
    (firstChild T).Path → T.Path
  | _, @node _ _ _ _ law _ _ _, p => ⟨Classical.choice (branch_nonempty law), p⟩

/-- Remove `k` initial levels. The additive depth form avoids subtraction casts. -/
def drop : (k : ℕ) → {d : ℕ} → ProbabilityTree X (d + k) → ProbabilityTree X d
  | 0, _, T => T
  | k + 1, _, T => drop k (firstChild T)

/-- Lift a retained path through the fixed choices on the removed prefix. -/
def liftDropPath : (k : ℕ) → {d : ℕ} → (T : ProbabilityTree X (d + k)) →
    (drop k T).Path → T.Path
  | 0, _, _, p => p
  | k + 1, _, T, p => prependChosen T (liftDropPath k (firstChild T) p)

/-- Reindex a tree along equality of depths, without changing its data. -/
def castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) : ProbabilityTree X e := h ▸ T

def castPath {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    T.Path ≃ (castDepth h T).Path := by
  cases h
  exact Equiv.refl _

/-- Subtraction-indexed convenience wrapper for removing an initial prefix. -/
def dropPrefix {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d) :
    ProbabilityTree X (d - k) :=
  drop k (castDepth (Nat.sub_add_cancel hk).symm T)

def liftDropPrefixPath {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d)
    (p : (dropPrefix T k hk).Path) : T.Path :=
  (castPath (Nat.sub_add_cancel hk).symm T).symm
    (liftDropPath k (castDepth (Nat.sub_add_cancel hk).symm T) p)

section Properties

variable [DecidableEq X]

/-- Labels committed by the deterministic choices on the removed prefix. -/
def prefixUnion : (k : ℕ) → {d : ℕ} → ProbabilityTree X (d + k) → Finset X
  | 0, _, _ => ∅
  | k + 1, _, T => firstLabel T ∪ prefixUnion k (firstChild T)

@[simp] theorem support_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    (castDepth h T).support = T.support := by cases h; rfl

@[simp] theorem isDisjoint_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    (castDepth h T).IsDisjoint ↔ T.IsDisjoint := by cases h; rfl

omit [DecidableEq X] in
@[simp] theorem hasCapacities_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (m : ℕ → ℕ) : (castDepth h T).HasCapacities m ↔ T.HasCapacities m := by cases h; rfl

@[simp] theorem hasSpread_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (a : ℕ → ℝ) : (castDepth h T).HasSpread a ↔ T.HasSpread a := by cases h; rfl

end Properties

end LeanBlast.SecondKahnKalai.ProbabilityTree

end

end OAI


