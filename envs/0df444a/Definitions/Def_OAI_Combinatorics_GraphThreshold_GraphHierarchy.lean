-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
-- name    : OAI_Combinatorics_GraphThreshold_GraphHierarchy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:23:48.93614+00:00
-- url     : https://prove2.me/theorems/d8c81b05-c22f-4ede-a20e-7a05b489938c
-- title:
--   Predecessor hierarchies and the uniform tree of nested orbit-copy extensions
-- statement:
--   1. **Set hierarchy.** Let $X$ be a set, let $R$ be a relation between finite subsets of $X$ (read $R(S,I)$ as "$S$ is the selected predecessor of $I$"), and let $H\subseteq X$ be finite. An $R$-hierarchy for $H$ consists of a depth $d\in\mathbb{N}$ and a sequence of finite sets $H_0,H_1,H_2,\dots\subseteq X$ such that $H_0=\emptyset$, $H_d=H$, and for every $i<d$
--
--      $$H_i\subseteq H_{i+1},\qquad 17\,|H_i|<|H_{i+1}|,\qquad R(H_i,H_{i+1}).$$
--
--      Its capacity at level $i$ is $c_i=|H_{i+1}|-|H_i|$, the number of elements added at that level.
--
--   2. **Orbit extension tree.** Let a finite group $G$ act on $X$, extended to finite subsets by $g\cdot F=\{g\cdot x:\ x\in F\}$, and let $\mathcal{C}(F)=\{g\cdot F:\ g\in G\}$ be the set of distinct copies of $F$. A probability tree of depth $d$ over $X$ is a leaf if $d=0$, and otherwise a root with a finite set of children carrying a strictly positive probability law, a finite subset of $X$ labelling each arc, and a probability tree of depth $d-1$ below each child. Given $d\in\mathbb{N}$, finite sets $A_0,A_1,A_2,\dots\subseteq X$ with $A_i\subseteq A_{i+1}$ for every $i<d$, and a copy $S_0\in\mathcal{C}(A_0)$, the tree $\mathcal{T}_d(A;S_0)$ is defined recursively. For $d=0$ it is a leaf. For depth $d+1$:
--      - the children of the root are the distinct copies $J\in\mathcal{C}(A_1)$ with $S_0\subseteq J$, chosen with the uniform law (this set is nonempty because $A_0\subseteq A_1$, so a copy of $A_0$ extends to a copy of $A_1$);
--      - the arc to the child $J$ is labelled by $J\setminus S_0$;
--      - the subtree at $J$ is $\mathcal{T}_d(A';J)$ for the shifted sequence $A'_i=A_{i+1}$.
--
--   Thus a full path of $\mathcal{T}_d(A;S_0)$ is a chain $S_0=J_0\subseteq J_1\subseteq\dots\subseteq J_d$ with $J_i\in\mathcal{C}(A_i)$, where each $J_i$ is uniform among the copies of $A_i$ containing $J_{i-1}$, and its labels are the increments $J_i\setminus J_{i-1}$; distinct histories remain distinct paths even when they end at the same set. When $A_0=\emptyset$ (so $S_0=\emptyset$), the union of the labels along every path is a copy $J_d$ of $A_d$.
--
--   A hierarchy turns a target set into a short chain of rapidly growing sets, each obtained from the previous one by the predecessor rule $R$; feeding its stages into the orbit extension tree produces a random multi-stage construction of a copy of the target, with level-$i$ labels of size at most $|A_{i+1}|-|A_i|$. In the graph application $X$ is the edge set of $K_n$, $G$ is the symmetric group acting by relabelling vertices, and the target is the edge set of a placement of the fixed graph $H$ in $K_n$.
--
--   **Formalization Note** `SetHierarchy R H` is a structure with fields `depth`, `stage`, `first`, `last`, `nested`, `sparse` and `selected`; `stage` is indexed by all of $\mathbb{N}$, but only the stages $i\le d$ are constrained. `SetHierarchy.capacity` uses truncated subtraction of natural numbers, which is exact for $i<d$ because the stages are nested. `orbitExtensionTree G d A hnested S0 hS0` is built from `ExtensionCopy`, `extensionLaw` and `extensionLaw_isPositive`, and requires `X : Type`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The finite hierarchy and the actual tree of extensions used in the graph
application. Histories are represented by the probability tree's dependent
paths; equal set labels do not identify distinct histories. -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

/-- A reversed predecessor chain, with its first term empty and last term the
given set. The relation records the actual rule used to select predecessors. -/
structure SetHierarchy {X : Type*} [DecidableEq X]
    (R : Finset X → Finset X → Prop) (H : Finset X) where
  depth : ℕ
  stage : ℕ → Finset X
  first : stage 0 = ∅
  last : stage depth = H
  nested : ∀ i, i < depth → stage i ⊆ stage (i + 1)
  sparse : ∀ i, i < depth → 17 * (stage i).card < (stage (i + 1)).card
  selected : ∀ i, i < depth → R (stage i) (stage (i + 1))

namespace SetHierarchy

variable {X : Type*} [DecidableEq X]
variable {R : Finset X → Finset X → Prop} {H : Finset X}

/-- The number of new elements on a level of the hierarchy. -/
def capacity (h : SetHierarchy R H) (i : ℕ) : ℕ :=
  (h.stage (i + 1)).card - (h.stage i).card

end SetHierarchy

section OrbitTrees

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

/-- The actual extension tree. At each node its children are all distinct
copies of the next set containing the current copy, with their uniform law.
The dependent path type retains the entire sequence of choices. -/
def orbitExtensionTree : (d : ℕ) → (A : ℕ → Finset X) →
    (∀ i, i < d → A i ⊆ A (i + 1)) →
    (S0 : Finset X) → S0 ∈ copyOrbit G (A 0) → ProbabilityTree X d
  | 0, _, _, _, _ => .leaf
  | d + 1, A, hnested, S0, hS0 =>
      let hp := containmentProb_pos_of_copy_subset G (hnested 0 (by omega)) hS0
      .node (ExtensionCopy G (A 1) S0)
        (extensionLaw G (A 1) S0 hp)
        (extensionLaw_isPositive G (A 1) S0 hp)
        (fun b => b.val.val \ S0)
        (fun b => orbitExtensionTree d (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property)

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI


