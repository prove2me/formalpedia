-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering
-- name    : OAI_Combinatorics_GraphThreshold_TreeCovering
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:38:10.849621+00:00
-- url     : https://prove2.me/theorems/5e1ffd15-2e3c-455b-9814-3e0ec47e4190
-- title:
--   Covering a probability tree by iterated reductions: recovery, cover states and rank
-- statement:
--   Let $X$ be a type with decidable equality. An equal-depth probability tree over $X$ is either a leaf (depth $0$) or a node of depth $d+1$ with a finite index set $B$, a strictly positive law $\mu$ on $B$, finite labels $A_b\subseteq X$ and child trees $T_b$ of depth $d$. For a full path $p$ (a root-to-leaf sequence of indices) of a tree $T$, let $U_T(p)$ be the union of the labels along $p$. A tree is *disjoint* if at every node each label $A_b$ is disjoint from all labels occurring in $T_b$; it *has capacities* $c=(c_0,c_1,\dots)$ if every label at level $i$ (the root is level $0$) has at most $c_i$ elements; it *has spread* $a=(a_0,a_1,\dots)$ if every node at level $i$ satisfies $\mu\{b:\ J\subseteq A_b\}\le a_i^{|J|}$ for all nonempty finite $J\subseteq X$. For $\sigma\in\mathbb{R}$ and $m\in\mathbb N$ let
--   $$\mathrm{res}(\sigma,m)=4\sigma\prod_{j=1}^{m}\big(1-e^{-j}\big)$$
--   be the capacity reserve, and let $\mathrm{succ}(l)=\lfloor\log_2 l\rfloor+1$ for $l\ge1$ (and $\mathrm{succ}(0)=1$).
--
--   1. **Recovery.** A tree $S$ *recovers* a tree $T$ with collected set $W\subseteq X$ if every full path of $S$, completed by $W$, contains a full path of $T$:
--   $$\forall q\ \exists p:\qquad U_T(p)\subseteq W\cup U_S(q).$$
--   Every tree recovers itself with $W=\varnothing$, and recovery is preserved when $W$ is enlarged.
--   2. **Monotonicity of spread.** If $T$ has depth $d$ and spread $a$, and $0\le a_i\le b_i$ for every $i<d$, then $T$ has spread $b$.
--   3. **Cover states.** Fix an original tree $T_0$ of depth $k$ and $\sigma\in\mathbb{R}$. A cover state consists of a depth $e$, a tree $S$ of depth $e$, capacities $c:\mathbb N\to\mathbb N$ and a collected set $U\subseteq X$ such that $S$ is disjoint, has capacities $c$, has spread $\big(\mathrm{res}(\sigma,c_i)\big)_{i}$, satisfies $c_i>0$ for $i<e$ and $16\,c_i\le c_{i+1}$ whenever $i+1<e$, and recovers $T_0$ with collected set $U$.
--   4. **Initial state.** If $\sigma>0$ and $T_0$ is disjoint, has capacities $m$ with $m_i>0$ for $i<k$ and $16\,m_i\le m_{i+1}$ for $i+1<k$, and has spread $\sigma$ at every level, then $(k,T_0,m,\varnothing)$ is a cover state; its spread requirement holds because $\sigma\le\mathrm{res}(\sigma,m_i)$.
--   5. **Rank.** The rank of a state is $0$ if $e=0$ and $\mathrm{succ}(c_{e-1})$ otherwise, where $c_{e-1}$ is the capacity of the deepest level; the rank is $0$ exactly when $e=0$.
--   6. **Accumulation, advance and step.** $\mathrm{acc}(\mathcal C,W)$ adds a draw $W$ to the collected set and changes nothing else, so it has the same rank. A state $\mathcal C'$ *advances* $\mathcal C$ with draw $W$ if $\mathrm{rank}(\mathcal C')<\mathrm{rank}(\mathcal C)$ and $U'=U\cup W$. The step map sends $(\mathcal C,W)$ to some state advancing $\mathcal C$ with $W$ if one exists, and to $\mathrm{acc}(\mathcal C,W)$ otherwise.
--
--   Feeding a sequence of random draws to the step map, starting from the initial state, every draw is retained in the collected set, even after a failed attempt, and a state of rank zero certifies through recovery that some full path of the original tree is covered by the union of the draws. Combined with a lower bound on the probability of advancing, this turns covering a probability tree by a random set into a completion problem for an adaptive process.
--
--   **Formalization Note** The objects are `ProbabilityTree.Recovers` (with `Recovers.refl`, `Recovers.mono`), `HasSpread.mono`, the structure `CoverState original σ`, and `CoverState.initial`, `rank` (with `rank_eq_zero_iff`), `accumulate` (with `accumulate_rank`), `Advances` and `step`. The step uses `Classical.choose`, and $\lfloor\log_2 l\rfloor$ is `Nat.log2`. The depth of a cover state is a field, so trees of different depths can occur along a run.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Covering a probability tree by iterative reductions

Recovery keeps the original and retained path histories distinct, even when
their labels agree. All draws are retained in the accumulating union.
-/

noncomputable section
open Classical

namespace LeanBlast.SecondKahnKalai

namespace ProbabilityTree

variable {X : Type} [DecidableEq X]

/-- Each path of a retained tree recovers a path of the original tree after
the already collected coordinates are added. -/
def Recovers {d e : ℕ} (T : ProbabilityTree X d) (S : ProbabilityTree X e)
    (W : Finset X) : Prop :=
  ∀ q : S.Path, ∃ p : T.Path, T.pathUnion p ⊆ W ∪ S.pathUnion q

theorem Recovers.refl {d : ℕ} (T : ProbabilityTree X d) : Recovers T T ∅ := by
  intro p
  exact ⟨p, by simp⟩

theorem Recovers.mono {d e : ℕ} {T : ProbabilityTree X d} {S : ProbabilityTree X e}
    {W V : Finset X} (h : Recovers T S W) (hWV : W ⊆ V) : Recovers T S V := by
  intro q
  obtain ⟨p, hp⟩ := h q
  exact ⟨p, hp.trans (Finset.union_subset_union hWV (Finset.Subset.refl _))⟩

/-- Increasing each nonnegative level spread parameter preserves spread. -/
theorem HasSpread.mono {d : ℕ} {T : ProbabilityTree X d} {a b : ℕ → ℝ}
    (hT : T.HasSpread a) (ha : ∀ i, i < d → 0 ≤ a i)
    (hab : ∀ i, i < d → a i ≤ b i) : T.HasSpread b := by
  induction T generalizing a b with
  | leaf => trivial
  | @node d B inst law positive label child ih =>
      constructor
      · intro J hJ
        exact (hT.1 J hJ).trans (pow_le_pow_left₀ (ha 0 (by omega)) (hab 0 (by omega)) _)
      · intro c
        exact ih c (hT.2 c) (fun i hi => ha (i + 1) (by omega))
          (fun i hi => hab (i + 1) (by omega))

/-- The actual retained tree, its spread budget, and recovery to the fixed
original tree. Only positive-capacity levels are stored. -/
structure CoverState {k : ℕ} (original : ProbabilityTree X k) (σ : ℝ) where
  depth : ℕ
  tree : ProbabilityTree X depth
  capacity : ℕ → ℕ
  disjoint : tree.IsDisjoint
  capacities : tree.HasCapacities capacity
  spread : tree.HasSpread (fun i => capacityReserve σ (capacity i))
  positive : ∀ i, i < depth → 0 < capacity i
  growth : ∀ i, i + 1 < depth → 16 * capacity i ≤ capacity (i + 1)
  seen : Finset X
  recovery : Recovers original tree seen

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

def initial (original : ProbabilityTree X k) (σ : ℝ) (m : ℕ → ℕ)
    (hσ : 0 < σ) (hdisjoint : original.IsDisjoint)
    (hcapacity : original.HasCapacities m)
    (hspread : original.HasSpread (fun _ => σ))
    (hpositive : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) : CoverState original σ :=
  { depth := k
    tree := original
    capacity := m
    disjoint := hdisjoint
    capacities := hcapacity
    spread := hspread.mono (fun _ _ => hσ.le) (fun i _ => capacityReserve_lower hσ.le (m i))
    positive := hpositive
    growth := hgrowth
    seen := ∅
    recovery := Recovers.refl original }

def rank (state : CoverState original σ) : ℕ :=
  if state.depth = 0 then 0 else successesNeeded (state.capacity (state.depth - 1))

@[simp] theorem rank_eq_zero_iff (state : CoverState original σ) :
    state.rank = 0 ↔ state.depth = 0 := by
  unfold rank
  split_ifs with h
  · simp [h]
  · simp [h, ne_of_gt (successesNeeded_pos _)]

/-- Every draw is retained even when the reduction attempt fails. -/
def accumulate (state : CoverState original σ) (W : Finset X) : CoverState original σ :=
  { state with
    seen := state.seen ∪ W
    recovery := state.recovery.mono Finset.subset_union_left }

@[simp] theorem accumulate_rank (state : CoverState original σ) (W : Finset X) :
    (state.accumulate W).rank = state.rank := rfl

def Advances (state : CoverState original σ) (W : Finset X)
    (next : CoverState original σ) : Prop :=
  next.rank < state.rank ∧ next.seen = state.seen ∪ W

/-- Choose a strict improvement when one exists; otherwise keep the tree.
Existence of improvements will be supplied by the actual good-tree reduction. -/
def step (state : CoverState original σ) (W : Finset X) : CoverState original σ :=
  if h : ∃ next, state.Advances W next then Classical.choose h else state.accumulate W

end CoverState

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI


