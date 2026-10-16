-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
-- name    : OAI_Combinatorics_GraphThreshold_TreeReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:34:28.2047+00:00
-- url     : https://prove2.me/theorems/b212331a-a7c0-4a8b-9cff-cd1e3ed04796
-- title:
--   Pruning a good probability tree to its successful targets and renormalizing
-- statement:
--   **Retained laws.** Let $B$ be a finite set, $w:B\to\mathbb{R}$ a weight function and $G$ a predicate on $B$.
--
--   1. The *retained mass* is $M(w,G)=\sum_{b\in B:\ G(b)}w(b)$, and the *retained index set* is $R(w,G)=\{b\in B:\ G(b)\text{ and }w(b)>0\}$. If $w\ge0$, then for every $f:B\to\mathbb{R}$
--   $$\sum_{b\in R(w,G)}w(b)\,f(b)=\sum_{b\in B:\ G(b)}w(b)\,f(b),$$
--   and in particular $\sum_{b\in R(w,G)}w(b)=M(w,G)$.
--   2. If $w\ge0$ and $M(w,G)>0$, the *retained law* is the probability law $b\mapsto w(b)/M(w,G)$ on $R(w,G)$; it is strictly positive.
--
--   **Tree reduction.** Let $X$ be a type with decidable equality. An equal-depth probability tree over $X$ is either a leaf (depth $0$) or a node of depth $d+1$ with a finite index set $B$, a strictly positive law $\mu$ on $B$, finite labels $A_b\subseteq X$ and child trees $T_b$ of depth $d$. Fix $\rho\in\mathbb{R}$, a finite $W\subseteq X$ and capacities $m=(m_0,m_1,\dots)$. At a node, the planted resampling transition has weights
--   $$P_W(c,b)=\mu(c)\,\frac{\mathbf 1[A_b\subseteq W\cup A_c]\,\mu(b)\,\rho^{-|A_b|}}{Z(W\cup A_c)},\qquad Z(Y)=\sum_{b:\ A_b\subseteq Y}\mu(b)\,\rho^{-|A_b|};$$
--   $(c,b)$ is a local success at capacity $m_0$ if $e^{-10m_0}\le Z(W\cup A_c)$ and $|A_b\setminus W|\le\lfloor m_0/2\rfloor$, and the successful target mass is $s_W(b)=\sum_{c}\mathbf 1[(c,b)\text{ local success}]\,P_W(c,b)$. A leaf is good, and a node is good for $(\rho,m,W)$ if $1-e^{-m_0}\le\sum_{b:\ T_b\text{ good for }(\rho,(m_1,m_2,\dots),W)}s_W(b)$.
--
--   3. For every natural number $k>0$, $1-e^{-k}>0$; consequently, if $m_0>0$ and a node is good, the retained mass of $s_W$ over the indices $b$ with $T_b$ good is strictly positive.
--   4. **The reduced tree.** Assume $\rho>0$, $m_j>0$ for every level $j<d$, and $T$ (of depth $d$) is good for $(\rho,m,W)$. The reduced tree $\mathrm{red}(T)$ has the same depth $d$ and is defined recursively: a leaf stays a leaf, and a node $(B,\mu,A,(T_b))$ becomes the node whose
--      - index set is $R=\{b\in B:\ T_b\text{ good for }(\rho,(m_1,m_2,\dots),W)\text{ and }s_W(b)>0\}$,
--      - law is the retained law $b\mapsto s_W(b)\big/\sum_{b'\in R}s_W(b')$,
--      - label at $b\in R$ is the fragment $A_b\setminus W$,
--      - child at $b\in R$ is $\mathrm{red}(T_b)$, computed with the same $\rho$ and $W$ and the shifted capacities $(m_1,m_2,\dots)$.
--
--   Every retained label is the actual fragment of its original label, and every index with zero successful mass is removed, so the new laws are again strictly positive. This is one round of the simultaneous tree reduction, with one set $W$ used at all nodes. In the same development it is shown that $\mathrm{red}(T)$ has capacities $(\lfloor m_j/2\rfloor)_j$, is disjoint whenever $T$ is, has spread $\big(a_j/(1-e^{-m_j})\big)_j$ whenever $T$ has spread $a$ with $a_j\ge0$, and that every full path of $\mathrm{red}(T)$, together with $W$, contains the label union of a full path of $T$.
--
--   **Formalization Note** The objects are `retainedMass`, `RetainedIndex` (a subtype), `retainedLaw`, `retainedLaw_positive`, `sum_retained`, `sum_retained_weights`, `one_sub_exp_neg_nat_pos`, `good_retainedMass_pos` and `reduceTree`; the last takes proofs of $\rho>0$, of positivity of the capacities below depth $d$, and of goodness, and is defined by structural recursion on the tree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeReduction.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Classical

noncomputable section

namespace LeanBlast.SecondKahnKalai

section RetainedLaw

variable {B X : Type*} [Fintype B] [DecidableEq X]

def retainedMass (w : B → ℝ) (G : B → Prop) : ℝ :=
  ∑ b, if G b then w b else 0

abbrev RetainedIndex (w : B → ℝ) (G : B → Prop) := {b : B // G b ∧ 0 < w b}

theorem sum_retained (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b) (f : B → ℝ) :
    (∑ b : RetainedIndex w G, w b * f b) = ∑ b, if G b then w b * f b else 0 := by
  symm
  apply Finset.sum_congr_set {b | G b ∧ 0 < w b}
  · intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    simp [hb.1]
  · intro b hb
    by_cases hg : G b
    · have hnot : ¬ 0 < w b := fun hpos => hb ⟨hg, hpos⟩
      have hz : w b = 0 := le_antisymm (le_of_not_gt hnot) (hw b)
      simp [hg, hz]
    · simp [hg]

theorem sum_retained_weights (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : RetainedIndex w G, w b) = retainedMass w G := by
  simpa only [mul_one, retainedMass] using sum_retained w G hw (fun _ => 1)

/-- The actual normalized child law, after removing all zero-mass targets. -/
def retainedLaw (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) : FiniteLaw (RetainedIndex w G) where
  weight b := w b / retainedMass w G
  nonneg b := div_nonneg (hw b) hpos.le
  total := by
    rw [← Finset.sum_div, sum_retained_weights w G hw]
    exact div_self hpos.ne'

theorem retainedLaw_positive (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) : (retainedLaw w G hw hpos).IsPositive := by
  intro b
  exact div_pos b.property.2 hpos

end RetainedLaw

section Construction

variable {X : Type} [DecidableEq X]

theorem one_sub_exp_neg_nat_pos {m : ℕ} (hm : 0 < m) :
    0 < 1 - Real.exp (-(m : ℝ)) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hm'))

theorem good_retainedMass_pos {d : ℕ} {B : Type} [Fintype B]
    (μ : FiniteLaw B) (hμ : μ.IsPositive) (A : B → Finset X)
    (child : B → ProbabilityTree X d) (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X)
    (hm : 0 < m 0) (hg : Good ρ m W (.node B μ hμ A child)) :
    0 < retainedMass (successfulTargetMass μ A ρ (m 0) W)
      (fun b => Good ρ (fun j => m (j + 1)) W (child b)) := by
  apply lt_of_lt_of_le (one_sub_exp_neg_nat_pos hm)
  simpa only [Good, retainedMass] using hg

/-- Explicit good-node pruning and normalization. The depth is preserved in the
result type. Every retained label is the actual fragment of its original label. -/
def reduceTree (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) : ProbabilityTree X d :=
  match T with
  | .leaf => .leaf
  | @ProbabilityTree.node _ n _B _inst μ hμ A child =>
      let w := successfulTargetMass μ A ρ (m 0) W
      let G := fun b => Good ρ (fun j => m (j + 1)) W (child b)
      have hw : ∀ b, 0 ≤ w b := successfulTargetMass_nonneg μ A hρ.le (m 0) W
      have hp : 0 < retainedMass w G :=
        good_retainedMass_pos μ hμ A child ρ m W (hm 0 (Nat.succ_pos _)) hg
      .node (RetainedIndex w G) (retainedLaw w G hw hp)
        (retainedLaw_positive w G hw hp) (fun b => A b.val \ W)
        (fun b => reduceTree ρ (fun j => m (j + 1)) W (child b.val) hρ
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1)
termination_by structural T

end Construction

end LeanBlast.SecondKahnKalai

end

end OAI


