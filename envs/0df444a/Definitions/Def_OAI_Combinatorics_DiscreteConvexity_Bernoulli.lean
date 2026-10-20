-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
-- name    : OAI_Combinatorics_DiscreteConvexity_Bernoulli
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:36:46.195415+00:00
-- url     : https://prove2.me/theorems/aa90addb-e881-4e88-83a9-dbd444f20bd5
-- title:
--   Bernoulli bits, product measures on the cube and random subsets
-- statement:
--   Let $X$ be finite and $p\in\mathbb{R}$.
--
--   1. **Bits.** A bit has mass $p$ at $1$ and $1-p$ at $0$. For $0\le p\le1$ this is a finite law with $\Pr(1)=p$ and $\Pr(0)=1-p$.
--   2. **Cube and subsets.** The product mass of $x\in\{0,1\}^X$ is $\prod_i(\text{mass of }x_i)$. For a subset $S\subseteq X$,
--   $$
--   \beta_p(S)=\prod_{i\in X}\begin{cases}p,&i\in S,\\1-p,&i\notin S,\end{cases}
--   $$
--      with the corresponding expectation and probability over subsets.
--   3. **Identities.** Subsets correspond bijectively to Boolean vectors, and the masses agree. Expectations of product functions factor:
--   $$
--   \sum_{W\subseteq X}\beta_p(W)\prod_{x\in X}f_x([x\in W])=\prod_{x\in X}\bigl(pf_x(1)+(1-p)f_x(0)\bigr).
--   $$
--      In particular $\sum_W\beta_p(W)=1$, and for $0\le p\le1$ the weights are nonnegative and form the Bernoulli law on subsets.
--
--   The algebraic identities hold for every real $p$, which is used for signed alternating corrections.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/Bernoulli.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Bernoulli.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandDiscreteConvexity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Bernoulli product laws and Boolean cubes

The algebraic identities hold for every real parameter. Nonnegative normalized
laws additionally require a parameter in the closed unit interval.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

/-- The mass of a Bernoulli bit. -/
def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

@[simp] theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl
@[simp] theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl

theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b
  · exact sub_nonneg.mpr hp1
  · exact hp0

def bitLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw Bool where
  weight := bitWeight p
  nonneg := bitWeight_nonneg hp0 hp1
  total := by simp [bitWeight]

@[simp] theorem bitLaw_weight (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    (bitLaw p hp0 hp1).weight b = bitWeight p b := rfl

@[simp] theorem bitLaw_prob_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitLaw p hp0 hp1).prob (fun b => b = true) = p := by
  simp [FiniteLaw.prob, bitLaw, bitWeight]

@[simp] theorem bitLaw_prob_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitLaw p hp0 hp1).prob (fun b => b = false) = 1 - p := by
  simp [FiniteLaw.prob, bitLaw, bitWeight]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Product mass on the Boolean cube, including signed parameters. -/
def cubeWeight (p : ℝ) (x : α → Bool) : ℝ := ∏ i, bitWeight p (x i)

def cubeExpectation (p : ℝ) (f : (α → Bool) → ℝ) : ℝ :=
  ∑ x, cubeWeight p x * f x

def bernoulliWeight (p : ℝ) (s : Finset α) : ℝ :=
  ∏ i, if i ∈ s then p else 1 - p

def bernoulliExpectation (p : ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ s, bernoulliWeight p s * f s

def bernoulliProbability (p : ℝ) (P : Finset α → Prop) : ℝ :=
  ∑ s, if P s then bernoulliWeight p s else 0

def finsetBoolEquiv : Finset α ≃ (α → Bool) where
  toFun W x := decide (x ∈ W)
  invFun b := Finset.univ.filter fun x => b x = true
  left_inv W := by ext x; simp
  right_inv b := by
    funext x
    cases hb : b x <;> simp [hb]

theorem sum_finset_product (f : α → Bool → ℝ) :
    (∑ W : Finset α, ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (f x true + f x false) := by
  calc
    (∑ W : Finset α, ∏ x, f x (decide (x ∈ W))) =
        ∑ b : α → Bool, ∏ x, f x (b x) :=
      (finsetBoolEquiv (α := α)).sum_comp (fun b => ∏ x, f x (b x))
    _ = _ := by rw [← Fintype.prod_sum f]; simp only [Fintype.sum_bool]

theorem bernoulliExpectation_product (p : ℝ) (f : α → Bool → ℝ) :
    bernoulliExpectation p (fun W => ∏ x, f x (decide (x ∈ W))) =
      ∏ x, (p * f x true + (1 - p) * f x false) := by
  unfold bernoulliExpectation bernoulliWeight
  simp_rw [← Finset.prod_mul_distrib]
  simpa using sum_finset_product (fun x b => (if b then p else 1 - p) * f x b)

theorem bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset α) :
    0 ≤ bernoulliWeight p W := by
  apply Finset.prod_nonneg
  intro x _
  split_ifs <;> linarith

theorem bernoulliWeight_sum (p : ℝ) : ∑ W : Finset α, bernoulliWeight p W = 1 := by
  have hp : p + (1 - p) = 1 := by ring
  simpa [bernoulliExpectation, hp] using
    bernoulliExpectation_product p (fun (_ : α) (_ : Bool) => 1)

def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (Finset α) where
  weight := bernoulliWeight p
  nonneg := bernoulliWeight_nonneg hp0 hp1
  total := bernoulliWeight_sum p

@[simp] theorem bernoulliLaw_weight (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset α) :
    (bernoulliLaw p hp0 hp1).weight W = bernoulliWeight p W := rfl

@[simp] theorem bernoulliLaw_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Finset α → ℝ) :
    (bernoulliLaw p hp0 hp1).expectation f = bernoulliExpectation p f := rfl

@[simp] theorem bernoulliLaw_prob (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset α → Prop) : (bernoulliLaw p hp0 hp1).prob P = bernoulliProbability p P := rfl

@[simp] theorem cubeSet_finsetBoolEquiv (s : Finset α) :
    cubeSet (finsetBoolEquiv s) = s := cubeSet_decide s

@[simp] theorem cubeWeight_finsetBoolEquiv (p : ℝ) (s : Finset α) :
    cubeWeight p (finsetBoolEquiv s) = bernoulliWeight p s := by
  simp [cubeWeight, bitWeight, finsetBoolEquiv, bernoulliWeight]

end TalagrandDiscreteConvexity

end

end OAI


