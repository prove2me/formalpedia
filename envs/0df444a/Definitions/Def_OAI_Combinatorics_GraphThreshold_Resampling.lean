-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
-- name    : OAI_Combinatorics_GraphThreshold_Resampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:29:18.541753+00:00
-- url     : https://prove2.me/theorems/742942cf-0c9d-4333-9d7b-9475c5384694
-- title:
--   The planted resampling transition: normalizing density and source–target law
-- statement:
--   Let $X$ be a type with decidable equality (all subsets of $X$ below are finite), $B$ a finite index set, $\nu$ a finite law on $B$ (weights $\nu(b)\ge0$ with $\sum_{b}\nu(b)=1$), $(A_b)_{b\in B}$ a family of finite labels $A_b\subseteq X$, $\rho$ a real parameter and $W\subseteq X$ a finite set. The file defines a two-step transition from a *source* index $c$ to a *target* index $b$.
--
--   1. **Observed set.** $Y(W,c)=W\cup A_c$.
--   2. **Numerator and normalizing density.** For a finite set $Y\subseteq X$,
--   $$N_Y(b)=\begin{cases}\nu(b)\,\rho^{-|A_b|}, & A_b\subseteq Y,\\ 0, & \text{otherwise},\end{cases}\qquad Z(Y)=\sum_{b\in B}N_Y(b).$$
--   3. **Target weight.** $\tau_W(c,b)=N_{Y(W,c)}(b)\,/\,Z\big(Y(W,c)\big)$: given the source $c$, the target $b$ is chosen with probability proportional to $\nu(b)\rho^{-|A_b|}$ among the indices whose label lies inside the observed set $W\cup A_c$.
--   4. **Joint weight and resampling law.** $P_W(c,b)=\nu(c)\,\tau_W(c,b)$ on $B\times B$. If $\nu$ is strictly positive ($\nu(b)>0$ for all $b$) and $\rho>0$, then $P_W$ is a probability law on $B\times B$, the *resampling law*.
--   5. **Fragment.** The retained part of a target label is $A_b\setminus W$.
--
--   The accompanying facts are: $N_Y(b)\ge0$ and $Z(Y)\ge0$ whenever $\rho\ge0$; and if $\nu$ is strictly positive and $\rho>0$, then $Z(W\cup A_c)>0$ for every $c$, $\sum_{b}\tau_W(c,b)=1$, the source marginal is exact,
--   $$\sum_{b\in B}P_W(c,b)=\nu(c)\qquad\text{for every }c\in B,$$
--   and hence $\sum_{(c,b)\in B\times B}P_W(c,b)=1$.
--
--   Interpretation: if $X$ is finite, $0<\rho\le1$, $W$ is a $\rho$-random subset of $X$ (each element included independently with probability $\rho$) and $c$ is drawn from $\nu$ independently, then $Z$ is the density of the law of $W\cup A_c$ with respect to the law of a $\rho$-random subset, and $\tau_W(c,\cdot)$ is the conditional law of the planted index given the observed set $W\cup A_c$. Replacing the planted label $A_c$ by a resampled label $A_b$ and keeping only its fragment $A_b\setminus W$ is the basic move of the tree reduction in this development.
--
--   **Formalization Note** The definitions `resamplingY`, `resamplingNumerator`, `resamplingZ`, `resamplingTargetWeight`, `resamplingWeight` and `resamplingFragment` are total: for $\rho=0$ Lean's inverse gives $0^{-1}=0$, and division by $Z=0$ returns $0$. The law `resamplingLaw` takes proofs that $\nu$ is strictly positive and that $\rho>0$. The private lemma `ite_eq_left` is a rewriting helper.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Resampling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Resampling.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

def resamplingY (A : B → Finset X) (W : Finset X) (c : B) : Finset X := W ∪ A c

def resamplingNumerator (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (Y : Finset X) (b : B) : ℝ :=
  if A b ⊆ Y then ν.weight b * (ρ⁻¹) ^ (A b).card else 0

/-- The actual normalizing density `Z(Y)`. -/
def resamplingZ (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (Y : Finset X) : ℝ :=
  ∑ b, resamplingNumerator ν A ρ Y b

def resamplingTargetWeight (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (c b : B) : ℝ :=
  resamplingNumerator ν A ρ (resamplingY A W c) b /
    resamplingZ ν A ρ (resamplingY A W c)

def resamplingWeight (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (cb : B × B) : ℝ :=
  ν.weight cb.1 * resamplingTargetWeight ν A ρ W cb.1 cb.2

/-- The retained target fragment; no quotienting of the label indices occurs. -/
def resamplingFragment (A : B → Finset X) (W : Finset X) (b : B) : Finset X :=
  A b \ W

theorem resamplingNumerator_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (Y : Finset X) (b : B) :
    0 ≤ resamplingNumerator ν A ρ Y b := by
  unfold resamplingNumerator
  split_ifs
  · exact mul_nonneg (ν.nonneg b) (pow_nonneg (inv_nonneg.mpr hρ) _)
  · exact le_rfl

theorem resamplingZ_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (Y : Finset X) : 0 ≤ resamplingZ ν A ρ Y := by
  exact Finset.sum_nonneg fun b _ => resamplingNumerator_nonneg ν A hρ Y b

theorem resamplingZ_pos (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (c : B) :
    0 < resamplingZ ν A ρ (resamplingY A W c) := by
  classical
  have hc : 0 < resamplingNumerator ν A ρ (resamplingY A W c) c := by
    rw [resamplingNumerator, resamplingY, ite_eq_left Finset.subset_union_right]
    exact mul_pos (hν c) (pow_pos (inv_pos.mpr hρ) _)
  exact lt_of_lt_of_le hc (Finset.single_le_sum
    (fun b _ => resamplingNumerator_nonneg ν A hρ.le (resamplingY A W c) b)
    (Finset.mem_univ c))

theorem resamplingTargetWeight_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (W : Finset X) (c b : B) :
    0 ≤ resamplingTargetWeight ν A ρ W c b :=
  div_nonneg (resamplingNumerator_nonneg ν A hρ _ _)
    (resamplingZ_nonneg ν A hρ _)

theorem resamplingWeight_nonneg (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (W : Finset X) (cb : B × B) :
    0 ≤ resamplingWeight ν A ρ W cb :=
  mul_nonneg (ν.nonneg _) (resamplingTargetWeight_nonneg ν A hρ W _ _)

theorem resamplingTargetWeight_total (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (c : B) :
    (∑ b, resamplingTargetWeight ν A ρ W c b) = 1 := by
  simp only [resamplingTargetWeight, ← Finset.sum_div]
  exact div_self (resamplingZ_pos ν A hν hρ W c).ne'

theorem resampling_source_marginal (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (c : B) :
    (∑ b, resamplingWeight ν A ρ W (c, b)) = ν.weight c := by
  simp only [resamplingWeight, ← Finset.mul_sum,
    resamplingTargetWeight_total ν A hν hρ W c, mul_one]

theorem resamplingWeight_total (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) :
    (∑ cb : B × B, resamplingWeight ν A ρ W cb) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [resampling_source_marginal ν A hν hρ W]
  exact ν.total

def resamplingLaw (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (hν : ν.IsPositive) (hρ : 0 < ρ) : FiniteLaw (B × B) where
  weight := resamplingWeight ν A ρ W
  nonneg := resamplingWeight_nonneg ν A hρ.le W
  total := resamplingWeight_total ν A hν hρ W

@[simp] theorem resamplingLaw_weight (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ)
    (W : Finset X) (hν : ν.IsPositive) (hρ : 0 < ρ) (cb : B × B) :
    (resamplingLaw ν A ρ W hν hρ).weight cb = resamplingWeight ν A ρ W cb := rfl

end LeanBlast.SecondKahnKalai

end

end OAI


