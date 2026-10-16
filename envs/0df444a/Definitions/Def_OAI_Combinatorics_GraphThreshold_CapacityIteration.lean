-- Prove2me | Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
-- name    : OAI_Combinatorics_GraphThreshold_CapacityIteration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:28:27.735075+00:00
-- url     : https://prove2.me/theorems/34330891-6540-489a-b482-66db792916bc
-- title:
--   Halving capacities, spread inflation and the retention bound $\prod_{m\in S}(1-e^{-m})\ge 1/3$
-- statement:
--   This file collects the arithmetic of capacities that are halved at each successful reduction step, together with finite product estimates for the corresponding inflation of a spread parameter. Throughout, $l,t,m$ are natural numbers and $\sigma$ is a real number.
--
--   1. **Reduced capacity.** $\mathrm{red}(l,t)=\lfloor l/2^{t}\rfloor$, the capacity after $t$ halvings of $l$; in particular $\mathrm{red}(l,0)=l$.
--   2. **Number of successes needed.** $\mathrm{succ}(l)=\lfloor\log_2 l\rfloor+1$ for $l\ge1$, and $\mathrm{succ}(0)=1$; always $\mathrm{succ}(l)\ge1$. For $l\ge1$ this is the least $t$ with $\lfloor l/2^{t}\rfloor=0$.
--   3. **Iterated spread.** The spread parameter after $t$ reductions, each of which inflates it by the reciprocal of the retention factor at the current capacity:
--   $$\mathrm{spr}(\sigma,l,t)=\sigma\prod_{u=0}^{t-1}\Big(1-e^{-\lfloor l/2^{u}\rfloor}\Big)^{-1},\qquad \mathrm{spr}(\sigma,l,0)=\sigma .$$
--   4. **Capacity reserve.** A history-free allowance for the spread parameter at capacity $m$:
--   $$\mathrm{res}(\sigma,m)=4\sigma\prod_{j=1}^{m}\big(1-e^{-j}\big),\qquad \mathrm{res}(\sigma,0)=4\sigma .$$
--
--   The file also contains the elementary estimates behind these quantities: for a finite set $S$ of positive integers and $0\le q<1$, $\sum_{m\in S}q^{m}\le q/(1-q)$; for a finite family of reals with $0\le f_i\le1$, $1-\sum_i f_i\le\prod_i(1-f_i)$; $e^{-1}\le 2/5$; and consequently, for every finite set $S$ of positive integers,
--   $$\sum_{m\in S}e^{-m}\le\frac23,\qquad \prod_{m\in S}\big(1-e^{-m}\big)\ge\frac13 .$$
--   In particular $\sigma\le\mathrm{res}(\sigma,m)$ for every $m$ whenever $\sigma\ge0$.
--
--   These bounds show that repeatedly halving a positive capacity and paying the factor $(1-e^{-m})^{-1}$ at each capacity $m$ along the way multiplies a spread parameter by at most a fixed constant, which is what makes a reduction scheme with halving capacities affordable.
--
--   **Formalization Note** $\lfloor l/2^{t}\rfloor$ is natural-number division (`reducedCapacity`), and $\lfloor\log_2 l\rfloor$ is `Nat.log2`, which returns $0$ at $l=0$ (`successesNeeded`). In `iteratedSpread` the inverse is Lean's field inverse, so a factor with $\lfloor l/2^{u}\rfloor=0$ equals $0^{-1}=0$; the formula is meaningful only while all reduced capacities $\lfloor l/2^{u}\rfloor$, $u<t$, are positive. The reserve is `capacityReserve` and its lower bound is `capacityReserve_lower`. All sums and products are finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/CapacityIteration.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/CapacityIteration.lean by skeleton subtraction
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

-- Lean 4.34 name of Finset.prod_le_prod_of_subset_of_le_one (ordered-semiring version) in Mathlib 0df444a.
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Capacities and finite inflation products

The capacity after `t` successful reductions is natural-number division by
`2^t`. All product estimates below are finite; no infinite product is used.
-/

noncomputable section

open Finset Set

namespace LeanBlast.SecondKahnKalai

def reducedCapacity (l t : ℕ) : ℕ := l / 2 ^ t

def successesNeeded (l : ℕ) : ℕ := Nat.log2 l + 1

@[simp] theorem reducedCapacity_zero (l : ℕ) : reducedCapacity l 0 = l := by
  simp [reducedCapacity]

theorem successesNeeded_pos (l : ℕ) : 0 < successesNeeded l := by
  exact Nat.succ_pos _

/-- A finite sum of distinct positive geometric powers. -/
theorem sum_positive_geometric_le (s : Finset ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∑ m ∈ s, q ^ m) ≤ q / (1 - q) := by
  obtain ⟨N, hN⟩ := s.exists_nat_subset_range
  calc
    (∑ m ∈ s, q ^ m) ≤ ∑ m ∈ Finset.Ico 1 N, q ^ m := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Ico.mpr ⟨hpos m hm, mem_range.mp (hN hm)⟩
      · intro m _ _
        exact pow_nonneg hq _
    _ ≤ q / (1 - q) := by
      simpa only [pow_one] using geom_sum_Ico_le_of_lt_one (m := 1) (n := N) hq hq1

/-- Elementary finite product bound, applied below to the retention factors. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - (∑ i ∈ s, f i) ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have h0i := h0 i (mem_insert_self _ _)
      have h1i := h1 i (mem_insert_self _ _)
      have h0s : ∀ j ∈ s, 0 ≤ f j := fun j hj => h0 j (mem_insert_of_mem hj)
      have h1s : ∀ j ∈ s, f j ≤ 1 := fun j hj => h1 j (mem_insert_of_mem hj)
      have hp := mul_le_mul_of_nonneg_left (ih h0s h1s) (sub_nonneg.mpr h1i)
      have hs := sum_nonneg h0s
      rw [sum_insert hi, prod_insert hi]
      nlinarith [mul_nonneg h0i hs]

theorem exp_neg_one_le_two_fifths : Real.exp (-1) ≤ (2 / 5 : ℝ) := by
  have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    norm_num at h
    exact h
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 1)).mpr
  nlinarith

theorem sum_exp_neg_capacities_le_two_thirds (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (∑ m ∈ s, Real.exp (-(m : ℝ))) ≤ (2 / 3 : ℝ) := by
  have hq0 := (Real.exp_pos (-1)).le
  have hq1 : Real.exp (-1) < 1 := lt_of_le_of_lt exp_neg_one_le_two_fifths (by norm_num)
  have heq (m : ℕ) : Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
    simpa only [mul_neg_one] using Real.exp_nat_mul (-1) m
  simp_rw [heq]
  apply (sum_positive_geometric_le s hq0 hq1 hpos).trans
  apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith [exp_neg_one_le_two_fifths]

theorem finite_retentionProduct_ge_one_third (s : Finset ℕ)
    (hpos : ∀ m ∈ s, 1 ≤ m) :
    (1 / 3 : ℝ) ≤ ∏ m ∈ s, (1 - Real.exp (-(m : ℝ))) := by
  have h0 (m : ℕ) (_ : m ∈ s) : 0 ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
  have h1 (m : ℕ) (_ : m ∈ s) : Real.exp (-(m : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg m)
  have hb := one_sub_sum_le_prod_one_sub s (fun m => Real.exp (-(m : ℝ))) h0 h1
  have hs := sum_exp_neg_capacities_le_two_thirds s hpos
  linarith

def iteratedSpread (σ : ℝ) (l t : ℕ) : ℝ :=
  σ * ∏ u ∈ range t, (1 - Real.exp (-(reducedCapacity l u : ℝ)))⁻¹

@[simp] theorem iteratedSpread_zero (σ : ℝ) (l : ℕ) : iteratedSpread σ l 0 = σ := by
  simp [iteratedSpread]

/-- A history-free allowance for the spread parameter at capacity `m`. -/
def capacityReserve (σ : ℝ) (m : ℕ) : ℝ :=
  4 * σ * ∏ j ∈ Finset.Icc 1 m, (1 - Real.exp (-(j : ℝ)))

@[simp] theorem capacityReserve_zero (σ : ℝ) : capacityReserve σ 0 = 4 * σ := by
  simp [capacityReserve]

theorem capacityReserve_lower {σ : ℝ} (hσ : 0 ≤ σ) (m : ℕ) :
    σ ≤ capacityReserve σ m := by
  have hp := finite_retentionProduct_ge_one_third (Finset.Icc 1 m)
    (fun j hj => (Finset.mem_Icc.mp hj).1)
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hσ)
  unfold capacityReserve
  nlinarith

end LeanBlast.SecondKahnKalai

end

end OAI


