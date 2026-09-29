-- Prove2me | solution 1 for AGT.nash_existence
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T00:05:48.493137+00:00
-- url     : https://prove2.me/submissions/d89aadbf-57d9-4032-a8a8-ba16c497870c

import Definitions.Def_agt_games
import Theorems.Thm_AGT_brouwer_fixed_point
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Nash's theorem from Brouwer's fixed-point theorem

A reduction of `AGT.nash_existence` to `AGT.brouwer_fixed_point` through the
Nash map on the product of the players' simplices.
-/

namespace NashProof

open Finset AGT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]

open scoped Classical in
/-- The pure strategy `a`, viewed as a lottery. -/
noncomputable def pureStrat {α : Type*} (a : α) : α → ℝ :=
  fun b => if b = a then 1 else 0

lemma isLottery_pureStrat {α : Type*} [Fintype α] (a : α) : IsLottery (pureStrat a) := by
  classical
  constructor
  · intro b
    by_cases h : b = a <;> simp [pureStrat, h]
  · simp [pureStrat]

/-- Expected payoff of player `i` after `i` deviates to the weight function `τ`,
written as a sum over pure profiles with the other players' weights factored out. -/
lemma expectedPayoff_update (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ)
    (i : ι) (τ : S i → ℝ) :
    expectedPayoff u (Function.update σ i τ) i
      = ∑ s : ∀ j, S j, τ (s i) * ((∏ j ∈ univ.erase i, σ j (s j)) * u i s) := by
  classical
  unfold expectedPayoff profileProb
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : ∏ j, (Function.update σ i τ) j (s j)
      = τ (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
    rw [← Finset.mul_prod_erase univ (fun j => (Function.update σ i τ) j (s j))
      (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h, mul_assoc]

/-- Player `i`'s expected payoff is linear in `i`'s own mixed strategy. -/
lemma expectedPayoff_update_linear (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ)
    (i : ι) (τ : S i → ℝ) :
    expectedPayoff u (Function.update σ i τ) i
      = ∑ a : S i, τ a * expectedPayoff u (Function.update σ i (pureStrat a)) i := by
  classical
  rw [expectedPayoff_update]
  have hpure : ∀ a : S i, expectedPayoff u (Function.update σ i (pureStrat a)) i
      = ∑ s : ∀ j, S j, (if s i = a then (1:ℝ) else 0)
          * ((∏ j ∈ univ.erase i, σ j (s j)) * u i s) := by
    intro a
    rw [expectedPayoff_update]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [pureStrat]
  simp_rw [hpure, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [ite_mul, mul_ite]

/-- The set of mixed profiles. -/
def mixedSet (S : ι → Type*) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  {σ | IsMixedProfile σ}

omit [Fintype ι] [DecidableEq ι] in
lemma convex_mixedSet : Convex ℝ (mixedSet S) := by
  intro σ hσ ρ hρ a b ha hb hab i
  constructor
  · intro x
    have h1 := (hσ i).1 x
    have h2 := (hρ i).1 x
    have : (a • σ + b • ρ) i x = a * σ i x + b * ρ i x := rfl
    rw [this]
    nlinarith
  · have : ∀ x, (a • σ + b • ρ) i x = a * σ i x + b * ρ i x := fun x => rfl
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hσ i).2, (hρ i).2,
      mul_one, mul_one, hab]

omit [Fintype ι] [DecidableEq ι] in
lemma isClosed_mixedSet : IsClosed (mixedSet S) := by
  have h : mixedSet S = (⋂ (i : ι) (a : S i), {σ : ∀ i, S i → ℝ | 0 ≤ σ i a}) ∩
      (⋂ i : ι, {σ : ∀ i, S i → ℝ | ∑ a, σ i a = 1}) := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, mixedSet,
      IsMixedProfile, IsLottery]
    constructor
    · intro h
      exact ⟨fun i a => (h i).1 a, fun i => (h i).2⟩
    · intro h i
      exact ⟨fun a => h.1 i a, h.2 i⟩
  rw [h]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_iInter fun i => isClosed_iInter fun a => ?_
    exact isClosed_le continuous_const ((continuous_apply a).comp (continuous_apply i))
  · refine isClosed_iInter fun i => ?_
    exact isClosed_eq (continuous_finsetSum _ fun a _ =>
      (continuous_apply a).comp (continuous_apply i)) continuous_const

omit [DecidableEq ι] in
lemma isBounded_mixedSet : Bornology.IsBounded (mixedSet S) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun σ hσ => ?_⟩
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  have hnn : 0 ≤ σ i a := (hσ i).1 a
  have hle : σ i a ≤ 1 := by
    rw [← (hσ i).2]
    exact Finset.single_le_sum (fun b _ => (hσ i).1 b) (Finset.mem_univ a)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

omit [DecidableEq ι] in
lemma isCompact_mixedSet : IsCompact (mixedSet S) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_mixedSet isBounded_mixedSet

omit [Fintype ι] [DecidableEq ι] in
lemma nonempty_mixedSet [∀ i, Nonempty (S i)] : (mixedSet S).Nonempty := by
  classical
  refine ⟨fun i => pureStrat (Classical.arbitrary (S i)), fun i => ?_⟩
  exact isLottery_pureStrat _

/-- The gain from deviating to the pure strategy `a`, truncated at zero. -/
noncomputable def gain (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι) (a : S i) : ℝ :=
  max 0 (expectedPayoff u (Function.update σ i (pureStrat a)) i - expectedPayoff u σ i)

/-- The Nash map. -/
noncomputable def nashMap (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i a => (σ i a + gain u σ i a) / (1 + ∑ b, gain u σ i b)

lemma gain_nonneg (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι) (a : S i) :
    0 ≤ gain u σ i a := le_max_left _ _

lemma one_le_denom (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ) (i : ι) :
    (1 : ℝ) ≤ 1 + ∑ b, gain u σ i b := by
  have : (0:ℝ) ≤ ∑ b, gain u σ i b :=
    Finset.sum_nonneg fun b _ => gain_nonneg u σ i b
  linarith

lemma continuous_expectedPayoff (u : ι → (∀ i, S i) → ℝ) (i : ι) :
    Continuous fun σ : (∀ j, S j → ℝ) => expectedPayoff u σ i := by
  unfold expectedPayoff profileProb
  refine continuous_finsetSum _ fun s _ => ?_
  exact (continuous_finsetProd _ fun j _ =>
    (continuous_apply (s j)).comp (continuous_apply j)).mul continuous_const

omit [Fintype ι] [∀ i, Fintype (S i)] in
lemma continuous_update_left (i : ι) (τ : S i → ℝ) :
    Continuous fun σ : (∀ j, S j → ℝ) => Function.update σ i τ := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact continuous_const
  · simp only [Function.update_of_ne h]
    exact continuous_apply j

lemma continuous_gain (u : ι → (∀ i, S i) → ℝ) (i : ι) (a : S i) :
    Continuous fun σ : (∀ j, S j → ℝ) => gain u σ i a := by
  unfold gain
  exact continuous_const.max
    (((continuous_expectedPayoff u i).comp (continuous_update_left i (pureStrat a))).sub
      (continuous_expectedPayoff u i))

lemma continuous_nashMap (u : ι → (∀ i, S i) → ℝ) :
    Continuous (nashMap u (S := S)) := by
  refine continuous_pi fun i => continuous_pi fun a => ?_
  have hden : Continuous fun σ : (∀ j, S j → ℝ) => 1 + ∑ b, gain u σ i b :=
    continuous_const.add (continuous_finsetSum _ fun b _ => continuous_gain u i b)
  have hcoord : Continuous fun σ : (∀ j, S j → ℝ) => σ i a :=
    (continuous_apply a).comp (continuous_apply i)
  have hnum : Continuous fun σ : (∀ j, S j → ℝ) => σ i a + gain u σ i a :=
    hcoord.add (continuous_gain u i a)
  exact hnum.div hden fun σ => by have := one_le_denom u σ i; linarith

lemma mapsTo_nashMap (u : ι → (∀ i, S i) → ℝ) :
    Set.MapsTo (nashMap u) (mixedSet S) (mixedSet S) := by
  intro σ hσ i
  have hd : (0:ℝ) < 1 + ∑ b, gain u σ i b := lt_of_lt_of_le zero_lt_one (one_le_denom u σ i)
  constructor
  · intro a
    have h1 : 0 ≤ σ i a + gain u σ i a :=
      add_nonneg ((hσ i).1 a) (gain_nonneg u σ i a)
    exact div_nonneg h1 hd.le
  · show ∑ a, (σ i a + gain u σ i a) / (1 + ∑ b, gain u σ i b) = 1
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [Finset.sum_add_distrib, (hσ i).2]
    field_simp

/-- At a fixed point of the Nash map, no pure deviation is profitable. -/
lemma fixed_point_gain_zero (u : ι → (∀ i, S i) → ℝ) (σ : ∀ i, S i → ℝ)
    (hσ : IsMixedProfile σ) (hfix : nashMap u σ = σ) (i : ι) (a : S i) :
    gain u σ i a = 0 := by
  classical
  set c : ℝ := ∑ b, gain u σ i b with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun b _ => gain_nonneg u σ i b
  have hd : (0:ℝ) < 1 + c := by linarith
  -- the fixed point equation, cleared of denominators
  have key : ∀ b : S i, σ i b * c = gain u σ i b := by
    intro b
    have h := congrFun (congrFun hfix i) b
    have h' : (σ i b + gain u σ i b) / (1 + c) = σ i b := h
    field_simp at h'
    linarith [h']
  -- the average payoff
  set V : ℝ := expectedPayoff u σ i with hV
  set A : S i → ℝ := fun b => expectedPayoff u (Function.update σ i (pureStrat b)) i with hA
  have hVsum : V = ∑ b, σ i b * A b := by
    have := expectedPayoff_update_linear u σ i (σ i)
    rwa [Function.update_eq_self] at this
  have hex : ∃ b : S i, 0 < σ i b ∧ A b ≤ V := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hb0 : ∃ b : S i, 0 < σ i b := by
      by_contra hno
      simp only [not_exists, not_lt] at hno
      have : ∑ b, σ i b = 0 := by
        refine Finset.sum_eq_zero fun b _ => le_antisymm (hno b) ((hσ i).1 b)
      rw [(hσ i).2] at this
      exact one_ne_zero this
    obtain ⟨b₀, hb₀⟩ := hb0
    have hlt : ∑ b, σ i b * V < ∑ b, σ i b * A b := by
      refine Finset.sum_lt_sum (fun b _ => ?_) ⟨b₀, Finset.mem_univ b₀, ?_⟩
      · rcases lt_or_eq_of_le ((hσ i).1 b) with hpos | hzero
        · exact mul_le_mul_of_nonneg_left (le_of_lt (hcon b hpos)) (le_of_lt hpos)
        · rw [← hzero]; simp
      · exact mul_lt_mul_of_pos_left (hcon b₀ hb₀) hb₀
    rw [← Finset.sum_mul, (hσ i).2, one_mul, ← hVsum] at hlt
    exact lt_irrefl V hlt
  obtain ⟨b, hbpos, hble⟩ := hex
  have hgb : gain u σ i b = 0 := by
    unfold gain
    rw [max_eq_left]
    simp only [← hV]
    linarith
  have hc_zero : c = 0 := by
    have := key b
    rw [hgb] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hbpos)
    · exact h
  have := key a
  rw [hc_zero, mul_zero] at this
  exact this.symm

end NashProof

open NashProof AGT in
/-- **Nash's theorem**: every finite game has a mixed Nash equilibrium. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∃ σ : ∀ i, S i → ℝ, IsMixedNash u σ := by
  classical
  obtain ⟨σ, hσmem, hfix⟩ :=
    brouwer_fixed_point (E := ∀ i, S i → ℝ) (K := mixedSet S)
      convex_mixedSet isCompact_mixedSet nonempty_mixedSet (nashMap u)
      (continuous_nashMap u).continuousOn (mapsTo_nashMap u)
  have hσ : IsMixedProfile σ := hσmem
  refine ⟨σ, hσ, ?_⟩
  intro i τ hτ
  have hgain : ∀ a : S i,
      expectedPayoff u (Function.update σ i (pureStrat a)) i ≤ expectedPayoff u σ i := by
    intro a
    have h := fixed_point_gain_zero u σ hσ hfix i a
    unfold gain at h
    have h2 := max_eq_left_iff.mp h
    linarith [h2]
  rw [expectedPayoff_update_linear u σ i τ]
  have hstep : ∑ a : S i, τ a * expectedPayoff u (Function.update σ i (pureStrat a)) i
      ≤ ∑ a : S i, τ a * expectedPayoff u σ i :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hgain a) (hτ.1 a)
  rwa [← Finset.sum_mul, hτ.2, one_mul] at hstep

