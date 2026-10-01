-- Prove2me | solution 1 for ApproxOptRL.CPI.conservative_update_improvement
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:30:35.98108+00:00
-- url     : https://prove2.me/submissions/4e995a25-e69c-4497-b878-6483210c7770

import Definitions.Def_ApproxOptRL_CPI_Algorithm
import Definitions.Def_ApproxOptRL_PolicyQuality_PolicyAdvantage
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

set_option autoImplicit false

open FoundationsML.ReinforcementLearning in
theorem rl_M_nonneg {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s s' : S) : 0 ≤ InducedTransition π P s s' := by
  unfold InducedTransition
  exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

open FoundationsML.ReinforcementLearning in
theorem rl_M_sum {S A : Type*} [Fintype S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s : S) : ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  have h1 : ∀ a, ∑ s', P s a s' = 1 := fun a => (hP s a).2
  simp_rw [← Finset.mul_sum, h1, mul_one]
  exact (hπ s).2

open FoundationsML.ReinforcementLearning in
theorem rl_D_zero {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 s : S) :
    OccupationDist π P s0 0 s = if s = s0 then 1 else 0 := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_succ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) (t : ℕ) (s' : S) :
    OccupationDist π P s0 (t + 1) s' =
      ∑ s, OccupationDist π P s0 t s * InducedTransition π P s s' := rfl

open FoundationsML.ReinforcementLearning in
theorem rl_D_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (s0 : S) (t : ℕ) :
    (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · rw [rl_D_zero]
      split_ifs <;> norm_num
    · simp [rl_D_zero]
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · rw [rl_D_succ]
      exact Finset.sum_nonneg (fun s _ => mul_nonneg (ih.1 s) (rl_M_nonneg π hπ P hP s s'))
    · simp only [rl_D_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, rl_M_sum π hπ P hP, mul_one]
      exact ih.2

open FoundationsML.ReinforcementLearning in
theorem rl_D_front {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (t : ℕ) :
    ∀ (s0 u : S), OccupationDist π P s0 (t + 1) u =
      ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t u := by
  induction t with
  | zero =>
    intro s0 u
    simp [rl_D_succ, rl_D_zero]
  | succ t ih =>
    intro s0 u
    calc OccupationDist π P s0 (t + 1 + 1) u
        = ∑ v, (∑ s', InducedTransition π P s0 s' * OccupationDist π P s' t v) *
            InducedTransition π P v u := by
          rw [rl_D_succ]
          exact Finset.sum_congr rfl (fun v _ => by rw [ih s0 v])
      _ = ∑ s', InducedTransition π P s0 s' *
            ∑ v, OccupationDist π P s' t v * InducedTransition π P v u := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      _ = ∑ s', InducedTransition π P s0 s' * OccupationDist π P s' (t + 1) u := by
          simp only [rl_D_succ]

open FoundationsML.ReinforcementLearning in
theorem rl_summable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (g : S → ℝ) (s0 : S) :
    Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s0 t s' * g s') := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ0 hγ1).mul_right (∑ s', |g s'|)) (fun t => ?_)
  obtain ⟨hnn, hsum⟩ := rl_D_prob π hπ P hP s0 t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
  calc |∑ s', OccupationDist π P s0 t s' * g s'|
      ≤ ∑ s', |OccupationDist π P s0 t s' * g s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |g s'| := by
      apply Finset.sum_le_sum
      intro s' _
      rw [abs_mul, abs_of_nonneg (hnn s')]
      have h1 : OccupationDist π P s0 t s' ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ s')
      calc OccupationDist π P s0 t s' * |g s'| ≤ 1 * |g s'| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |g s'| := one_mul _

open FoundationsML.ReinforcementLearning in
theorem rl_bellman {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    PolicyValue π P Er γ s =
      InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * PolicyValue π P Er γ s' := by
  have hsum := fun s0 => rl_summable π hπ P hP γ hγ0 hγ1 (InducedReward π Er) s0
  have key : ∀ t : ℕ, γ ^ (t + 1) * ∑ u, OccupationDist π P s (t + 1) u * InducedReward π Er u =
      γ * ∑ s', InducedTransition π P s s' *
        (γ ^ t * ∑ u, OccupationDist π P s' t u * InducedReward π Er u) := by
    intro t
    simp_rw [rl_D_front π P t s]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  unfold PolicyValue
  rw [(hsum s).tsum_eq_zero_add, tsum_congr key, tsum_mul_left,
    Summable.tsum_finsetSum (fun s' _ => (hsum s').mul_left (InducedTransition π P s s'))]
  simp_rw [tsum_mul_left]
  have h0 : γ ^ 0 * ∑ u, OccupationDist π P s 0 u * InducedReward π Er u = InducedReward π Er s := by
    simp [rl_D_zero]
  rw [h0]



open FoundationsML.ReinforcementLearning ApproxOptRL.Shared
namespace RLProof
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]

lemma state_zero (P : S → A → S → ℝ) (π : S → A → ℝ) (μ : S → ℝ) (s : S) :
    stateProb P π μ 0 s = μ s := by
  simp [stateProb,rl_D_zero]

lemma state_succ (P : S → A → S → ℝ) (π : S → A → ℝ) (μ : S → ℝ) (t : ℕ) (s : S) :
    stateProb P π μ (t+1) s = ∑ u, stateProb P π μ t u * InducedTransition π P u s := by
  simp only [stateProb,rl_D_succ]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma state_prob (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (μ : S → ℝ) (hμ : IsStateDist μ) (t : ℕ) :
    (∀ s, 0 ≤ stateProb P π μ t s) ∧ ∑ s, stateProb P π μ t s = 1 := by
  constructor
  · intro s
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (hμ.1 u) ((rl_D_prob π hπ P hP u t).1 s))
  · unfold stateProb
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,(rl_D_prob π hπ P hP _ t).2,mul_one]
    exact hμ.2

lemma state_summable (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (μ : S → ℝ) (hμ : IsStateDist μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    Summable (fun t : ℕ => γ^t*stateProb P π μ t s) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one hγ0 hγ1)
  intro t
  have hp := state_prob P hP π hπ μ hμ t
  have hu : stateProb P π μ t s ≤ 1 := by
    rw [← hp.2]
    exact Finset.single_le_sum (fun u _ => hp.1 u) (Finset.mem_univ s)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg hγ0 t) (hp.1 s))]
  exact mul_le_of_le_one_right (pow_nonneg hγ0 t) hu

lemma future_prob (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (μ : S → ℝ) (hμ : IsStateDist μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsStateDist (futureStateDist P γ π μ) := by
  have hsum := state_summable P hP π hπ μ hμ γ hγ0 hγ1
  constructor
  · intro s
    apply mul_nonneg (by linarith)
    apply tsum_nonneg
    intro t
    exact mul_nonneg (pow_nonneg hγ0 t) ((state_prob P hP π hπ μ hμ t).1 s)
  · unfold futureStateDist
    rw [← Finset.mul_sum,← Summable.tsum_finsetSum (fun s _ => hsum s)]
    simp_rw [← Finset.mul_sum,(state_prob P hP π hπ μ hμ _).2,mul_one]
    rw [tsum_geometric_of_lt_one hγ0 hγ1,mul_inv_cancel₀ (show 1-γ ≠ 0 by linarith)]

lemma future_balance (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (μ : S → ℝ) (hμ : IsStateDist μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    futureStateDist P γ π μ s = (1-γ)*μ s+
      γ*∑ u, futureStateDist P γ π μ u*InducedTransition π P u s := by
  have hsum := state_summable P hP π hπ μ hμ γ hγ0 hγ1
  have he (t : ℕ) : γ^(t+1)*stateProb P π μ (t+1) s =
      γ*∑ u, (γ^t*stateProb P π μ t u)*InducedTransition π P u s := by
    rw [state_succ,pow_succ]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  unfold futureStateDist
  rw [(hsum s).tsum_eq_zero_add,tsum_congr he,tsum_mul_left,
    Summable.tsum_finsetSum (fun u _ => (hsum u).mul_right (InducedTransition π P u s))]
  simp_rw [tsum_mul_right]
  simp only [pow_zero,one_mul,state_zero]
  rw [mul_add]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

lemma future_lower (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (μ : S → ℝ) (hμ : IsStateDist μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    (1-γ)*μ s ≤ futureStateDist P γ π μ s := by
  rw [future_balance P hP π hπ μ hμ γ hγ0 hγ1 s]
  have hn : 0 ≤ γ*∑ u, futureStateDist P γ π μ u*InducedTransition π P u s :=
    mul_nonneg hγ0 (Finset.sum_nonneg (fun u _ =>
      mul_nonneg ((future_prob P hP π hπ μ hμ γ hγ0 hγ1).1 u) (rl_M_nonneg π hπ P hP u s)))
  linarith

lemma value_bellman (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (π : S → A → ℝ) (hπ : IsPolicy π)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    value P r γ π s = (1-γ)*InducedReward π r s+
      γ*∑ u,InducedTransition π P s u*value P r γ π u := by
  have hb := rl_bellman π hπ P hP r γ hγ0 hγ1 s
  unfold value
  rw [hb,mul_add]
  congr 1
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

lemma advantage_sum (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (π πt : S → A → ℝ) (hπt : IsPolicy πt)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    ∑ a, πt s a*advantage P r γ π s a =
      (value P r γ πt s-value P r γ π s)-
      γ*∑ u,InducedTransition πt P s u*(value P r γ πt u-value P r γ π u) := by
  have hb := value_bellman P hP r πt hπt γ hγ0 hγ1 s
  have he : ∑ a, πt s a*advantage P r γ π s a =
      (1-γ)*InducedReward πt r s+γ*∑ u,InducedTransition πt P s u*value P r γ π u-value P r γ π s := by
    unfold advantage qValue InducedReward InducedTransition
    simp_rw [mul_sub,Finset.sum_sub_distrib,mul_add,Finset.sum_add_distrib,
      ← Finset.sum_mul,(hπt s).2,one_mul]
    simp_rw [Finset.mul_sum,Finset.sum_mul]
    congr 1
    congr 1
    · apply Finset.sum_congr rfl; intro a ha; ring
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro u hu
      ring
  rw [he]
  simp_rw [mul_sub,Finset.sum_sub_distrib,mul_sub]
  linarith

lemma performance (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (π πt : S → A → ℝ) (hπt : IsPolicy πt)
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    eta P r γ πt μ-eta P r γ π μ =
      1/(1-γ)*∑ s,futureStateDist P γ πt μ s*∑ a,πt s a*advantage P r γ π s a := by
  let W := fun s => value P r γ πt s-value P r γ π s
  have hs : ∑ s, futureStateDist P γ πt μ s*∑ a,πt s a*advantage P r γ π s a =
      (1-γ)*∑ s,μ s*W s := by
    simp_rw [advantage_sum P hP r π πt hπt γ hγ0 hγ1]
    change (∑ s,futureStateDist P γ πt μ s*(W s-γ*∑ u,InducedTransition πt P s u*W u)) = _
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    have he : (∑ s,futureStateDist P γ πt μ s*(γ*∑ u,InducedTransition πt P s u*W u)) =
        ∑ u, (futureStateDist P γ πt μ u-(1-γ)*μ u)*W u := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      have hh := future_balance P hP πt hπt μ hμ γ hγ0 hγ1 u
      calc
        (∑ s, futureStateDist P γ πt μ s*(γ*(InducedTransition πt P s u*W u))) =
            (γ*∑ s,futureStateDist P γ πt μ s*InducedTransition πt P s u)*W u := by
          simp_rw [Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl; intro s hs; ring
        _ = _ := by congr 1; linarith
    rw [he,← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [hs]
  have he : eta P r γ πt μ-eta P r γ π μ = ∑ s,μ s*W s := by
    simp only [eta,W,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  field_simp [show 1-γ ≠ 0 by linarith]

end RLProof

open ApproxOptRL.CPI
namespace CPIProof
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]

lemma mix_policy (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (α : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) : IsPolicy (mixPolicy α π π') := by
  intro s
  constructor
  · intro a
    exact add_nonneg (mul_nonneg (by linarith [hα.2]) ((hπ s).1 a)) (mul_nonneg hα.1 ((hπ' s).1 a))
  · simp only [mixPolicy,Finset.sum_add_distrib,← Finset.mul_sum,(hπ s).2,(hπ' s).2,mul_one]
    ring

lemma mix_transition (P : S → A → S → ℝ) (π π' : S → A → ℝ) (α : ℝ) (u s : S) :
    InducedTransition (mixPolicy α π π') P u s =
      (1-α)*InducedTransition π P u s+α*InducedTransition π' P u s := by
  simp only [InducedTransition,mixPolicy,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro a ha <;> ring

lemma transition_prob (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (d : S → ℝ) (hd : IsStateDist d) :
    IsStateDist (fun s => ∑ u,d u*InducedTransition π P u s) := by
  constructor
  · intro s
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (hd.1 u) (rl_M_nonneg π hπ P hP u s))
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,rl_M_sum π hπ P hP,mul_one]
    exact hd.2

lemma transition_l1 (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π : S → A → ℝ) (hπ : IsPolicy π) (v : S → ℝ) :
    (∑ s,|∑ u,v u*InducedTransition π P u s|) ≤ ∑ s,|v s| := by
  calc
    _ ≤ ∑ s,∑ u,|v u| *InducedTransition π P u s := by
      apply Finset.sum_le_sum
      intro s hs
      calc _ ≤ ∑ u,|v u*InducedTransition π P u s| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul,abs_of_nonneg (rl_M_nonneg π hπ P hP _ s)]
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum,rl_M_sum π hπ P hP,mul_one]

lemma distance_le_two (d e : S → ℝ) (hd : IsStateDist d) (he : IsStateDist e) :
    (∑ s,|d s-e s|) ≤ 2 := by
  calc _ ≤ ∑ s,(d s+e s) := Finset.sum_le_sum (fun s _ => by
      rw [abs_le]
      constructor <;> linarith [hd.1 s,he.1 s])
    _ = 2 := by rw [Finset.sum_add_distrib,hd.2,he.2]; norm_num

lemma distribution_difference (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) :
    (∑ s,|futureStateDist P γ (mixPolicy α π π') μ s-futureStateDist P γ π μ s|) ≤
      2*α*γ/(1-γ*(1-α)) := by
  let dn := futureStateDist P γ (mixPolicy α π π') μ
  let d := futureStateDist P γ π μ
  let v := fun s => dn s-d s
  have hn := mix_policy π π' hπ hπ' α hα
  have hdn := RLProof.future_prob P hP _ hn μ hμ γ hγ0 hγ1
  have hd := RLProof.future_prob P hP π hπ μ hμ γ hγ0 hγ1
  have hαc : 0 ≤ 1-α := by linarith [hα.2]
  have hden : 0 < 1-γ*(1-α) := by nlinarith [hα.1]
  have hform (s : S) : v s = γ*(1-α)*(∑ u,v u*InducedTransition π P u s)+
      γ*α*((∑ u,dn u*InducedTransition π' P u s)-(∑ u,d u*InducedTransition π P u s)) := by
    have hb1 := RLProof.future_balance P hP _ hn μ hμ γ hγ0 hγ1 s
    have hb0 := RLProof.future_balance P hP π hπ μ hμ γ hγ0 hγ1 s
    change dn s = (1-γ)*μ s+γ*∑ u,dn u*InducedTransition (mixPolicy α π π') P u s at hb1
    change d s = (1-γ)*μ s+γ*∑ u,d u*InducedTransition π P u s at hb0
    have he : (∑ u,dn u*InducedTransition (mixPolicy α π π') P u s) =
        (1-α)*(∑ u,dn u*InducedTransition π P u s)+α*(∑ u,dn u*InducedTransition π' P u s) := by
      simp_rw [mix_transition,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro u hu <;> ring
    rw [he] at hb1
    dsimp only [v]
    simp_rw [sub_mul,Finset.sum_sub_distrib]
    nlinarith
  have habs (s : S) : |v s| ≤ γ*(1-α)*|∑ u,v u*InducedTransition π P u s|+
      γ*α*|(∑ u,dn u*InducedTransition π' P u s)-(∑ u,d u*InducedTransition π P u s)| := by
    rw [hform]
    calc _ ≤ _ := abs_add_le _ _
      _ = _ := by simp only [abs_mul,abs_of_nonneg hγ0,abs_of_nonneg hαc,abs_of_nonneg hα.1]
  have hb1 := transition_l1 P hP π hπ v
  have hb2 := distance_le_two _ _ (transition_prob P hP π' hπ' dn hdn) (transition_prob P hP π hπ d hd)
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => habs s)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hsum
  have h1 := mul_le_mul_of_nonneg_left hb1 (mul_nonneg hγ0 hαc)
  have h2 := mul_le_mul_of_nonneg_left hb2 (mul_nonneg hγ0 hα.1)
  change (∑ s,|v s|) ≤ _
  apply (le_div_iff₀ hden).mpr
  nlinarith

lemma mix_advantage (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (α : ℝ) (s : S) :
    (∑ a,mixPolicy α π π' s a*advantage P r γ π s a) = α*∑ a,π' s a*advantage P r γ π s a := by
  have hzero : (∑ a,π s a*advantage P r γ π s a) = 0 := by
    rw [RLProof.advantage_sum P hP r π π hπ γ hγ0 hγ1 s]
    simp
  simp only [mixPolicy,add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,hzero,mul_zero,zero_add]

lemma improvement (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ s, |∑ a,π' s a*advantage P r γ π s a| ≤ ε) :
    α/(1-γ)*(policyAdvantage P r γ π μ π'-2*α*γ*ε/(1-γ*(1-α))) ≤
      eta P r γ (mixPolicy α π π') μ-eta P r γ π μ := by
  let a := fun s => ∑ b,π' s b*advantage P r γ π s b
  let dn := futureStateDist P γ (mixPolicy α π π') μ
  let d := futureStateDist P γ π μ
  have hdist := distribution_difference P hP π π' hπ hπ' μ hμ γ hγ0 hγ1 α hα
  have hpair : (∑ s,d s*a s)-(∑ s,dn s*a s) ≤ ε*∑ s,|dn s-d s| := by
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    calc d s*a s-dn s*a s = (d s-dn s)*a s := by ring
      _ ≤ |(d s-dn s)*a s| := le_abs_self _
      _ = |dn s-d s| *|a s| := by rw [abs_mul,abs_sub_comm]
      _ ≤ ε*|dn s-d s| := by nlinarith [mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg (dn s-d s))]
  have herr := mul_le_mul_of_nonneg_left hdist hε
  have hsum : policyAdvantage P r γ π μ π'-2*α*γ*ε/(1-γ*(1-α)) ≤ ∑ s,dn s*a s := by
    change (∑ s,d s*a s)-_ ≤ _
    change ε*(∑ s,|dn s-d s|) ≤ _ at herr
    have he : ε*(2*α*γ/(1-γ*(1-α))) = 2*α*γ*ε/(1-γ*(1-α)) := by ring
    rw [he] at herr
    linarith
  rw [RLProof.performance P hP r π _ (mix_policy π π' hπ hπ' α hα) μ hμ γ hγ0 hγ1]
  simp_rw [mix_advantage P hP r π π' hπ γ hγ0 hγ1 α]
  have he : (∑ s,futureStateDist P γ (mixPolicy α π π') μ s*(α*∑ b,π' s b*advantage P r γ π s b)) =
      α*∑ s,dn s*a s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [dn,a]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsum (div_nonneg hα.1 (sub_nonneg.mpr hγ1.le))
  convert! hh using 1 <;> ring

end CPIProof

namespace CPIProof
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]

lemma value_range (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π : S → A → ℝ) (hπ : IsPolicy π) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    0 ≤ value P r γ π s ∧ value P r γ π s ≤ R := by
  have hrew (u : S) : 0 ≤ InducedReward π r u ∧ InducedReward π r u ≤ R := by
    constructor
    · exact Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ u).1 a) (hr u a).1)
    · calc _ ≤ ∑ a,π u a*R := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hr u a).2 ((hπ u).1 a))
        _ = R := by rw [← Finset.sum_mul,(hπ u).2,one_mul]
  have he (t : ℕ) : 0 ≤ (∑ u,OccupationDist π P s t u*InducedReward π r u) ∧
      (∑ u,OccupationDist π P s t u*InducedReward π r u) ≤ R := by
    have hD := rl_D_prob π hπ P hP s t
    constructor
    · exact Finset.sum_nonneg (fun u _ => mul_nonneg (hD.1 u) (hrew u).1)
    · calc _ ≤ ∑ u,OccupationDist π P s t u*R := Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hrew u).2 (hD.1 u))
        _ = R := by rw [← Finset.sum_mul,hD.2,one_mul]
  have hs := rl_summable π hπ P hP γ hγ0 hγ1 (InducedReward π r) s
  have hgeo := (summable_geometric_of_lt_one hγ0 hγ1).mul_right R
  have hu := hs.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (he t).2 (pow_nonneg hγ0 t)) hgeo
  rw [tsum_mul_right,tsum_geometric_of_lt_one hγ0 hγ1] at hu
  have hn : 0 ≤ PolicyValue π P r γ s := by
    apply tsum_nonneg
    intro t
    exact mul_nonneg (pow_nonneg hγ0 t) (he t).1
  have hden : 0 < 1-γ := by linarith
  refine ⟨mul_nonneg hden.le hn,?_⟩
  have hh := mul_le_mul_of_nonneg_left hu hden.le
  change (1-γ)*PolicyValue π P r γ s ≤ R
  simpa only [PolicyValue,← mul_assoc,mul_inv_cancel₀ (ne_of_gt hden),one_mul] using hh

lemma q_range (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π : S → A → ℝ) (hπ : IsPolicy π) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) (a : A) :
    0 ≤ qValue P r γ π s a ∧ qValue P r γ π s a ≤ R := by
  have hv := value_range P hP r R hR hr π hπ γ hγ0 hγ1
  have hs0 : 0 ≤ ∑ u,P s a u*value P r γ π u :=
    Finset.sum_nonneg (fun u _ => mul_nonneg ((hP s a).1 u) (hv u).1)
  have hs1 : (∑ u,P s a u*value P r γ π u) ≤ R := by
    calc _ ≤ ∑ u,P s a u*R := Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hv u).2 ((hP s a).1 u))
      _ = R := by rw [← Finset.sum_mul,(hP s a).2,one_mul]
  unfold qValue
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hγ1.le) (hr s a).1) (mul_nonneg hγ0 hs0)
  · have h1 := mul_le_mul_of_nonneg_left (hr s a).2 (show 0 ≤ 1-γ by linarith)
    have h2 := mul_le_mul_of_nonneg_left hs1 hγ0
    nlinarith

lemma average_advantage_abs (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s : S) :
    |∑ a,π' s a*advantage P r γ π s a| ≤ R := by
  have hv := value_range P hP r R hR hr π hπ γ hγ0 hγ1 s
  have hb (a : A) : |advantage P r γ π s a| ≤ R := by
    have hq := q_range P hP r R hR hr π hπ γ hγ0 hγ1 s a
    unfold advantage
    rw [abs_le]
    constructor <;> linarith
  calc _ ≤ ∑ a,|π' s a*advantage P r γ π s a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a,π' s a*R := Finset.sum_le_sum (fun a _ => by
      rw [abs_mul,abs_of_nonneg ((hπ' s).1 a)]
      exact mul_le_mul_of_nonneg_left (hb a) ((hπ' s).1 a))
    _ = R := by rw [← Finset.sum_mul,(hπ' s).2,one_mul]

lemma advantage_le_R (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    policyAdvantage P r γ π μ π' ≤ R := by
  have hd := RLProof.future_prob P hP π hπ μ hμ γ hγ0 hγ1
  calc _ ≤ ∑ s,futureStateDist P γ π μ s*R := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (average_advantage_abs P hP r R hR hr π π' hπ hπ' γ hγ0 hγ1 s)) (hd.1 s))
    _ = R := by rw [← Finset.sum_mul,hd.2,one_mul]

lemma eta_range (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π : S → A → ℝ) (hπ : IsPolicy π) (μ : S → ℝ) (hμ : IsStateDist μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : 0 ≤ eta P r γ π μ ∧ eta P r γ π μ ≤ R := by
  have hv := value_range P hP r R hR hr π hπ γ hγ0 hγ1
  constructor
  · exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ.1 s) (hv s).1)
  · calc _ ≤ ∑ s,μ s*R := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hv s).2 (hμ.1 s))
      _ = R := by rw [← Finset.sum_mul,hμ.2,one_mul]

lemma bounded_step (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 < R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ policyAdvantage P r γ π μ π') :
    a^2/(8*R) ≤ eta P r γ (mixPolicy ((1-γ)*a/(4*R)) π π') μ-eta P r γ π μ := by
  have haR := ha.trans (advantage_le_R P hP r R hR.le hr π π' hπ hπ' μ hμ γ hγ0 hγ1)
  let α := (1-γ)*a/(4*R)
  have hden : 0 < 1-γ := by linarith
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by
    apply (div_le_one (show 0 < 4*R by positivity)).mpr
    nlinarith [mul_nonneg hγ0 ha0]
  have hb := improvement P hP r π π' hπ hπ' μ hμ γ hγ0 hγ1 α ⟨hα0,hα1⟩ R hR.le
    (average_advantage_abs P hP r R hR.le hr π π' hπ hπ' γ hγ0 hγ1)
  have hd : 0 < 1-γ*(1-α) := by nlinarith
  have hcost : 2*α*γ*R/(1-γ*(1-α)) ≤ a/2 := by
    apply (div_le_iff₀ hd).mpr
    have hid : 4*R*α = (1-γ)*a := by dsimp [α]; field_simp
    have hprod := mul_nonneg (show 0 ≤ a*γ by positivity) hα0
    nlinarith [mul_nonneg (show 0 ≤ (1-γ)*a by positivity) (show 0 ≤ 1-γ by linarith)]
  have hgain : a^2/(8*R) ≤ α/(1-γ)*(policyAdvantage P r γ π μ π'-2*α*γ*R/(1-γ*(1-α))) := by
    calc _ = α/(1-γ)*(a/2) := by dsimp [α]; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hα0 hden.le)
  exact hgain.trans hb

end CPIProof

namespace CPIProof
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]

lemma run_policy (P : S → A → S → ℝ) (r : S → A → ℝ) (μ : S → ℝ)
    (γ R ε : ℝ) (hγ1 : γ < 1) (hR : 0 < R) (hε : 0 < ε)
    (G : (S → A → ℝ) → S → A → ℝ) (hG : IsGreedyChooser P r γ μ ε G)
    (π₀ : S → A → ℝ) (hπ₀ : IsPolicy π₀) (e : ℕ → ℝ) (j : ℕ) :
    IsPolicy (cpiPolicy γ R ε G π₀ e j) := by
  induction j with
  | zero => exact hπ₀
  | succ j ih =>
    rw [cpiPolicy]
    split_ifs with he
    · exact ih
    · have he' : 2*ε/3 ≤ e j := le_of_not_gt he
      apply mix_policy _ _ ih (hG _ ih).1
      constructor
      · apply le_min (by norm_num)
        apply div_nonneg _ (by positivity)
        exact mul_nonneg (by linarith) (by linarith)
      · exact min_le_left _ _

lemma accurate_update (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (R : ℝ) (hR : 0 < R) (hr : ∀ s a,0 ≤ r s a ∧ r s a ≤ R)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ε t : ℝ) (hε : 0 < ε) (ht : 2*ε/3 ≤ t)
    (hacc : |t-policyAdvantage P r γ π μ π'| < ε/3) :
    eta P r γ π μ+ε^2/(72*R) ≤ eta P r γ (mixPolicy (cpiStepSize γ R ε t) π π') μ := by
  let a := t-ε/3
  have haε : ε/3 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := by linarith
  have ha : a ≤ policyAdvantage P r γ π μ π' := by
    have hh := (abs_lt.mp hacc).2
    dsimp [a]
    linarith
  have haR := ha.trans (advantage_le_R P hP r R hR.le hr π π' hπ hπ' μ hμ γ hγ0 hγ1)
  have hclip : (1-γ)*a/(4*R) ≤ 1 := by
    apply (div_le_one (show 0 < 4*R by positivity)).mpr
    nlinarith [mul_nonneg hγ0 ha0]
  have he : cpiStepSize γ R ε t = (1-γ)*a/(4*R) := min_eq_right hclip
  rw [he]
  have hh := bounded_step P hP r R hR hr π π' hπ hπ' μ hμ γ hγ0 hγ1 a ha0 ha
  have hsq := pow_le_pow_left₀ (show 0 ≤ ε/3 by positivity) haε 2
  have hrate : ε^2/(72*R) ≤ a^2/(8*R) := by
    calc _ = (ε/3)^2/(8*R) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsq (by positivity)
  linarith

end CPIProof

theorem solution {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (π π' : S → A → ℝ) (hπ : IsPolicy π) (hπ' : IsPolicy π')
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let ε : ℝ := Finset.univ.sup' Finset.univ_nonempty
      (fun s => |∑ a, π' s a * advantage P r γ π s a|)
    α / (1 - γ) * (policyAdvantage P r γ π μ π' - 2 * α * γ * ε / (1 - γ * (1 - α))) ≤
      eta P r γ (mixPolicy α π π') μ - eta P r γ π μ := by
  classical
  let E := Finset.univ.sup' Finset.univ_nonempty (fun s => |∑ a,π' s a*advantage P r γ π s a|)
  have hE (s : S) : |∑ a,π' s a*advantage P r γ π s a| ≤ E := by
    exact Finset.le_sup' (fun u : S => |∑ a,π' u a*advantage P r γ π u a|) (Finset.mem_univ s)
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE (Classical.arbitrary S))
  exact CPIProof.improvement P hP r π π' hπ hπ' μ hμ γ hγ0 hγ1 α hα E hE0 hE


