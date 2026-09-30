-- Prove2me | solution 1 for ApproxOptRL.PolicyQuality.policy_quality_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:19:09.567633+00:00
-- url     : https://prove2.me/submissions/eaac52b1-f1d2-41cb-affb-834ee1ff7046

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

namespace RLProof
open ApproxOptRL.PolicyQuality
variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] [Nonempty A]

lemma policy_average_le (π : S → A → ℝ) (hπ : IsPolicy π) (f : S → A → ℝ)
    (z : S → ℝ) (hz : ∀ s a, f s a ≤ z s) (s : S) : ∑ a, π s a*f s a ≤ z s := by
  calc _ ≤ ∑ a, π s a*z s := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hz s a) ((hπ s).1 a))
    _ = z s := by rw [← Finset.sum_mul,(hπ s).2,one_mul]

lemma greedy_data (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (π : S → A → ℝ) (hπ : IsPolicy π)
    (μ : S → ℝ) (hμ : IsStateDist μ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ z : S → ℝ, (∀ s, 0 ≤ z s) ∧
      (∀ π' : S → A → ℝ, IsPolicy π' → ∀ s, ∑ a,π' s a*advantage P r γ π s a ≤ z s) ∧
      optPolicyAdvantage P r γ π μ = ∑ s,futureStateDist P γ π μ s*z s := by
  classical
  have hex (s : S) : ∃ a : A, ∀ b : A, advantage P r γ π s b ≤ advantage P r γ π s a := by
    obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image Finset.univ (fun a => advantage P r γ π s a) Finset.univ_nonempty
    exact ⟨a,fun b => hmax b (Finset.mem_univ b)⟩
  choose a ha using hex
  let z := fun s => advantage P r γ π s (a s)
  let πg : S → A → ℝ := fun s b => if b = a s then 1 else 0
  have hπg : IsPolicy πg := by
    intro s
    constructor
    · intro b; dsimp [πg]; split_ifs <;> norm_num
    · simp [πg]
  have hg (s : S) : ∑ b,πg s b*advantage P r γ π s b = z s := by simp [πg,z]
  have hup (π' : S → A → ℝ) (hπ' : IsPolicy π') (s : S) :
      ∑ b,π' s b*advantage P r γ π s b ≤ z s :=
    policy_average_le π' hπ' (advantage P r γ π) z ha s
  have hzero (s : S) : (∑ b,π s b*advantage P r γ π s b) = 0 := by
    rw [advantage_sum P hP r π π hπ γ hγ0 hγ1 s]
    simp
  have hz (s : S) : 0 ≤ z s := by rw [← hzero s]; exact hup π hπ s
  let d := futureStateDist P γ π μ
  have hd := future_prob P hP π hπ μ hμ γ hγ0 hγ1
  have hbound : BddAbove {v : ℝ | ∃ π' : S → A → ℝ, IsPolicy π' ∧ policyAdvantage P r γ π μ π' = v} := by
    refine ⟨∑ s,d s*z s,?_⟩
    rintro v ⟨π',hπ',rfl⟩
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hup π' hπ' s) (hd.1 s))
  have he : policyAdvantage P r γ π μ πg = ∑ s,d s*z s := by
    unfold policyAdvantage
    simp_rw [hg]
    rfl
  refine ⟨z,hz,hup,?_⟩
  unfold optPolicyAdvantage
  apply le_antisymm
  · apply csSup_le (show {v : ℝ | ∃ π' : S → A → ℝ, IsPolicy π' ∧ policyAdvantage P r γ π μ π' = v}.Nonempty from ⟨_,πg,hπg,rfl⟩)
    rintro v ⟨π',hπ',rfl⟩
    exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hup π' hπ' s) (hd.1 s))
  · exact le_csSup hbound ⟨πg,hπg,he⟩

lemma domination_nonneg (d e : S → ℝ) (hd : IsStateDist d) (he : IsStateDist e)
    (C : ℝ) (hC : ∀ s, d s ≤ C*e s) : 0 ≤ C := by
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hC s)
  rw [hd.2,← Finset.mul_sum,he.2,mul_one] at hh
  linarith

lemma quality_first (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (π πt : S → A → ℝ) (hπ : IsPolicy π) (hπt : IsPolicy πt)
    (μ μ' : S → ℝ) (hμ : IsStateDist μ) (hμ' : IsStateDist μ')
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ε C : ℝ) (hε : optPolicyAdvantage P r γ π μ < ε)
    (hC : ∀ s,futureStateDist P γ πt μ' s ≤ C*futureStateDist P γ π μ s) :
    eta P r γ πt μ'-eta P r γ π μ' ≤ ε/(1-γ)*C := by
  have hd := future_prob P hP π hπ μ hμ γ hγ0 hγ1
  have hdt := future_prob P hP πt hπt μ' hμ' γ hγ0 hγ1
  have hC0 := domination_nonneg _ _ hdt hd C hC
  obtain ⟨z,hz,hu,ho⟩ := greedy_data P hP r π hπ μ hμ γ hγ0 hγ1
  have hsum : (∑ s,futureStateDist P γ πt μ' s*∑ a,πt s a*advantage P r γ π s a) ≤ C*ε := by
    calc _ ≤ ∑ s,futureStateDist P γ πt μ' s*z s :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hu πt hπt s) (hdt.1 s))
      _ ≤ ∑ s,(C*futureStateDist P γ π μ s)*z s :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (hC s) (hz s))
      _ = C*optPolicyAdvantage P r γ π μ := by rw [ho,Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs; ring
      _ ≤ C*ε := mul_le_mul_of_nonneg_left hε.le hC0
  rw [performance P hP r π πt hπt μ' hμ' γ hγ0 hγ1]
  calc _ ≤ 1/(1-γ)*(C*ε) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

lemma quality_comparison (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (π πt : S → A → ℝ) (hπ : IsPolicy π) (hπt : IsPolicy πt)
    (μ μ' : S → ℝ) (hμ : IsStateDist μ) (hμ' : IsStateDist μ')
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (C : ℝ) (hC : ∀ s,futureStateDist P γ πt μ' s ≤ C*μ s) (s : S) :
    futureStateDist P γ πt μ' s ≤ C/(1-γ)*futureStateDist P γ π μ s := by
  have hdt := future_prob P hP πt hπt μ' hμ' γ hγ0 hγ1
  have hC0 := domination_nonneg _ _ hdt hμ C hC
  have hd := future_lower P hP π hπ μ hμ γ hγ0 hγ1 s
  have hden : 0 < 1-γ := by linarith
  apply (hC s).trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_left hd hC0
  nlinarith

end RLProof

open ApproxOptRL.PolicyQuality
theorem solution {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (ε : ℝ) (h : optPolicyAdvantage P r γ π μ < ε)
    (πstar : S → A → ℝ) (hπstar : IsOptimalPolicy P r γ πstar)
    (μ' : S → ℝ) (hμ' : IsStateDist μ') :
    (∀ C : ℝ, (∀ s, futureStateDist P γ πstar μ' s ≤ C * futureStateDist P γ π μ s) →
        eta P r γ πstar μ' - eta P r γ π μ' ≤ ε / (1 - γ) * C) ∧
    (∀ C : ℝ, (∀ s, futureStateDist P γ πstar μ' s ≤ C * μ s) →
        ∀ s, futureStateDist P γ πstar μ' s ≤ C / (1 - γ) * futureStateDist P γ π μ s) ∧
    (∀ C : ℝ, (∀ s, futureStateDist P γ πstar μ' s ≤ C * μ s) →
        eta P r γ πstar μ' - eta P r γ π μ' ≤ ε / (1 - γ) ^ 2 * C) := by
  refine ⟨?_,?_,?_⟩
  · intro C hC
    exact RLProof.quality_first P hP r π πstar hπ hπstar.1 μ μ' hμ hμ' γ hγ0 hγ1 ε C h hC
  · intro C hC s
    exact RLProof.quality_comparison P hP π πstar hπ hπstar.1 μ μ' hμ hμ' γ hγ0 hγ1 C hC s
  · intro C hC
    have hc := RLProof.quality_comparison P hP π πstar hπ hπstar.1 μ μ' hμ hμ' γ hγ0 hγ1 C hC
    have hh := RLProof.quality_first P hP r π πstar hπ hπstar.1 μ μ' hμ hμ' γ hγ0 hγ1 ε (C/(1-γ)) h hc
    convert hh using 1 <;> field_simp [show 1-γ ≠ 0 by linarith] <;> ring


