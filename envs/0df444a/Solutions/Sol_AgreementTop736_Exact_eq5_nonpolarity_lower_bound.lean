-- Prove2me | solution 1 for AgreementTop736.Exact.eq5_nonpolarity_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:06.59637+00:00
-- url     : https://prove2.me/submissions/9a66c4b5-8134-4ddf-8353-a49a6caaf0ce

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized
import Theorems.Thm_AgreementTop736_Exact_eq3_conditioned_gap

section
set_option autoImplicit false
namespace AgreementTop736.Exact.Dev.Eq5
open Finset AgreementTop736.Exact AgreementTop736.Exact.Scheme

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma rho_pos (S : Scheme V) (hS : S.IsValid) : 0 < S.ρ := by
  unfold Scheme.ρ
  have h1 := hS.n_pos
  have h2 := hS.n_lt_N
  apply div_pos
  · exact_mod_cast h1
  · exact_mod_cast (h1.trans h2)

lemma muD_nonneg (S : Scheme V) (hS : S.IsValid) (K H : Finset V) : 0 ≤ S.μ K * S.D K H := by
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · exact mul_nonneg h.le (hS.D_nonneg K h H)

lemma muH_nonneg (S : Scheme V) (hS : S.IsValid) (H : Finset V) : 0 ≤ S.μH H :=
  Finset.sum_nonneg fun K _ => muD_nonneg S hS K H

lemma D_zero_of_not_mem (S : Scheme V) (hS : S.IsValid) (K : Finset V) (hK : 0 < S.μ K) (x : V)
    (hx : x ∉ K) (H : Finset V) : S.D K H * (if x ∈ H then 1 else 0) = 0 := by
  rcases (hS.D_nonneg K hK H).eq_or_lt with h | h
  · rw [← h]; simp
  · have := (hS.D_support K hK H h).1
    have : x ∉ H := fun hh => hx (this hh)
    simp [this]

lemma incl_zero (S : Scheme V) (hS : S.IsValid) (K : Finset V) (hK : 0 < S.μ K) (x : V)
    (hx : x ∉ K) : S.incl K x = 0 := by
  unfold Scheme.incl
  exact Finset.sum_eq_zero fun H _ => D_zero_of_not_mem S hS K hK x hx H

lemma probInH_eq (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) (x : V) :
    S.probInH x = S.ρ * S.pointMass x := by
  unfold Scheme.probInH Scheme.pointMass
  have : ∀ H, S.μH H * (if x ∈ H then (1:ℝ) else 0) = ∑ K, S.μ K * (S.D K H * (if x ∈ H then 1 else 0)) := by
    intro H
    unfold Scheme.μH
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro K _; ring
  simp_rw [this]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [← Finset.mul_sum]
  have hi : ∑ H, S.D K H * (if x ∈ H then (1:ℝ) else 0) = S.incl K x := rfl
  rw [hi]
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · by_cases hxK : x ∈ K
    · rw [h1 K h x hxK]; simp [hxK]; ring
    · rw [incl_zero S hS K h x hxK]; simp [hxK]


lemma pointMass_nonneg (S : Scheme V) (hS : S.IsValid) (x : V) : 0 ≤ S.pointMass x := by
  unfold Scheme.pointMass
  refine Finset.sum_nonneg fun K _ => ?_
  have := hS.μ_nonneg K
  split_ifs <;> simp [this]

lemma tw_nonneg (S : Scheme V) (hS : S.IsValid) (H K K' : Finset V) : 0 ≤ S.testWeight H K K' := by
  unfold Scheme.testWeight Scheme.U
  have h0 := muH_nonneg S hS H
  have hU : ∀ K, 0 ≤ S.μ K * S.D K H / S.μH H := fun K =>
    div_nonneg (muD_nonneg S hS K H) h0
  exact mul_nonneg (mul_nonneg h0 (hU K)) (hU K')

lemma tower {ι κ ℓ m' : Type*} (A : Finset ι) (B : Finset κ) (C : Finset ℓ) (T : Finset m')
    (f : ι → κ → ℓ → m' → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ y ∈ T, f a b c y = ∑ y ∈ T, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c y := by
  calc _ = ∑ a ∈ A, ∑ b ∈ B, ∑ y ∈ T, ∑ c ∈ C, f a b c y :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a ∈ A, ∑ y ∈ T, ∑ b ∈ B, ∑ c ∈ C, f a b c y :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- numerator of eq3 -/
noncomputable def Bnum (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (x : V) (s : α) : ℝ :=
  ∑ H, ∑ K, ∑ K', S.testWeight H K K' * (if x ∈ H then 1 else 0) *
          (phi F g a x s K - phi F g a x s K') ^ 2

lemma enp_swap (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) :
    S.Enp F g a = ∑ x, ∑ s ∈ offLabels g x, Bnum S F g a x s := by
  unfold Scheme.Enp phiDistSq Bnum
  have step : ∀ H K K', S.testWeight H K K' *
      ∑ x ∈ H, ∑ s ∈ offLabels g x, (phi F g a x s K - phi F g a x s K') ^ 2 =
      ∑ x, ∑ s ∈ offLabels g x, S.testWeight H K K' * (if x ∈ H then 1 else 0) *
          (phi F g a x s K - phi F g a x s K') ^ 2 := by
    intro H K K'
    have e : ∀ Q : V → ℝ, ∑ x ∈ H, Q x = ∑ x, if x ∈ H then Q x else 0 := fun Q => by
      rw [← Finset.sum_filter]; simp
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ H
    · simp only [if_pos hx, one_mul, mul_one]
      rw [Finset.mul_sum]
    · simp [hx]
  simp_rw [step]
  rw [tower]
  apply Finset.sum_congr rfl
  intro x _
  rw [tower]


lemma phi_sq_sum (F : Finset V → V → α) (g : V → α) {a : ℝ} (ha : 0 < a) (K : Finset V) :
    ∑ x, ∑ s ∈ offLabels g x, phi F g a x s K ^ 2 =
      (errCount F g K : ℝ) / ((errCount F g K : ℝ) + a) := by
  have hpos : 0 < (errCount F g K : ℝ) + a := by
    have : (0:ℝ) ≤ errCount F g K := Nat.cast_nonneg _
    linarith
  have hc : fReg a (errCount F g K) ^ 2 = 1 / ((errCount F g K : ℝ) + a) := by
    unfold fReg
    rw [div_pow, Real.sq_sqrt hpos.le]; simp
  have inner : ∀ x, ∑ s ∈ offLabels g x, phi F g a x s K ^ 2 =
      if x ∈ K ∧ F K x ≠ g x then 1 / ((errCount F g K : ℝ) + a) else 0 := by
    intro x
    have : ∀ s, phi F g a x s K ^ 2 = if F K x = s then (if x ∈ K then 1 / ((errCount F g K : ℝ) + a) else 0) else 0 := by
      intro s
      unfold phi
      by_cases h1 : x ∈ K <;> by_cases h2 : F K x = s <;> simp [h1, h2, hc]
    simp_rw [this]
    rw [Finset.sum_ite_eq]
    unfold offLabels
    by_cases h1 : x ∈ K <;> by_cases h2 : F K x = g x <;> simp [h1, h2]
  simp_rw [inner]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter (fun x => x ∈ K ∧ F K x ≠ g x)) = K.filter (fun x => F K x ≠ g x) := by
    ext x; simp
  rw [this]
  unfold errCount
  field_simp

lemma V_eq (S : Scheme V) (F : Finset V → V → α) (g : V → α) {a : ℝ} (ha : 0 < a) :
    S.Vreg F g a = ∑ x, ∑ s ∈ offLabels g x, ∑ K, S.μ K * phi F g a x s K ^ 2 := by
  unfold Scheme.Vreg
  have : ∀ x, ∑ s ∈ offLabels g x, ∑ K, S.μ K * phi F g a x s K ^ 2 =
      ∑ K, S.μ K * ∑ s ∈ offLabels g x, phi F g a x s K ^ 2 := by
    intro x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro K _
    rw [Finset.mul_sum]
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  rw [← Finset.mul_sum, phi_sq_sum F g ha K]

lemma coord_bound (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) {γ : ℝ} (hγ : 0 < γ)
    (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) (x : V) (s : α) (hs : s ≠ g x) :
    S.ρ * γ * ∑ K, S.μ K * phi F g a x s K ^ 2 ≤ Bnum S F g a x s := by
  have hρ := rho_pos S hS
  have hB : 0 ≤ Bnum S F g a x s := by
    unfold Bnum
    refine Finset.sum_nonneg fun H _ => Finset.sum_nonneg fun K _ => Finset.sum_nonneg fun K' _ => ?_
    have := tw_nonneg S hS H K K'
    have : 0 ≤ (if x ∈ H then (1:ℝ) else 0) := by split_ifs <;> norm_num
    positivity
  rcases (pointMass_nonneg S hS x).eq_or_lt with hp | hp
  · have hz : ∀ K, S.μ K * (if x ∈ K then (1:ℝ) else 0) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun K => S.μ K * (if x ∈ K then (1:ℝ) else 0)) (fun K _ => by
          have := hS.μ_nonneg K
          split_ifs <;> simp [this])).1 hp.symm
      intro K; exact this K (mem_univ _)
    have : ∑ K, S.μ K * phi F g a x s K ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro K _
      by_cases hxK : x ∈ K
      · have := hz K
        simp only [hxK, if_true, mul_one] at this
        rw [this]; simp
      · simp [phi, hxK]
    rw [this]; simpa using hB
  · have hx := hp
    have hpi : 0 < S.probInH x := by rw [probInH_eq S hS h1]; positivity
    have e3 := AgreementTop736.Exact.eq3_conditioned_gap S hS h1 hγ h3 F g hg ha x hx s hs
    have hW : ∑ K, S.μ K * phi F g a x s K ^ 2 = S.pointMass x * ∑ K, S.μx x K * phi F g a x s K ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hxK : x ∈ K
      · unfold Scheme.μx
        simp only [hxK, if_true, mul_one]
        field_simp
      · simp [phi, hxK]
    rw [hW]
    have := (le_div_iff₀ hpi).1 e3
    unfold Bnum
    rw [probInH_eq S hS h1] at this
    nlinarith

end AgreementTop736.Exact.Dev.Eq5
namespace AgreementTop736.Exact
open Finset Scheme
open AgreementTop736.Exact.Dev.Eq5 in
theorem chk_eq5_nonpolarity_lower_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) {γ : ℝ} (hγ : 0 < γ)
    (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) :
    S.ρ * γ * S.Vreg F g a ≤ S.Enp F g a := by
  rw [enp_swap, V_eq S F g ha, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hs' : s ≠ g x := by simpa [offLabels] using hs
  exact coord_bound S hS h1 hγ h3 F g hg ha x s hs'

end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_eq5_nonpolarity_lower_bound := @AgreementTop736.Exact.chk_eq5_nonpolarity_lower_bound
