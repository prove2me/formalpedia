-- Prove2me | solution 1 for AC02Frege.eq_49_sampling_tail
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T03:18:09.76398+00:00
-- url     : https://prove2.me/submissions/885e8b8f-5ec4-4651-9720-50698c424f79

import Mathlib
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Bernoulli

section
-- Inlined Solutions.SamplingJointProbabilities

set_option maxHeartbeats 2000000

namespace AC02Frege.SamplingJointProbabilities

theorem choose_power_compare (N j k : ℕ) (hj : j ≤ N) :
    j.choose k*N^k ≤ N.choose k*j^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k+1 ≤ j
    · have hratio : (j-k)*N ≤ (N-k)*j := by
        rw [Nat.sub_mul,Nat.sub_mul,Nat.mul_comm N j]
        exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hj) _
      apply Nat.le_of_mul_le_mul_right (c:=k+1) ?_ (by omega)
      calc
        _ = (j.choose (k+1)*(k+1))*N^k*N := by rw [pow_succ]; ring
        _ = (j.choose k*(j-k))*N^k*N := by rw [Nat.choose_succ_right_eq]
        _ = (j.choose k*N^k)*((j-k)*N) := by ring
        _ ≤ (N.choose k*j^k)*((j-k)*N) := Nat.mul_le_mul_right _ ih
        _ ≤ (N.choose k*j^k)*((N-k)*j) := Nat.mul_le_mul_left _ hratio
        _ = (N.choose k*(N-k))*j^k*j := by ring
        _ = (N.choose (k+1)*(k+1))*j^k*j := by rw [Nat.choose_succ_right_eq]
        _ = (N.choose (k+1)*j^(k+1))*(k+1) := by rw [pow_succ]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : j < k+1)]
      simp

theorem choose_ratio_le (N j k : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (hk : k ≤ N) :
    (j.choose k : ℝ)/(N.choose k : ℝ) ≤ ((j : ℝ)/(N : ℝ))^k := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hC : 0 < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  rw [div_pow]
  apply (div_le_div_iff₀ hC (pow_pos hNp k)).mpr
  have h := choose_power_compare N j k hj
  have hh : (j.choose k : ℝ)*(N : ℝ)^k ≤ (N.choose k : ℝ)*(j : ℝ)^k := by exact_mod_cast h
  nlinarith

theorem joint_bound (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (A : Finset (Fin N)) :
    ((((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·)).card : ℝ)/
      (N.choose j : ℝ) ≤ ((j : ℝ)/(N : ℝ))^A.card := by
  classical
  have hAN : A.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
  by_cases hAj : A.card ≤ j
  · rw [Finset.card_filter_powersetCard_subset A Finset.univ j (Finset.subset_univ _) hAj,
      Finset.card_univ,Fintype.card_fin]
    have hCNj : 0 < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
    have hCNk : 0 < (N.choose A.card : ℝ) := by exact_mod_cast Nat.choose_pos hAN
    have he : ((N-A.card).choose (j-A.card) : ℝ)/(N.choose j : ℝ) =
        (j.choose A.card : ℝ)/(N.choose A.card : ℝ) := by
      apply (div_eq_div_iff hCNj.ne' hCNk.ne').mpr
      have h := Nat.choose_mul (n:=N) hAj
      have hh : (N.choose j : ℝ)*(j.choose A.card : ℝ) =
          (N.choose A.card : ℝ)*((N-A.card).choose (j-A.card) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [he]
    exact choose_ratio_le N j A.card hN hj hAN
  · have he : ((Finset.univ : Finset (Fin N)).powersetCard j).filter (A ⊆ ·) = ∅ := by
      apply Finset.ext
      intro S
      constructor
      · intro hS
        exfalso
        obtain ⟨hSj,hAS⟩ := Finset.mem_filter.mp hS
        have hcard := (Finset.mem_powersetCard.mp hSj).2
        have hh := Finset.card_le_card hAS
        omega
      · simp
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_div]
    positivity

end AC02Frege.SamplingJointProbabilities
end

section
-- Inlined Solutions.SamplingMomentBound

set_option maxHeartbeats 2000000

namespace AC02Frege.SamplingMomentBound

open Classical

noncomputable def sample (N j : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powersetCard j

noncomputable def moment (N j : ℕ) (I : Finset (Fin N)) (θ : ℝ) : ℝ :=
  (∑ S ∈ sample N j, Real.exp (θ*((S ∩ I).card : ℝ)))/(N.choose j : ℝ)

theorem exp_card_expansion {N : ℕ} (I S : Finset (Fin N)) (θ : ℝ) :
    Real.exp (θ*((S ∩ I).card : ℝ)) =
      ∑ A ∈ I.powerset, if A ⊆ S then (Real.exp θ-1)^A.card else 0 := by
  let t := Real.exp θ-1
  have hfilter : I.filter (fun i => i ∈ S) = S ∩ I := by ext i; simp [and_comm]
  have hp : (∏ i ∈ I, (1+if i ∈ S then t else 0)) = Real.exp (θ*((S ∩ I).card : ℝ)) := by
    calc
      _ = ∏ i ∈ I, if i ∈ S then Real.exp θ else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : i ∈ S <;> simp [h,t]
      _ = (Real.exp θ)^((S ∩ I).card) := by simp only [Finset.prod_ite,Finset.prod_const_one,mul_one,hfilter,Finset.prod_const]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [← hp,Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hAS : A ⊆ S
  · rw [if_pos hAS]
    calc
      _ = ∏ _i ∈ A, t := Finset.prod_congr rfl (fun i hi => by simp [hAS hi])
      _ = _ := by simp [t]
  · rw [if_neg hAS]
    obtain ⟨i,hi,hni⟩ := Finset.not_subset.mp hAS
    exact Finset.prod_eq_zero hi (by simp [hni])

theorem moment_le (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (I : Finset (Fin N))
    (θ : ℝ) (hθ : 0 ≤ θ) : moment N j I θ ≤ (1-(j : ℝ)/N+((j : ℝ)/N)*Real.exp θ)^I.card := by
  let p := (j : ℝ)/(N : ℝ)
  let t := Real.exp θ-1
  have ht : 0 ≤ t := by dsimp [t]; linarith [Real.one_le_exp hθ]
  have hinner (A : Finset (Fin N)) :
      (∑ S ∈ sample N j, if A ⊆ S then t^A.card else 0) =
        ((((sample N j).filter (A ⊆ ·)).card : ℝ)*t^A.card) := by
    rw [← Finset.sum_filter]
    simp
  have hsum : moment N j I θ =
      ∑ A ∈ I.powerset, t^A.card*((((sample N j).filter (A ⊆ ·)).card : ℝ)/(N.choose j : ℝ)) := by
    unfold moment
    simp_rw [exp_card_expansion]
    rw [Finset.sum_comm,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro A hA
    rw [hinner A]
    ring
  rw [hsum]
  calc
    _ ≤ ∑ A ∈ I.powerset, (t*p)^A.card := by
      apply Finset.sum_le_sum
      intro A hA
      have h := mul_le_mul_of_nonneg_left (SamplingJointProbabilities.joint_bound N j hN hj A)
        (pow_nonneg ht A.card)
      simpa only [mul_pow,sample,p] using h
    _ = (1+t*p)^I.card := by
      have h := Finset.prod_one_add (f:=fun _i : Fin N => t*p) I
      simpa only [Finset.prod_const] using h.symm
    _ = _ := by congr 1; dsimp [t,p]; ring

end AC02Frege.SamplingMomentBound
end

section
-- Inlined Solutions.BernoulliHoeffding

open MeasureTheory ProbabilityTheory

namespace AC02Frege.BernoulliHoeffding

theorem centered_mgf (p θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p*Real.exp (θ*(1-p))+(1-p)*Real.exp (-θ*p) ≤ Real.exp (θ^2/8) := by
  let q : unitInterval := ⟨p,hp0,hp1⟩
  let μ := bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hm : AEMeasurable X μ := (measurable_of_countable X).aemeasurable
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun b => by cases b <;> simp [X])
  have hmean : ∫ b, X b ∂μ = p := by
    rw [integral_bernoulliMeasure]
    simp [X,q]
  have h := (hasSubgaussianMGF_of_mem_Icc hm hb).mgf_le θ
  rw [hmean] at h
  unfold mgf at h
  rw [integral_bernoulliMeasure] at h
  norm_num [X,q,smul_eq_mul] at h
  rw [show (1/4 : ℝ)*θ^2/2 = θ^2/8 by ring] at h
  simpa only [neg_mul] using h

theorem uncentered_mgf (p θ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    1-p+p*Real.exp θ ≤ Real.exp (p*θ+θ^2/8) := by
  have h := mul_le_mul_of_nonneg_right (centered_mgf p θ hp0 hp1) (Real.exp_pos (p*θ)).le
  have he : (p*Real.exp (θ*(1-p))+(1-p)*Real.exp (-θ*p))*Real.exp (p*θ) = 1-p+p*Real.exp θ := by
    rw [add_mul,mul_assoc,mul_assoc,← Real.exp_add,← Real.exp_add]
    rw [show θ*(1-p)+p*θ = θ by ring,show -θ*p+p*θ = 0 by ring,Real.exp_zero,mul_one]
    ring
  rw [he,← Real.exp_add] at h
  simpa only [add_comm] using h

end AC02Frege.BernoulliHoeffding
end

section
-- Inlined Solutions.SamplingTail

set_option maxHeartbeats 2000000

namespace AC02Frege.SamplingTail

open Classical SamplingMomentBound

theorem sampling_tail (N j : ℕ) (hj : j ≤ N) (I : Finset (Fin N)) (hI : 1 ≤ I.card)
    (u : ℝ) (hu : 0 ≤ u) :
    ((((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
        u ≤ ((S ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/N))).card : ℕ) : ℝ)/
      (N.choose j : ℝ) ≤ Real.exp (-2*u^2/I.card) := by
  have hIN : I.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
  have hN : 1 ≤ N := hI.trans hIN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hden : 0 < (N.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  let p := (j : ℝ)/(N : ℝ)
  let L := (I.card : ℝ)
  let θ := 4*u/L
  let E (S : Finset (Fin N)) := u ≤ ((S ∩ I).card : ℝ)-L*p
  have hL : 0 < L := by dsimp [L]; exact_mod_cast (show 0 < I.card by omega)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hNp).mpr (by exact_mod_cast hj)
  have hmoment : moment N j I θ ≤ Real.exp (L*(p*θ+θ^2/8)) := by
    have hb := BernoulliHoeffding.uncentered_mgf p θ hp0 hp1
    have hb0 : 0 ≤ 1-p+p*Real.exp θ := by positivity
    have hpow := pow_le_pow_left₀ hb0 hb I.card
    calc
      _ ≤ (1-p+p*Real.exp θ)^I.card := SamplingMomentBound.moment_le N j hN hj I θ hθ
      _ ≤ (Real.exp (p*θ+θ^2/8))^I.card := hpow
      _ = _ := by rw [← Real.exp_nat_mul]
  have hline : (∑ S ∈ sample N j, if E S then (1 : ℝ) else 0) ≤
      Real.exp (-θ*(L*p+u))*(∑ S ∈ sample N j, Real.exp (θ*((S ∩ I).card : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S hS
    by_cases hE : E S
    · rw [if_pos hE,← Real.exp_add]
      apply Real.one_le_exp
      have hh : L*p+u ≤ ((S ∩ I).card : ℝ) := by dsimp [E] at hE; linarith
      have hmul := mul_le_mul_of_nonneg_left hh hθ
      linarith
    · rw [if_neg hE]
      positivity
  have hcount : (∑ S ∈ sample N j, if E S then (1 : ℝ) else 0) =
      (((sample N j).filter E).card : ℝ) := by rw [← Finset.sum_filter]; simp
  rw [hcount] at hline
  have hmarkov : (((sample N j).filter E).card : ℝ)/(N.choose j : ℝ) ≤
      Real.exp (-θ*(L*p+u))*moment N j I θ := by
    have h := div_le_div_of_nonneg_right hline hden.le
    simpa only [moment,mul_div_assoc] using h
  have htail : (((sample N j).filter E).card : ℝ)/(N.choose j : ℝ) ≤ Real.exp (-2*u^2/I.card) := by
    calc
      _ ≤ Real.exp (-θ*(L*p+u))*moment N j I θ := hmarkov
      _ ≤ Real.exp (-θ*(L*p+u))*Real.exp (L*(p*θ+θ^2/8)) :=
        mul_le_mul_of_nonneg_left hmoment (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        dsimp [θ,L]
        field_simp [ne_of_gt hL] <;> ring
  have he : (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
      u ≤ ((S ∩ I).card : ℝ)-(I.card : ℝ)*((j : ℝ)/N)) = (sample N j).filter E := by
    ext S
    simp [sample,E,L,p,Finset.mem_powersetCard]
  rw [he]
  exact htail

end AC02Frege.SamplingTail
end

open AC02Frege

theorem solution (N j : ℕ) (hj : j ≤ N) (I : Finset (Fin N)) (hI : 1 ≤ I.card)
    (u : ℝ) (hu : 0 ≤ u) :
    ((((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card = j ∧
        u ≤ ((S ∩ I).card : ℝ) - (I.card : ℝ) * ((j : ℝ) / N))).card : ℕ) : ℝ)
        / (N.choose j : ℝ)
      ≤ Real.exp (-2 * u ^ 2 / I.card)  := by
  exact AC02Frege.SamplingTail.sampling_tail N j hj I hI u hu
