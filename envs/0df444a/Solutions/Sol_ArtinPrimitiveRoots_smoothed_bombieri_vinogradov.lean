-- Prove2me | solution 1 for ArtinPrimitiveRoots.smoothed_bombieri_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T14:12:53.472971+00:00
-- url     : https://prove2.me/submissions/82cab236-5b1c-4b5a-9be6-8b2b4a814f1f

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_bombieri_vinogradov

namespace ArtinPrimitiveRoots.WFDsbv

section
open Real Finset Filter Topology MeasureTheory

/-- Indicator of primes in a residue class. -/
noncomputable def primeInd (q v : ℕ) (k : ℕ) : ℝ :=
  if k.Prime ∧ k ≡ v [MOD q] then 1 else 0

lemma primeCountingAP_eq_sum (t : ℝ) (q v : ℕ) :
    (primeCountingAP t q v : ℝ) = ∑ k ∈ Icc 0 ⌊t⌋₊, primeInd q v k := by
  unfold primeCountingAP primeInd
  rw [Finset.card_filter, Nat.cast_sum]
  have : Finset.range (⌊t⌋₊ + 1) = Icc 0 ⌊t⌋₊ := by
    ext k; simp
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma logIntegral_hasDerivAt {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt logIntegral (1 / log t) t := by
  have hc : ContinuousOn (fun s : ℝ => 1 / log s) (Set.Ioi 1) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_log.mono fun s hs => by
        simp only [Set.mem_Ioi] at hs; simp; linarith
    · intro s hs; simp only [Set.mem_Ioi] at hs
      exact (log_pos hs).ne'
  have hint : IntervalIntegrable (fun s : ℝ => 1 / log s) volume 2 t := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    simp only [Set.mem_Ioi]; linarith [hs.1]
  have hca : ContinuousAt (fun s : ℝ => 1 / log s) t :=
    hc.continuousAt (Ioi_mem_nhds (by linarith))
  unfold logIntegral
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hc.stronglyMeasurableAtFilter isOpen_Ioi t (by simp only [Set.mem_Ioi]; linarith)) hca

/-- Hypotheses on a smooth weight supported in `[T₁, T₂]`. -/
structure Weight (f : ℝ → ℝ) (T₁ T₂ : ℝ) : Prop where
  diff : Differentiable ℝ f
  cont : Continuous (deriv f)
  zero : ∀ t, t ≤ T₁ ∨ T₂ ≤ t → f t = 0 ∧ deriv f t = 0

lemma partial_summation {f : ℝ → ℝ} {T₁ T₂ : ℝ} (hw : Weight f T₁ T₂) (h2 : 2 ≤ T₁)
    (h12 : T₁ ≤ T₂) (q v : ℕ) :
    ∑ k ∈ Icc 0 ⌊T₂⌋₊, f k * primeInd q v k - (1 / (Nat.totient q : ℝ)) *
        ∫ t in T₁..T₂, f t * (1 / log t) =
      -∫ t in T₁..T₂, deriv f t *
        ((primeCountingAP t q v : ℝ) - logIntegral t / Nat.totient q) := by
  have habel := sum_mul_eq_sub_integral_mul (primeInd q v) (f := f) (b := T₂) (by linarith)
    (fun t _ => hw.diff t) hw.cont.integrableOn_Icc
  rw [(hw.zero T₂ (Or.inr le_rfl)).1, zero_mul, zero_sub] at habel
  rw [habel]
  have hset : ∫ t in Set.Ioc 0 T₂, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, primeInd q v k =
      ∫ t in T₁..T₂, deriv f t * (primeCountingAP t q v : ℝ) := by
    rw [intervalIntegral.integral_of_le h12]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Set.Ioc_subset_Ioc (by linarith : (0:ℝ) ≤ T₁) le_rfl)]
    · refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      simp only [primeCountingAP_eq_sum]
    · intro t ht
      simp only [Set.mem_sdiff, Set.mem_Ioc, not_and, not_le] at ht
      have : t ≤ T₁ := by
        by_contra h; exact absurd (ht.2 (lt_of_not_ge h)) (not_lt.mpr ht.1.2)
      rw [(hw.zero t (Or.inl this)).2, zero_mul]
  rw [hset]
  have hLi : ∀ t ∈ Set.uIcc T₁ T₂, HasDerivAt logIntegral (1 / log t) t := by
    intro t ht; rw [Set.uIcc_of_le h12] at ht; exact logIntegral_hasDerivAt (by linarith [ht.1])
  have hcl : ContinuousOn (fun t : ℝ => 1 / log t) (Set.uIcc T₁ T₂) := by
    intro t ht; rw [Set.uIcc_of_le h12] at ht
    refine (ContinuousAt.div continuousAt_const (continuousAt_log (by linarith [ht.1]))
      (log_pos (by linarith [ht.1])).ne').continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hLi
    (fun t _ => (hw.diff t).hasDerivAt) hcl.intervalIntegrable
    hw.cont.continuousOn.intervalIntegrable
  rw [(hw.zero T₂ (Or.inr le_rfl)).1, (hw.zero T₁ (Or.inl le_rfl)).1, mul_zero, mul_zero,
    sub_zero, zero_sub] at hibp
  have hLic : ContinuousOn logIntegral (Set.uIcc T₁ T₂) :=
    fun t ht => (hLi t ht).continuousAt.continuousWithinAt
  have hi1 : IntervalIntegrable (fun t => deriv f t * (primeCountingAP t q v : ℝ)) volume T₁ T₂ := by
    have := integrableOn_mul_sum_Icc (primeInd q v) (m := 0) (a := T₁) (b := T₂) (by linarith)
      hw.cont.integrableOn_Icc
    refine (IntegrableOn.intervalIntegrable ?_)
    rw [Set.uIcc_of_le h12]
    refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [primeCountingAP_eq_sum]
  have hi2 : IntervalIntegrable (fun t => deriv f t * (logIntegral t / Nat.totient q))
      volume T₁ T₂ :=
    (hw.cont.continuousOn.mul (hLic.div_const _)).intervalIntegrable
  have e1 : ∫ t in T₁..T₂, deriv f t *
        ((primeCountingAP t q v : ℝ) - logIntegral t / Nat.totient q) =
      (∫ t in T₁..T₂, deriv f t * (primeCountingAP t q v : ℝ)) -
        ∫ t in T₁..T₂, deriv f t * (logIntegral t / Nat.totient q) := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    congr 1; ext t; ring
  have e2 : ∫ t in T₁..T₂, deriv f t * (logIntegral t / Nat.totient q) =
      (1 / (Nat.totient q : ℝ)) * ∫ t in T₁..T₂, logIntegral t * deriv f t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext t; ring
  have e3 : ∫ t in T₁..T₂, f t * (1 / log t) = ∫ t in T₁..T₂, 1 / log t * f t := by
    congr 1; ext t; ring
  rw [e1, e2, hibp, e3]
  ring

lemma err_integrable {f : ℝ → ℝ} {T₁ T₂ : ℝ} (hw : Weight f T₁ T₂) (h2 : 2 ≤ T₁)
    (h12 : T₁ ≤ T₂) (q v : ℕ) :
    IntervalIntegrable (fun t => deriv f t *
        ((primeCountingAP t q v : ℝ) - logIntegral t / Nat.totient q)) volume T₁ T₂ := by
  have hLi : ∀ t ∈ Set.uIcc T₁ T₂, HasDerivAt logIntegral (1 / log t) t := by
    intro t ht; rw [Set.uIcc_of_le h12] at ht; exact logIntegral_hasDerivAt (by linarith [ht.1])
  have hLic : ContinuousOn logIntegral (Set.uIcc T₁ T₂) :=
    fun t ht => (hLi t ht).continuousAt.continuousWithinAt
  have hi1 : IntervalIntegrable (fun t => deriv f t * (primeCountingAP t q v : ℝ)) volume T₁ T₂ := by
    have := integrableOn_mul_sum_Icc (primeInd q v) (m := 0) (a := T₁) (b := T₂) (by linarith)
      hw.cont.integrableOn_Icc
    refine (IntegrableOn.intervalIntegrable ?_)
    rw [Set.uIcc_of_le h12]
    refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [primeCountingAP_eq_sum]
  have hi2 : IntervalIntegrable (fun t => deriv f t * (logIntegral t / Nat.totient q))
      volume T₁ T₂ :=
    (hw.cont.continuousOn.mul (hLic.div_const _)).intervalIntegrable
  refine (hi1.sub hi2).congr ?_
  intro t _
  simp only; ring

lemma smoothed_bv (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (T₁ T₂ B : ℝ), Weight f T₁ T₂ → 2 ≤ T₁ → T₁ ≤ T₂ →
      (∀ t, |deriv f t| ≤ B) → ∀ (S : Finset ℕ) (v : ℕ → ℕ),
      (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) < T₁ ^ (1 / 2 - η) ∧ Nat.Coprime (v q) q) →
      ∑ q ∈ S, |∑ k ∈ Icc 0 ⌊T₂⌋₊, f k * primeInd q (v q) k - (1 / (Nat.totient q : ℝ)) *
          ∫ t in T₁..T₂, f t * (1 / log t)| ≤
        C * (B * ((T₂ - T₁) * (T₂ * log T₁ ^ (-A')))) := by
  obtain ⟨C₀, hC₀⟩ := bombieri_vinogradov A' η hA' hη
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro f T₁ T₂ B hw h2 h12 hB S v hS
  set E : ℕ → ℝ → ℝ := fun q t => deriv f t *
    ((primeCountingAP t q (v q) : ℝ) - logIntegral t / Nat.totient q) with hE
  have step1 : ∀ q ∈ S, |∑ k ∈ Icc 0 ⌊T₂⌋₊, f k * primeInd q (v q) k -
      (1 / (Nat.totient q : ℝ)) * ∫ t in T₁..T₂, f t * (1 / log t)| ≤
        ∫ t in T₁..T₂, |E q t| := by
    intro q _
    rw [partial_summation hw h2 h12 q (v q), abs_neg]
    exact intervalIntegral.abs_integral_le_integral_abs h12
  refine (Finset.sum_le_sum step1).trans ?_
  have hint : ∀ q ∈ S, IntervalIntegrable (fun t => |E q t|) volume T₁ T₂ :=
    fun q _ => (err_integrable hw h2 h12 q (v q)).abs
  rw [← intervalIntegral.integral_finsetSum hint]
  set K := max C₀ 0 * (B * (T₂ * log T₁ ^ (-A'))) with hK
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hpt : ∀ t ∈ Set.Icc T₁ T₂, ∑ q ∈ S, |E q t| ≤ K := by
    intro t ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    let v' : ℕ → ℕ := fun q => if q ∈ S then v q else 1
    have hv' : ∀ q, Nat.Coprime (v' q) q := by
      intro q; by_cases hq : q ∈ S
      · simp only [v', if_pos hq]; exact (hS q hq).2.2
      · simp only [v', if_neg hq]; exact Nat.coprime_one_left q
    have hbv := hC₀ t ht2 v' hv'
    have hsub : S ⊆ (Finset.range ⌈t ^ (1 / 2 - η)⌉₊).filter
        (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < t ^ (1 / 2 - η)) := by
      intro q hq
      obtain ⟨h1, hlt, -⟩ := hS q hq
      have : (q : ℝ) < t ^ (1 / 2 - η) := hlt.trans_le
        (Real.rpow_le_rpow (by linarith) ht.1 (by linarith))
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_ceil.mpr this, h1, this⟩
    have h3 : ∑ q ∈ S, |(primeCountingAP t q (v q) : ℝ) - logIntegral t / Nat.totient q| ≤
        C₀ * (t * log t ^ (-A')) := by
      refine le_trans ?_ hbv
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun q hq => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _)
      simp only [v', if_pos hq]
    have hlog : log t ^ (-A') ≤ log T₁ ^ (-A') :=
      Real.rpow_le_rpow_of_nonpos (log_pos (by linarith)) (log_le_log (by linarith) ht.1)
        (by linarith)
    have hlogpos : 0 ≤ log t ^ (-A') := Real.rpow_nonneg (log_nonneg (by linarith)) _
    have h4 : C₀ * (t * log t ^ (-A')) ≤ max C₀ 0 * (T₂ * log T₁ ^ (-A')) := by
      calc C₀ * (t * log t ^ (-A')) ≤ max C₀ 0 * (t * log t ^ (-A')) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C₀ 0 * (T₂ * log T₁ ^ (-A')) :=
            mul_le_mul_of_nonneg_left (mul_le_mul ht.2 hlog hlogpos (by linarith))
              (le_max_right _ _)
    calc ∑ q ∈ S, |E q t| = |deriv f t| * ∑ q ∈ S,
          |(primeCountingAP t q (v q) : ℝ) - logIntegral t / Nat.totient q| := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_
          simp only [hE, abs_mul]
      _ ≤ B * (max C₀ 0 * (T₂ * log T₁ ^ (-A'))) :=
          mul_le_mul (hB t) (h3.trans h4) (Finset.sum_nonneg fun _ _ => abs_nonneg _) hB0
      _ = K := by rw [hK]; ring
  have hmono := intervalIntegral.integral_mono_on h12
    (by
      have := IntervalIntegrable.sum S hint
      refine this.congr fun x _ => ?_
      simp [Finset.sum_apply]) intervalIntegrable_const hpt
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul, hK]; ring

end
open Real in
theorem smoothed_bombieri_vinogradov_proof (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (T₁ T₂ B : ℝ), Differentiable ℝ f → Continuous (deriv f) →
      (∀ t, t ≤ T₁ ∨ T₂ ≤ t → f t = 0 ∧ deriv f t = 0) → 2 ≤ T₁ → T₁ ≤ T₂ →
      (∀ t, |deriv f t| ≤ B) → ∀ (S : Finset ℕ) (v : ℕ → ℕ),
      (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) < T₁ ^ (1 / 2 - η) ∧ Nat.Coprime (v q) q) →
      ∑ q ∈ S, |∑ k ∈ (Finset.Icc 0 ⌊T₂⌋₊).filter (fun k => k.Prime ∧ k ≡ v q [MOD q]), f k -
          (1 / (Nat.totient q : ℝ)) * ∫ t in T₁..T₂, f t * (1 / log t)| ≤
        C * (B * ((T₂ - T₁) * (T₂ * log T₁ ^ (-A')))) := by
  obtain ⟨C, hC0, hC⟩ := smoothed_bv A' η hA' hη hη2
  refine ⟨C, hC0, fun f T₁ T₂ B hd hc hz h2 h12 hB S v hS => ?_⟩
  convert hC f T₁ T₂ B ⟨hd, hc, hz⟩ h2 h12 hB S v hS using 4 with q _
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold primeInd
  split_ifs <;> simp

end ArtinPrimitiveRoots.WFDsbv

open ArtinPrimitiveRoots ArtinPrimitiveRoots.WFDsbv Real in
theorem solution (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (T₁ T₂ B : ℝ), Differentiable ℝ f → Continuous (deriv f) →
      (∀ t, t ≤ T₁ ∨ T₂ ≤ t → f t = 0 ∧ deriv f t = 0) → 2 ≤ T₁ → T₁ ≤ T₂ →
      (∀ t, |deriv f t| ≤ B) → ∀ (S : Finset ℕ) (v : ℕ → ℕ),
      (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) < T₁ ^ (1 / 2 - η) ∧ Nat.Coprime (v q) q) →
      ∑ q ∈ S, |∑ k ∈ (Finset.Icc 0 ⌊T₂⌋₊).filter (fun k => k.Prime ∧ k ≡ v q [MOD q]), f k -
          (1 / (Nat.totient q : ℝ)) * ∫ t in T₁..T₂, f t * (1 / log t)| ≤
        C * (B * ((T₂ - T₁) * (T₂ * log T₁ ^ (-A')))) := by
  apply ArtinPrimitiveRoots.WFDsbv.smoothed_bombieri_vinogradov_proof <;> assumption
