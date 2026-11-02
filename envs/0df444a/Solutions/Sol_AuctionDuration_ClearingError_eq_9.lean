-- Prove2me | solution 1 for AuctionDuration.ClearingError.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:29:21.95726+00:00
-- url     : https://prove2.me/submissions/515b4d2f-b67c-4e07-a86d-7ab7b7407619

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model
import Theorems.Thm_QueueingFundamentals_Foundations_poisson_count_cdf

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations
open scoped NNReal ENNReal

namespace ADEq9

/-- The counting process evaluated at a measurable random time is measurable. -/
theorem countingProcess_measurable_at {Ω : Type*} [MeasurableSpace Ω] (T : ℕ → Ω → ℝ)
    (hT : ∀ i, Measurable (T i)) (τ : Ω → ℝ) (hτ : Measurable τ) :
    Measurable (fun ω => countingProcess T (τ ω) ω) := by
  set A : Ω → Set ℕ := fun ω => {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ τ ω} with hA
  set F : Ω → ℝ≥0∞ := fun ω => ∑' n : ℕ, (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n with hF
  have hFm : Measurable F := by
    refine Measurable.ennreal_tsum (fun n => ?_)
    have hS : Measurable (arrivalTime T n) := by
      unfold arrivalTime
      exact Finset.measurable_sum _ (fun i _ => hT i)
    have hset : MeasurableSet {ω | n ∈ A ω} := by
      by_cases hn : 1 ≤ n
      · simp only [hA, Set.mem_setOf_eq, hn, true_and]
        exact measurableSet_le hS hτ
      · simp [hA, hn]
    have : (fun ω => (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n) =
        {ω | n ∈ A ω}.indicator (fun _ => 1) := by
      ext ω; simp [Set.indicator]
    rw [this]
    exact measurable_const.indicator hset
  have hFenc : ∀ ω, F ω = ((A ω).encard : ℝ≥0∞) := by
    intro ω
    rw [← ENNReal.tsum_set_one]
    show ∑' n : ℕ, (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n = _
    rw [← tsum_subtype (A ω) (fun _ => (1 : ℝ≥0∞))]
  apply measurable_to_countable'
  intro k
  have : (fun ω => countingProcess T (τ ω) ω) ⁻¹' {k} =
      F ⁻¹' ({((k : ℕ∞) : ℝ≥0∞)} ∪ (if k = 0 then {⊤} else ∅)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, hFenc]
    unfold countingProcess
    rw [Set.ncard_def]
    change ENat.toNat (A ω).encard = k ↔ _
    generalize (A ω).encard = e
    induction e using ENat.recTopCoe with
    | top =>
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk, eq_comm (a := 0)]
    | coe m =>
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk]
  rw [this]
  exact hFm ((measurableSet_singleton _).union (by split_ifs <;> simp))

end ADEq9

open AuctionDuration.ClearingError in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    (P (OmegaT X h)).toReal = 1 - Real.exp (-(p.mu * h)) * (p.nu / (p.nu + p.mu)) := by
  obtain ⟨hnu, hmu, -, -, -⟩ := hp
  obtain ⟨hPr, -, -, -, hA, hTm, hTlaw, -, -, -, -, -, -, -, -, hind⟩ := hX
  -- the arrival sequence as a single random element of `ℕ → ℝ`
  set Y : Ω → (ℕ → ℝ) := fun ω n => X.A n ω with hYdef
  have hY : Measurable Y := measurable_pi_lambda _ hA.measurable
  -- canonical counting process on the path space
  set C : ℝ × (ℕ → ℝ) → ℕ := fun q => countingProcess (fun n (a : ℕ → ℝ) => a n) (q.1 + h) q.2
    with hCdef
  have hC : Measurable C :=
    ADEq9.countingProcess_measurable_at (fun n (q : ℝ × (ℕ → ℝ)) => q.2 n)
      (fun n => (measurable_pi_apply n).comp measurable_snd) (fun q => q.1 + h)
      (measurable_fst.add_const h)
  have hNC : ∀ ω, Nmm X (tauCl X h ω) ω = C (X.T ω, Y ω) := fun ω => rfl
  set B : Set (ℝ × (ℕ → ℝ)) := C ⁻¹' {0} with hBdef
  have hB : MeasurableSet B := hC (measurableSet_singleton 0)
  have hOc : (OmegaT X h)ᶜ = (fun ω => (X.T ω, Y ω)) ⁻¹' B := by
    ext ω
    simp [OmegaT, hBdef, hNC]
  have hOm : MeasurableSet (OmegaT X h) := by
    rw [← compl_compl (OmegaT X h), hOc]
    exact ((hTm.prodMk hY) hB).compl
  -- independence of the opening time and the arrivals
  have hTY : IndepFun X.T Y P := by
    have h21 := hind.indep (show (2 : Fin 5) ≠ 1 by decide)
    simp only [Matrix.cons_val] at h21
    have e : MeasurableSpace.comap Y MeasurableSpace.pi = X.sigmaA := by
      simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      rfl
    show Indep (MeasurableSpace.comap X.T inferInstance) (MeasurableSpace.comap Y inferInstance) P
    rw [e]
    exact h21
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hTm.aemeasurable hY.aemeasurable).1 hTY
  -- the slice probabilities
  have hslice : ∀ t, 0 ≤ t → (P.map Y) (Prod.mk t ⁻¹' B) =
      ENNReal.ofReal (Real.exp (-(p.mu * (t + h)))) := by
    intro t ht
    rw [Measure.map_apply hY (measurable_prodMk_left hB)]
    have h0 := (poisson_count_cdf P p.mu hmu X.A hA 0 (t + h) (by linarith)).2.2
    have hset : Y ⁻¹' (Prod.mk t ⁻¹' B) = {ω | countingProcess X.A (t + h) ω = 0} := by
      ext ω; simp [hBdef, hCdef, Y]; rfl
    rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top P _), h0]
    simp
  have hcompl : P (OmegaT X h)ᶜ = ENNReal.ofReal (Real.exp (-(p.mu * h)) * (p.nu / (p.nu + p.mu))) := by
    rw [hOc, ← Measure.map_apply (hTm.prodMk hY) hB, hprod, Measure.prod_apply hB, hTlaw]
    rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (gammaPDF 1 p.nu) from (measurable_gammaPDFReal 1 p.nu).ennreal_ofReal)
      (measurable_measure_prodMk_left hB)]
    set a : ℝ := -(p.nu + p.mu) with ha
    have ha0 : a < 0 := by rw [ha]; linarith
    have hpt : ∀ t, (gammaPDF 1 p.nu * fun t => (P.map Y) (Prod.mk t ⁻¹' B)) t =
        (Set.Ici 0).indicator
          (fun t => ENNReal.ofReal (p.nu * Real.exp (-(p.mu * h)) * Real.exp (a * t))) t := by
      intro t
      rcases lt_or_ge t 0 with ht | ht
      · have : t ∉ Set.Ici (0 : ℝ) := by simpa using ht
        simp only [Pi.mul_apply, Set.indicator_of_notMem this, gammaPDF_of_neg ht, zero_mul]
      · rw [Set.indicator_of_mem (by simpa using ht), Pi.mul_apply, hslice t ht]
        have he : gammaPDF 1 p.nu t = exponentialPDF p.nu t := rfl
        rw [he, exponentialPDF_of_nonneg ht, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [ha, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        ring
    simp_rw [hpt]
    rw [lintegral_indicator measurableSet_Ici]
    have hint : IntegrableOn
        (fun t => p.nu * Real.exp (-(p.mu * h)) * Real.exp (a * t)) (Set.Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact (integrableOn_exp_mul_Ioi ha0 0).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (fun t => by positivity))]
    congr 1
    rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_exp_mul_Ioi ha0 0, ha]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  have hsum := prob_compl_eq_one_sub (μ := P) hOm
  rw [hcompl] at hsum
  have hfin : P (OmegaT X h) ≠ ⊤ := measure_ne_top P _
  have hle : P (OmegaT X h) ≤ 1 := prob_le_one
  have hq : 0 ≤ Real.exp (-(p.mu * h)) * (p.nu / (p.nu + p.mu)) := by positivity
  have := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_ofReal hq, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
    ENNReal.toReal_one] at this
  linarith
