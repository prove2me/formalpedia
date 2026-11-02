-- Prove2me | solution 1 for AuctionDuration.ClearingError.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:17:52.506481+00:00
-- url     : https://prove2.me/submissions/0a9c98bf-d755-4790-8110-29725aeab136

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model
import Theorems.Thm_QueueingFundamentals_Foundations_poisson_count_cdf

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations AuctionDuration.ClearingError
open scoped NNReal ENNReal

namespace ADCore

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

theorem measurable_sum_range_var {α : Type*} [MeasurableSpace α] (n : α → ℕ) (hn : Measurable n)
    (f : ℕ → α → ℝ) (hf : ∀ k, Measurable (f k)) :
    Measurable (fun x => ∑ k ∈ Finset.range (n x), f k x) := by
  have hΨ : Measurable (fun q : α × ℕ => ∑ k ∈ Finset.range q.2, f k q.1) :=
    measurable_from_prod_countable_left (fun m => by
      simp only
      exact Finset.measurable_sum _ (fun k _ => hf k))
  exact hΨ.comp (measurable_id.prodMk hn)

/-- the counting function on the path space -/
noncomputable def cnt (t : ℝ) (y : ℕ → ℝ) : ℕ := countingProcess (fun n (y : ℕ → ℝ) => y n) t y

/-- arrival epochs on the path space -/
noncomputable def sT (k : ℕ) (y : ℕ → ℝ) : ℝ := arrivalTime (fun n (y : ℕ → ℝ) => y n) k y

noncomputable def Aφ {Ω : Type*} (p : Params) (X : Auction Ω) (t : ℝ) (y : ℕ → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (cnt t y), (Peff p X (sT (k + 1) y) ω - Peff p X t ω)

noncomputable def Bφ {Ω : Type*} (X : Auction Ω) (t : ℝ) (y : ℕ → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (cnt t y), X.g k ω

noncomputable def Hφ {Ω : Type*} (a b c : ℝ) (p : Params) (X : Auction Ω) (t : ℝ) (y : ℕ → ℝ)
    (ω : Ω) : ℝ :=
  if 0 < cnt t y then
    ((a * Aφ p X t y ω + b * Bφ X t y ω + c * (X.J ω / p.K)) / (cnt t y : ℝ)) ^ 2 else 0

theorem measurable_sT (k : ℕ) : Measurable (sT k) := by
  unfold sT arrivalTime
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem measurable_Hφ {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (a b c : ℝ) (p : Params) (X : Auction Ω)
    (hWc : ∀ ω, Continuous fun s => X.W s ω) (hW : ∀ s, Measurable (X.W s))
    (hg : ∀ k, Measurable (X.g k)) (hJ : Measurable X.J)
    (τ : β → ℝ) (hτ : Measurable τ) (υ : β → ℕ → ℝ) (hυ : Measurable υ) :
    Measurable (fun q : β × Ω => Hφ a b c p X (τ q.1) (υ q.1) q.2) := by
  have hWu : Measurable (Function.uncurry X.W) :=
    measurable_uncurry_of_continuous_of_measurable hWc hW
  have hPeff : ∀ σ : β × Ω → ℝ, Measurable σ →
      Measurable (fun q : β × Ω => Peff p X (σ q) q.2) := by
    intro σ hσ
    unfold Peff
    exact measurable_const.add (measurable_const.mul
      (hWu.comp ((measurable_real_toNNReal.comp hσ).prodMk measurable_snd)))
  have hn : Measurable (fun q : β × Ω => cnt (τ q.1) (υ q.1)) := by
    unfold cnt
    exact countingProcess_measurable_at (fun n (q : β × Ω) => υ q.1 n)
      (fun n => (measurable_pi_apply n).comp (hυ.comp measurable_fst)) (fun q => τ q.1)
      (hτ.comp measurable_fst)
  have hA : Measurable (fun q : β × Ω => Aφ p X (τ q.1) (υ q.1) q.2) := by
    unfold Aφ
    exact measurable_sum_range_var _ hn _ (fun k =>
      (hPeff _ ((measurable_sT (k + 1)).comp (hυ.comp measurable_fst))).sub
        (hPeff _ (hτ.comp measurable_fst)))
  have hB : Measurable (fun q : β × Ω => Bφ X (τ q.1) (υ q.1) q.2) := by
    unfold Bφ
    exact measurable_sum_range_var _ hn _ (fun k => (hg k).comp measurable_snd)
  unfold Hφ
  refine Measurable.ite (hn (measurableSet_Ioi (a := 0))) ?_ measurable_const
  exact ((((measurable_const.mul hA).add (measurable_const.mul hB)).add
    (measurable_const.mul ((hJ.comp measurable_snd).div_const _))).div
    (measurable_from_nat.comp hn)).pow_const 2


theorem integrable_mul_of_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A B : Ω → ℝ}
    (hA : MemLp A 2 P) (hB : MemLp B 2 P) : Integrable (fun ω => A ω * B ω) P :=
  hA.integrable_mul hB

theorem indepFun_of_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ P) {A B : Ω → ℝ}
    (hA : Measurable[m₁] A) (hB : Measurable[m₂] B) : IndepFun A B P :=
  indep_of_indep_of_le_right (indep_of_indep_of_le_left h hA.comap_le) hB.comap_le

theorem integral_sq_add3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B C : Ω → ℝ) (hA : MemLp A 2 P) (hB : MemLp B 2 P) (hC : MemLp C 2 P)
    (hAB : IndepFun A B P) (hAC : IndepFun A C P) (hBC : IndepFun B C P)
    (hA0 : ∫ ω, A ω ∂P = 0) (hB0 : ∫ ω, B ω ∂P = 0) :
    ∫ ω, (A ω + B ω + C ω) ^ 2 ∂P =
      ∫ ω, A ω ^ 2 ∂P + ∫ ω, B ω ^ 2 ∂P + ∫ ω, C ω ^ 2 ∂P := by
  have e : ∀ ω, (A ω + B ω + C ω) ^ 2 = (A ω ^ 2 + B ω ^ 2 + C ω ^ 2) +
      (2 * (A ω * B ω) + 2 * (A ω * C ω) + 2 * (B ω * C ω)) := fun ω => by ring
  simp_rw [e]
  have iA := hA.integrable_sq
  have iB := hB.integrable_sq
  have iC := hC.integrable_sq
  have iAB := integrable_mul_of_L2 hA hB
  have iAC := integrable_mul_of_L2 hA hC
  have iBC := integrable_mul_of_L2 hB hC
  have i1 : Integrable (fun ω => A ω ^ 2 + B ω ^ 2 + C ω ^ 2) P := (iA.add iB).add iC
  have i2 : Integrable (fun ω => 2 * (A ω * B ω) + 2 * (A ω * C ω) + 2 * (B ω * C ω)) P :=
    ((iAB.const_mul 2).add (iAC.const_mul 2)).add (iBC.const_mul 2)
  have i3 : Integrable (fun ω => A ω ^ 2 + B ω ^ 2) P := iA.add iB
  have i4 : Integrable (fun ω => 2 * (A ω * B ω) + 2 * (A ω * C ω)) P :=
    (iAB.const_mul 2).add (iAC.const_mul 2)
  rw [integral_add i1 i2, integral_add i3 iC, integral_add iA iB, integral_add i4 (iBC.const_mul 2),
    integral_add (iAB.const_mul 2) (iAC.const_mul 2)]
  simp only [integral_const_mul]
  rw [hAB.integral_fun_mul_eq_mul_integral hA.aestronglyMeasurable hB.aestronglyMeasurable,
    hAC.integral_fun_mul_eq_mul_integral hA.aestronglyMeasurable hC.aestronglyMeasurable,
    hBC.integral_fun_mul_eq_mul_integral hB.aestronglyMeasurable hC.aestronglyMeasurable]
  simp [hA0, hB0]

theorem integral_sq_sum_iid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ) (hg : iIndepFun g P) (hL : ∀ k, MemLp (g k) 2 P)
    (h0 : ∀ k, ∫ ω, g k ω ∂P = 0) (σ2 : ℝ) (h2 : ∀ k, ∫ ω, g k ω ^ 2 ∂P = σ2) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, g k ω) ^ 2 ∂P = n * σ2 := by
  have e : ∀ ω, (∑ k ∈ Finset.range n, g k ω) ^ 2 =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k ω * g l ω := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _
    (fun l _ => integrable_mul_of_L2 (hL k) (hL l)))]
  have : ∀ k ∈ Finset.range n, ∫ ω, ∑ l ∈ Finset.range n, g k ω * g l ω ∂P = σ2 := by
    intro k hk
    rw [integral_finset_sum _ (fun l _ => integrable_mul_of_L2 (hL k) (hL l))]
    rw [Finset.sum_eq_single k]
    · rw [← h2 k]; congr 1; ext ω; ring
    · intro l _ hlk
      rw [(hg.indepFun (Ne.symm hlk)).integral_fun_mul_eq_mul_integral
        (hL k).aestronglyMeasurable (hL l).aestronglyMeasurable, h0 k, zero_mul]
    · intro h; exact absurd hk h
  rw [Finset.sum_congr rfl this]
  simp


/-- Facts extracted from the model. -/
structure ModelFacts {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω)
    (X : Auction Ω) : Prop where
  memW : ∀ s, MemLp (X.W s) 2 P
  meanW : ∀ s, ∫ ω, X.W s ω ∂P = 0
  memg : ∀ k, MemLp (X.g k) 2 P
  meang : ∀ k, ∫ ω, X.g k ω ∂P = 0
  sqg : ∀ k, ∫ ω, X.g k ω ^ 2 ∂P = p.sigma ^ 2
  measW : ∀ s, Measurable[X.sigmaW] (X.W s)
  measg : ∀ k, Measurable[X.sigmaG] (X.g k)
  measJ : Measurable[X.sigmaJ] X.J
  iWG : Indep X.sigmaW X.sigmaG P
  iWJ : Indep X.sigmaW X.sigmaJ P
  iGJ : Indep X.sigmaG X.sigmaJ P
  indg : iIndepFun X.g P
  memJ : MemLp X.J 2 P
  sqinc : ∀ s t : ℝ≥0, ∫ ω, (X.W s ω - X.W t ω) ^ 2 ∂P = |(s : ℝ) - t|
  mulW : ∀ s t : ℝ≥0, ∫ ω, X.W s ω * X.W t ω ∂P = min (s : ℝ) t

theorem modelFacts {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω) (X : Auction Ω)
    (hX : IsModel p P X) : ModelFacts p P X := by
  obtain ⟨hPr, hBM, hWc, hWm, hA, hTm, hTlaw, hgm, hgind, hgid, hg0L, hg0mean, hgvar, hJm, hJL,
    hind⟩ := hX
  refine ⟨fun s => (hBM.isGaussianProcess.hasGaussianLaw_eval s).memLp_two,
    fun s => hBM.integral_eval s, fun k => (hgid k).symm.memLp_snd hg0L,
    fun k => by rw [(hgid k).integral_eq]; exact hg0mean, fun k => ?_,
    fun s => measurable_iff_comap_le.2 (le_iSup (fun t => MeasurableSpace.comap (X.W t) _) s),
    fun k => measurable_iff_comap_le.2 (le_iSup (fun t => MeasurableSpace.comap (X.g t) _) k),
    measurable_iff_comap_le.2 le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ∫ ω, X.g k ω ^ 2 ∂P = ∫ ω, X.g 0 ω ^ 2 ∂P := by
      have := ((hgid k).comp (measurable_id.pow_const 2)).integral_eq
      simpa [Function.comp_def] using this
    rw [e, ← variance_of_integral_eq_zero (hgm 0).aemeasurable hg0mean, hgvar]
  · have := hind.indep (show (0 : Fin 5) ≠ 3 by decide); simpa using this
  · have := hind.indep (show (0 : Fin 5) ≠ 4 by decide); simpa using this
  · have := hind.indep (show (3 : Fin 5) ≠ 4 by decide); simpa using this
  · exact hgind
  · exact hJL
  · intro s t
    have hl := hBM.hasLaw_sub s t
    have hv := hl.variance_eq
    rw [variance_id_gaussianReal] at hv
    have hm : ∫ ω, (X.W s - X.W t) ω ∂P = 0 := by
      simp only [Pi.sub_apply]
      rw [integral_sub (hBM.integrable_eval s) (hBM.integrable_eval t), hBM.integral_eval,
        hBM.integral_eval, sub_zero]
    rw [variance_of_integral_eq_zero ((hWm s).sub (hWm t)).aemeasurable hm] at hv
    simp only [Pi.sub_apply] at hv
    rw [hv]
    simp [NNReal.nndist_eq, Real.dist_eq]
  · intro s t
    have hc := hBM.covariance_eval s t
    rw [covariance_eq_sub (hBM.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      (hBM.isGaussianProcess.hasGaussianLaw_eval t).memLp_two, hBM.integral_eval,
      hBM.integral_eval, mul_zero, sub_zero] at hc
    simpa using hc


theorem memLp_Peff_sub {Ω : Type*} [MeasurableSpace Ω] {p : Params} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Auction Ω} (hF : ModelFacts p P X) (s t : ℝ) :
    MemLp (fun ω => Peff p X s ω - Peff p X t ω) 2 P ∧
    ∫ ω, (Peff p X s ω - Peff p X t ω) ∂P = 0 ∧
    Measurable[X.sigmaW] (fun ω => Peff p X s ω - Peff p X t ω) := by
  have e : (fun ω => Peff p X s ω - Peff p X t ω) =
      fun ω => p.sigmaF * X.W s.toNNReal ω - p.sigmaF * X.W t.toNNReal ω := by
    ext ω; unfold Peff; ring
  rw [e]
  refine ⟨((hF.memW _).const_mul _).sub ((hF.memW _).const_mul _), ?_,
    ((hF.measW _).const_mul _).sub ((hF.measW _).const_mul _)⟩
  rw [integral_sub (((hF.memW _).const_mul _).integrable one_le_two)
    (((hF.memW _).const_mul _).integrable one_le_two), integral_const_mul, integral_const_mul,
    hF.meanW, hF.meanW]
  ring

theorem integral_Hφ {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Auction Ω) (hF : ModelFacts p P X) (a b c t : ℝ)
    (y : ℕ → ℝ) :
    Integrable (Hφ a b c p X t y) P ∧
    ∫ ω, Hφ a b c p X t y ω ∂P = if 0 < cnt t y then
      (a ^ 2 * ∫ ω, Aφ p X t y ω ^ 2 ∂P + b ^ 2 * ((cnt t y : ℝ) * p.sigma ^ 2) +
        c ^ 2 * ((∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2)) / (cnt t y : ℝ) ^ 2 else 0 := by
  by_cases hn : 0 < cnt t y
  swap
  · have : Hφ a b c p X t y = fun _ => 0 := by ext ω; simp [Hφ, hn]
    rw [this]; simp [hn]
  set n := cnt t y with hndef
  have hAL : MemLp (Aφ p X t y) 2 P := by
    unfold Aφ
    exact memLp_finset_sum _ (fun k _ => (memLp_Peff_sub hF _ _).1)
  have hA0 : ∫ ω, Aφ p X t y ω ∂P = 0 := by
    unfold Aφ
    rw [integral_finset_sum _ (fun k _ => ((memLp_Peff_sub hF _ _).1).integrable one_le_two)]
    exact Finset.sum_eq_zero (fun k _ => (memLp_Peff_sub hF _ _).2.1)
  have hAm : Measurable[X.sigmaW] (Aφ p X t y) := by
    unfold Aφ
    exact Finset.measurable_sum _ (fun k _ => (memLp_Peff_sub hF _ _).2.2)
  have hBL : MemLp (Bφ X t y) 2 P := by
    unfold Bφ
    exact memLp_finset_sum _ (fun k _ => hF.memg k)
  have hB0 : ∫ ω, Bφ X t y ω ∂P = 0 := by
    unfold Bφ
    rw [integral_finset_sum _ (fun k _ => (hF.memg k).integrable one_le_two)]
    exact Finset.sum_eq_zero (fun k _ => hF.meang k)
  have hBm : Measurable[X.sigmaG] (Bφ X t y) := by
    unfold Bφ
    exact Finset.measurable_sum _ (fun k _ => hF.measg k)
  have hB2 : ∫ ω, Bφ X t y ω ^ 2 ∂P = n * p.sigma ^ 2 := by
    unfold Bφ
    exact integral_sq_sum_iid P X.g hF.indg hF.memg hF.meang _ hF.sqg n
  have hCL : MemLp (fun ω => c * (X.J ω / p.K)) 2 P := by
    have := hF.memJ.const_mul (c / p.K)
    convert this using 2 with ω
    ring
  have key := integral_sq_add3 P (fun ω => a * Aφ p X t y ω) (fun ω => b * Bφ X t y ω)
    (fun ω => c * (X.J ω / p.K)) (hAL.const_mul a) (hBL.const_mul b)
    hCL
    (indepFun_of_le hF.iWG (hAm.const_mul a) (hBm.const_mul b))
    (indepFun_of_le hF.iWJ (hAm.const_mul a) ((hF.measJ.div_const _).const_mul c))
    (indepFun_of_le hF.iGJ (hBm.const_mul b) ((hF.measJ.div_const _).const_mul c))
    (by rw [integral_const_mul, hA0, mul_zero]) (by rw [integral_const_mul, hB0, mul_zero])
  have hsum : MemLp (fun ω => a * Aφ p X t y ω + b * Bφ X t y ω + c * (X.J ω / p.K)) 2 P :=
    ((hAL.const_mul a).add (hBL.const_mul b)).add hCL
  have hH : Hφ a b c p X t y = fun ω =>
      (a * Aφ p X t y ω + b * Bφ X t y ω + c * (X.J ω / p.K)) ^ 2 / (n : ℝ) ^ 2 := by
    ext ω; simp only [Hφ]; rw [if_pos hn, div_pow]
  rw [hH]
  refine ⟨hsum.integrable_sq.div_const _, ?_⟩
  rw [integral_div, key, if_pos hn, ← hB2]
  congr 1
  have e1 : ∫ ω, (a * Aφ p X t y ω) ^ 2 ∂P = a ^ 2 * ∫ ω, Aφ p X t y ω ^ 2 ∂P := by
    rw [← integral_const_mul]; congr 1; ext ω; ring
  have e2 : ∫ ω, (b * Bφ X t y ω) ^ 2 ∂P = b ^ 2 * ∫ ω, Bφ X t y ω ^ 2 ∂P := by
    rw [← integral_const_mul]; congr 1; ext ω; ring
  have e3 : ∫ ω, (c * (X.J ω / p.K)) ^ 2 ∂P = c ^ 2 * ((∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2) := by
    rw [← integral_div, ← integral_const_mul]; congr 1; ext ω; ring
  rw [e1, e2, e3]


theorem sT_bounds (t : ℝ) (y : ℕ → ℝ) (hy : ∀ i, 0 < y i) (k : ℕ) (hk : k < cnt t y) :
    0 < sT (k + 1) y ∧ sT (k + 1) y ≤ t := by
  have hmono : ∀ m m', m ≤ m' → sT m y ≤ sT m' y := by
    intro m m' hmm
    unfold sT arrivalTime
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmm)
      (fun i _ _ => (hy i).le)
  refine ⟨?_, ?_⟩
  · unfold sT arrivalTime
    exact Finset.sum_pos (fun i _ => hy i) ⟨0, by simp⟩
  · by_contra hcon
    push_neg at hcon
    have hpos : 0 < cnt t y := lt_of_le_of_lt (Nat.zero_le k) hk
    unfold cnt countingProcess at hk hpos
    set S := {n : ℕ | 1 ≤ n ∧ arrivalTime (fun n (y : ℕ → ℝ) => y n) n y ≤ t} with hS
    have hsub : S ⊆ (Finset.Icc 1 k : Set ℕ) := by
      intro m hm
      simp only [hS, Set.mem_setOf_eq] at hm
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hm.1, ?_⟩
      by_contra hmk
      push_neg at hmk
      have := hmono (k + 1) m hmk
      have h2 : sT m y ≤ t := hm.2
      linarith
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega

theorem integral_Aφ_sq_le {Ω : Type*} [MeasurableSpace Ω] {p : Params} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Auction Ω} (hF : ModelFacts p P X) (t : ℝ) (y : ℕ → ℝ)
    (hy : ∀ i, 0 < y i) :
    ∫ ω, Aφ p X t y ω ^ 2 ∂P ≤ (cnt t y : ℝ) ^ 2 * (p.sigmaF ^ 2 * max t 0) := by
  set n := cnt t y with hn
  have hD : ∀ k ∈ Finset.range n,
      ∫ ω, (Peff p X (sT (k + 1) y) ω - Peff p X t ω) ^ 2 ∂P ≤ p.sigmaF ^ 2 * max t 0 := by
    intro k hk
    have hb := sT_bounds t y hy k (Finset.mem_range.1 hk)
    have e : ∀ ω, (Peff p X (sT (k + 1) y) ω - Peff p X t ω) ^ 2 =
        p.sigmaF ^ 2 * (X.W (sT (k + 1) y).toNNReal ω - X.W t.toNNReal ω) ^ 2 := by
      intro ω; unfold Peff; ring
    simp_rw [e]
    rw [integral_const_mul, hF.sqinc]
    have h1 : ((sT (k + 1) y).toNNReal : ℝ) = sT (k + 1) y := Real.coe_toNNReal _ hb.1.le
    have h2 : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ (hb.1.le.trans hb.2)
    rw [h1, h2, abs_of_nonpos (by linarith), max_eq_left (hb.1.le.trans hb.2)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [hb.1]
  have hCS : ∀ ω, Aφ p X t y ω ^ 2 ≤
      (n : ℝ) * ∑ k ∈ Finset.range n, (Peff p X (sT (k + 1) y) ω - Peff p X t ω) ^ 2 := by
    intro ω
    unfold Aφ
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
      (f := fun k => Peff p X (sT (k + 1) y) ω - Peff p X t ω)
    simpa using this
  have hint : ∀ k, Integrable (fun ω => (Peff p X (sT (k + 1) y) ω - Peff p X t ω) ^ 2) P :=
    fun k => (memLp_Peff_sub hF _ _).1.integrable_sq
  calc ∫ ω, Aφ p X t y ω ^ 2 ∂P
      ≤ ∫ ω, (n : ℝ) * ∑ k ∈ Finset.range n,
          (Peff p X (sT (k + 1) y) ω - Peff p X t ω) ^ 2 ∂P := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun ω => sq_nonneg _))
        · exact (integrable_finset_sum _ (fun k _ => hint k)).const_mul _
        · exact ae_of_all _ hCS
    _ = (n : ℝ) * ∑ k ∈ Finset.range n,
          ∫ ω, (Peff p X (sT (k + 1) y) ω - Peff p X t ω) ^ 2 ∂P := by
        rw [integral_const_mul, integral_finset_sum _ (fun k _ => hint k)]
    _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, p.sigmaF ^ 2 * max t 0 := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hD) (Nat.cast_nonneg _)
    _ = (n : ℝ) ^ 2 * (p.sigmaF ^ 2 * max t 0) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring


/-- σ-algebra of everything except the clock: Brownian motion, noises, imbalance. -/
abbrev sigG {Ω : Type*} (X : Auction Ω) : MeasurableSpace Ω :=
  ⨆ i ∈ ({0, 3, 4} : Set (Fin 5)), ![X.sigmaW, X.sigmaA, X.sigmaT, X.sigmaG, X.sigmaJ] i

abbrev sigH {Ω : Type*} (X : Auction Ω) : MeasurableSpace Ω :=
  ⨆ i ∈ ({1, 2} : Set (Fin 5)), ![X.sigmaW, X.sigmaA, X.sigmaT, X.sigmaG, X.sigmaJ] i

/-- the arrival sequence -/
def Yv {Ω : Type*} (X : Auction Ω) (ω : Ω) : ℕ → ℝ := fun n => X.A n ω

structure Frz {Ω : Type*} [mΩ : MeasurableSpace Ω] (p : Params) (P : Measure Ω)
    (X : Auction Ω) : Prop where
  hG : sigG X ≤ mΩ
  hWc : ∀ ω, Continuous fun s => X.W s ω
  hWG : ∀ s, Measurable[sigG X] (X.W s)
  hgG : ∀ k, Measurable[sigG X] (X.g k)
  hJG : Measurable[sigG X] X.J
  hY : Measurable (Yv X)
  hT : Measurable X.T
  indZ : Indep (MeasurableSpace.comap (fun ω => (X.T ω, Yv X ω)) inferInstance) (sigG X) P
  indY : Indep (MeasurableSpace.comap (Yv X) inferInstance) (sigG X) P
  lawZ : P.map (fun ω => (X.T ω, Yv X ω)) = (expMeasure p.nu).prod (P.map (Yv X))
  aeY : ∀ᵐ y ∂(P.map (Yv X)), ∀ i, 0 < y i

theorem frz {Ω : Type*} [mΩ : MeasurableSpace Ω] (p : Params) (hp : p.Standing) (P : Measure Ω)
    (X : Auction Ω) (hX : IsModel p P X) : Frz p P X := by
  obtain ⟨hnu, hmu, -, -, -⟩ := hp
  obtain ⟨hPr, hBM, hWc, hWm, hA, hTm, hTlaw, hgm, hgind, hgid, hg0L, hg0mean, hgvar, hJm, hJL,
    hind⟩ := hX
  set m : Fin 5 → MeasurableSpace Ω := ![X.sigmaW, X.sigmaA, X.sigmaT, X.sigmaG, X.sigmaJ] with hm
  have hle : ∀ i, m i ≤ mΩ := by
    intro i
    fin_cases i
    · exact iSup_le fun t => (hWm t).comap_le
    · exact iSup_le fun k => (hA.measurable k).comap_le
    · exact hTm.comap_le
    · exact iSup_le fun k => (hgm k).comap_le
    · exact hJm.comap_le
  have hGi : ∀ i ∈ ({0, 3, 4} : Set (Fin 5)), m i ≤ sigG X := fun i hi =>
    le_iSup₂ (f := fun i (_ : i ∈ ({0, 3, 4} : Set (Fin 5))) => m i) i hi
  have hHi : ∀ i ∈ ({1, 2} : Set (Fin 5)), m i ≤ sigH X := fun i hi =>
    le_iSup₂ (f := fun i (_ : i ∈ ({1, 2} : Set (Fin 5))) => m i) i hi
  have hindHG : Indep (sigH X) (sigG X) P :=
    indep_iSup_of_disjoint hle hind (by
      rw [Set.disjoint_left]; intro i hi1 hi2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi1 hi2
      rcases hi1 with rfl | rfl <;> rcases hi2 with h | h | h <;> exact absurd h (by decide))
  have hYH : Measurable[sigH X] (Yv X) := by
    apply @measurable_pi_lambda Ω ℕ (fun _ => ℝ) (sigH X) _ (Yv X)
    intro k
    have h1 : Measurable[X.sigmaA] (X.A k) :=
      measurable_iff_comap_le.2 (le_iSup (fun k => MeasurableSpace.comap (X.A k) _) k)
    exact h1.mono (hHi 1 (by simp)) le_rfl
  have hTH : Measurable[sigH X] X.T :=
    (measurable_iff_comap_le.2 (le_refl X.sigmaT)).mono (hHi 2 (by simp)) le_rfl
  have hY : Measurable (Yv X) := measurable_pi_lambda _ hA.measurable
  refine ⟨iSup₂_le fun i _ => hle i, hWc, fun s => ?_, fun k => ?_, ?_, hY, hTm, ?_, ?_, ?_, ?_⟩
  · exact (measurable_iff_comap_le.2 (le_iSup (fun t => MeasurableSpace.comap (X.W t) _) s)).mono
      (hGi 0 (by simp)) le_rfl
  · exact (measurable_iff_comap_le.2 (le_iSup (fun t => MeasurableSpace.comap (X.g t) _) k)).mono
      (hGi 3 (by simp)) le_rfl
  · exact (measurable_iff_comap_le.2 (le_refl X.sigmaJ)).mono (hGi 4 (by simp)) le_rfl
  · exact indep_of_indep_of_le_left hindHG (hTH.prodMk hYH).comap_le
  · exact indep_of_indep_of_le_left hindHG hYH.comap_le
  · have hTY : Indep (MeasurableSpace.comap X.T inferInstance)
        (MeasurableSpace.comap (Yv X) inferInstance) P := by
      have hYA : Measurable[X.sigmaA] (Yv X) :=
        @measurable_pi_lambda Ω ℕ (fun _ => ℝ) X.sigmaA _ (Yv X) (fun k =>
          measurable_iff_comap_le.2 (le_iSup (fun k => MeasurableSpace.comap (X.A k) _) k))
      have h21 : Indep X.sigmaT X.sigmaA P := hind.indep (show (2 : Fin 5) ≠ 1 by decide)
      exact indep_of_indep_of_le_right h21 hYA.comap_le
    have := (indepFun_iff_map_prod_eq_prod_map_map hTm.aemeasurable hY.aemeasurable).1 hTY
    rw [this, hTlaw]
  · rw [ae_all_iff]
    intro i
    rw [ae_map_iff hY.aemeasurable (measurableSet_lt measurable_const (measurable_pi_apply i))]
    have hl := hA.law i
    have h0 : P {ω | X.A i ω ≤ 0} = 0 := by
      have e : {ω | X.A i ω ≤ 0} = X.A i ⁻¹' Set.Iic 0 := rfl
      rw [e, ← Measure.map_apply (hA.measurable i) measurableSet_Iic, hl]
      rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iic,
        ← setLIntegral_congr Iio_ae_eq_Iic]
      exact lintegral_exponentialPDF_of_nonpos le_rfl
    rw [ae_iff]
    simpa [Yv] using h0

theorem lintegral_freeze {Ω β : Type*} (G : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    {mβ : MeasurableSpace β} (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ mΩ)
    (X : Ω → β) (hX : Measurable X) (hind : Indep (MeasurableSpace.comap X mβ) G P)
    (F : β → Ω → ℝ≥0∞)
    (hF : @Measurable (β × Ω) ℝ≥0∞ (@Prod.instMeasurableSpace β Ω mβ G) _ (Function.uncurry F)) :
    ∫⁻ ω, F (X ω) ω ∂P = ∫⁻ x, (∫⁻ ω, F x ω ∂P) ∂(P.map X) := by
  let mG : MeasurableSpace Ω := G
  have hi : @Measurable Ω Ω mΩ G id := by
    intro s hs; exact hG s hs
  have hind' : @IndepFun Ω β Ω mΩ mβ G X id P := by
    show Indep (MeasurableSpace.comap X mβ) (MeasurableSpace.comap id G) P
    rw [MeasurableSpace.comap_id]
    exact hind
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map (mβ := mβ) (mβ' := G) (μ := P)
    (f := X) (g := id) hX.aemeasurable (@Measurable.aemeasurable Ω Ω mΩ G id P hi)).1 hind'
  have hpm : @Measurable Ω (β × Ω) mΩ (@Prod.instMeasurableSpace β Ω mβ G)
      (fun ω => (X ω, id ω)) := hX.prodMk hi
  have hFsl : ∀ x, @Measurable Ω ℝ≥0∞ G _ (F x) := fun x =>
    @Measurable.comp Ω (β × Ω) ℝ≥0∞ G (@Prod.instMeasurableSpace β Ω mβ G) _ _ _ hF
      (@measurable_prodMk_left β Ω mβ G x)
  have h1 := @lintegral_map Ω (β × Ω) mΩ (@Prod.instMeasurableSpace β Ω mβ G) P
    (Function.uncurry F) (fun ω => (X ω, id ω)) hF hpm
  rw [hprod] at h1
  simp only [Function.uncurry_apply_pair, id] at h1
  rw [← h1]
  rw [lintegral_prod (Function.uncurry F) hF.aemeasurable]
  congr 1
  ext x
  have h2 := @lintegral_map Ω Ω mΩ G P (F x) id (hFsl x) hi
  simpa using h2


noncomputable def Φ1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω) (X : Auction Ω)
    (t : ℝ) (y : ℕ → ℝ) : ℝ :=
  if 0 < cnt t y then (∫ ω, Aφ p X t y ω ^ 2 ∂P) / (cnt t y : ℝ) ^ 2 else 0

noncomputable def Φ2 (t : ℝ) (y : ℕ → ℝ) : ℝ := if 0 < cnt t y then 1 / (cnt t y : ℝ) else 0

noncomputable def Φ3 (t : ℝ) (y : ℕ → ℝ) : ℝ := if 0 < cnt t y then 1 / (cnt t y : ℝ) ^ 2 else 0

theorem measurable_cnt (t : ℝ) : Measurable (cnt t) := by
  unfold cnt
  exact countingProcess_measurable_at (fun n (y : ℕ → ℝ) => y n) (fun n => measurable_pi_apply n)
    (fun _ => t) measurable_const

theorem integral_Hφ' {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Auction Ω) (hF : ModelFacts p P X) (a b c t : ℝ)
    (y : ℕ → ℝ) :
    ∫ ω, Hφ a b c p X t y ω ∂P = a ^ 2 * Φ1 p P X t y + b ^ 2 * p.sigma ^ 2 * Φ2 t y +
      c ^ 2 * ((∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2) * Φ3 t y := by
  rw [(integral_Hφ p P X hF a b c t y).2]
  unfold Φ1 Φ2 Φ3
  split_ifs with hn
  · have : (cnt t y : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · simp

theorem Φ_nonneg {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω) (X : Auction Ω)
    (t : ℝ) (y : ℕ → ℝ) : 0 ≤ Φ1 p P X t y ∧ 0 ≤ Φ2 t y ∧ 0 ≤ Φ3 t y := by
  unfold Φ1 Φ2 Φ3
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> first | exact le_rfl | positivity


theorem Hφ_nonneg {Ω : Type*} (a b c : ℝ) (p : Params) (X : Auction Ω) (t : ℝ) (y : ℕ → ℝ)
    (ω : Ω) : 0 ≤ Hφ a b c p X t y ω := by
  unfold Hφ; split_ifs <;> positivity

theorem gint_eq {Ω : Type*} (p : Params) (X : Auction Ω) (t : ℝ) (ω : Ω) :
    (if 0 < Nmm X t ω then
        ((∑ k ∈ Finset.range (Nmm X t ω),
            (Peff p X (arrivalTime X.A (k + 1) ω) ω - Peff p X t ω)) / (Nmm X t ω : ℝ)) ^ 2
      else 0) = Hφ 1 0 0 p X t (Yv X ω) ω := by
  simp only [Hφ, Aφ, one_mul, zero_mul, add_zero]
  rfl

set_option maxHeartbeats 1000000 in
theorem perT {Ω : Type*} [mΩ : MeasurableSpace Ω] (p : Params) (hp : p.Standing) (P : Measure Ω)
    (X : Auction Ω) (hX : IsModel p P X) (a b c t : ℝ) :
    Integrable (fun ω => if 0 < Nmm X t ω then
        ((∑ k ∈ Finset.range (Nmm X t ω),
            (Peff p X (arrivalTime X.A (k + 1) ω) ω - Peff p X t ω)) / (Nmm X t ω : ℝ)) ^ 2
      else 0) P ∧
    gFun p P X t = ∫ y, Φ1 p P X t y ∂(P.map (Yv X)) ∧
    gFun p P X t ≤ p.sigmaF ^ 2 * max t 0 ∧
    ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X t y ω) ∂P ∂(P.map (Yv X)) =
      ENNReal.ofReal (a ^ 2 * gFun p P X t + b ^ 2 * p.sigma ^ 2 * fFun P X t +
        c ^ 2 * ellFun P X t / p.K ^ 2) := by
  haveI : IsProbabilityMeasure P := hX.1
  have hF := modelFacts p P X hX
  have hZ := frz p hp P X hX
  obtain ⟨-, -, -, hWm, -, -, -, hgm, -, -, -, -, -, hJm, -, -⟩ := hX
  set LY := P.map (Yv X) with hLY
  have : IsProbabilityMeasure LY := Measure.isProbabilityMeasure_map hZ.hY.aemeasurable
  set EJ := (∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2 with hEJ
  have hEJ0 : 0 ≤ EJ := by positivity
  -- pointwise lintegral
  have hpt : ∀ a b c y, ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X t y ω) ∂P =
      ENNReal.ofReal (a ^ 2 * Φ1 p P X t y + b ^ 2 * p.sigma ^ 2 * Φ2 t y + c ^ 2 * EJ * Φ3 t y) := by
    intro a b c y
    rw [← integral_Hφ' p P X hF a b c t y]
    exact (ofReal_integral_eq_lintegral_ofReal (integral_Hφ p P X hF a b c t y).1
      (ae_of_all _ (fun ω => Hφ_nonneg a b c p X t y ω))).symm
  -- measurability in y
  have hHm : ∀ a b c, Measurable (fun q : (ℕ → ℝ) × Ω => Hφ a b c p X t q.1 q.2) := fun a b c =>
    measurable_Hφ a b c p X hZ.hWc hWm hgm hJm (fun _ => t) measurable_const id measurable_id
  have hΦ1m : Measurable (Φ1 p P X t) := by
    have e : Φ1 p P X t = fun y => ∫ ω, Hφ 1 0 0 p X t y ω ∂P := by
      ext y; rw [integral_Hφ' p P X hF]; ring
    rw [e]
    exact (StronglyMeasurable.integral_prod_right' (f := fun q : (ℕ → ℝ) × Ω =>
      Hφ 1 0 0 p X t q.1 q.2) (hHm 1 0 0).stronglyMeasurable).measurable
  have hcm := measurable_cnt t
  have hΦ2m : Measurable (Φ2 t) := by
    unfold Φ2
    exact Measurable.ite (hcm (measurableSet_Ioi (a := 0)))
      (measurable_const.div (measurable_from_nat.comp hcm)) measurable_const
  have hΦ3m : Measurable (Φ3 t) := by
    unfold Φ3
    exact Measurable.ite (hcm (measurableSet_Ioi (a := 0)))
      (measurable_const.div ((measurable_from_nat.comp hcm).pow_const 2)) measurable_const
  -- bounds
  have hb1 : ∀ᵐ y ∂LY, Φ1 p P X t y ≤ p.sigmaF ^ 2 * max t 0 := by
    filter_upwards [hZ.aeY] with y hy
    unfold Φ1
    split_ifs with hn
    · have hle := integral_Aφ_sq_le hF t y hy
      have hpos : (0 : ℝ) < (cnt t y : ℝ) ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      linarith
    · positivity
  have hb2 : ∀ y, Φ2 t y ≤ 1 := by
    intro y; unfold Φ2
    split_ifs with hn
    · have : (1 : ℝ) ≤ cnt t y := by exact_mod_cast hn
      rw [div_le_one (by linarith)]; exact this
    · norm_num
  have hb3 : ∀ y, Φ3 t y ≤ 1 := by
    intro y; unfold Φ3
    split_ifs with hn
    · have : (1 : ℝ) ≤ cnt t y := by exact_mod_cast hn
      rw [div_le_one (by positivity)]; nlinarith
    · norm_num
  have hi1 : Integrable (Φ1 p P X t) LY :=
    Integrable.mono' (integrable_const (p.sigmaF ^ 2 * max t 0)) hΦ1m.aestronglyMeasurable
      (by filter_upwards [hb1] with y hy
          rw [Real.norm_eq_abs, abs_of_nonneg (Φ_nonneg p P X t y).1]; exact hy)
  have hi2 : Integrable (Φ2 t) LY :=
    Integrable.mono' (integrable_const 1) hΦ2m.aestronglyMeasurable
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (Φ_nonneg p P X t y).2.1]; exact hb2 y))
  have hi3 : Integrable (Φ3 t) LY :=
    Integrable.mono' (integrable_const 1) hΦ3m.aestronglyMeasurable
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (Φ_nonneg p P X t y).2.2]; exact hb3 y))
  -- the generic Y-level identity
  have hY : ∀ a b c, ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X t y ω) ∂P ∂LY =
      ENNReal.ofReal (a ^ 2 * ∫ y, Φ1 p P X t y ∂LY + b ^ 2 * p.sigma ^ 2 * ∫ y, Φ2 t y ∂LY +
        c ^ 2 * EJ * ∫ y, Φ3 t y ∂LY) := by
    intro a b c
    simp_rw [hpt]
    have hint : Integrable (fun y => a ^ 2 * Φ1 p P X t y + b ^ 2 * p.sigma ^ 2 * Φ2 t y +
        c ^ 2 * EJ * Φ3 t y) LY :=
      ((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun y => by
      obtain ⟨h1, h2, h3⟩ := Φ_nonneg p P X t y
      exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) h1)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h2))
        (mul_nonneg (mul_nonneg (sq_nonneg _) hEJ0) h3)))]
    congr 1
    have j1 : Integrable (fun y => a ^ 2 * Φ1 p P X t y) LY := hi1.const_mul _
    have j2 : Integrable (fun y => b ^ 2 * p.sigma ^ 2 * Φ2 t y) LY := hi2.const_mul _
    have j3 : Integrable (fun y => c ^ 2 * EJ * Φ3 t y) LY := hi3.const_mul _
    have j12 : Integrable (fun y => a ^ 2 * Φ1 p P X t y + b ^ 2 * p.sigma ^ 2 * Φ2 t y) LY :=
      j1.add j2
    rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  -- g via freezing
  have hfreeze : ∫⁻ ω, ENNReal.ofReal (Hφ 1 0 0 p X t (Yv X ω) ω) ∂P =
      ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (Hφ 1 0 0 p X t y ω) ∂P ∂LY := by
    have hFm := (@measurable_Hφ Ω (ℕ → ℝ) (sigG X) _ 1 0 0 p X hZ.hWc hZ.hWG hZ.hgG hZ.hJG
      (fun _ => t) measurable_const id measurable_id).ennreal_ofReal
    exact lintegral_freeze (sigG X) P hZ.hG (Yv X) hZ.hY hZ.indY
      (fun y ω => ENNReal.ofReal (Hφ 1 0 0 p X t y ω)) hFm
  have hg1 := hY 1 0 0
  simp only [one_pow, one_mul, zero_pow two_ne_zero, zero_mul, add_zero] at hg1
  have hgm' : Measurable (fun ω => Hφ 1 0 0 p X t (Yv X ω) ω) := by
    have h0 := measurable_Hφ (β := Ω) 1 0 0 p X hZ.hWc hWm hgm hJm (fun _ => t) measurable_const
      (Yv X) hZ.hY
    exact h0.comp (f := fun ω : Ω => (ω, ω)) (measurable_id.prodMk measurable_id)
  have hgint : Integrable (fun ω => Hφ 1 0 0 p X t (Yv X ω) ω) P := by
    refine ⟨hgm'.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => Hφ_nonneg _ _ _ _ _ _ _ _)),
      hfreeze, hg1]
    exact ENNReal.ofReal_lt_top
  have hgF : gFun p P X t = ∫ y, Φ1 p P X t y ∂LY := by
    unfold gFun
    simp_rw [gint_eq]
    have h1 := ofReal_integral_eq_lintegral_ofReal hgint
      (ae_of_all _ (fun ω => Hφ_nonneg _ _ _ _ _ _ _ _))
    rw [hfreeze, hg1] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun ω => Hφ_nonneg _ _ _ _ _ _ _ _))
      (integral_nonneg (fun y => (Φ_nonneg p P X t y).1))).1 h1
  have hfF : fFun P X t = ∫ y, Φ2 t y ∂LY := by
    rw [hLY, integral_map hZ.hY.aemeasurable hΦ2m.aestronglyMeasurable]
    rfl
  have hlF : ellFun P X t = (∫ ω, X.J ω ^ 2 ∂P) * ∫ y, Φ3 t y ∂LY := by
    rw [hLY, integral_map hZ.hY.aemeasurable hΦ3m.aestronglyMeasurable]
    rfl
  refine ⟨?_, hgF, ?_, ?_⟩
  · simp_rw [gint_eq]; exact hgint
  · rw [hgF]
    calc ∫ y, Φ1 p P X t y ∂LY ≤ ∫ y, p.sigmaF ^ 2 * max t 0 ∂LY :=
          integral_mono_ae hi1 (integrable_const _) hb1
      _ = p.sigmaF ^ 2 * max t 0 := by simp
  · rw [hY a b c, hgF, hfF, hlF, hEJ]
    congr 1
    ring


theorem Tlevel {Ω : Type*} [mΩ : MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) (a b c : ℝ) :
    IntegrableOn (fun u => p.nu * Real.exp (-(p.nu * u)) * (a ^ 2 * gFun p P X u +
        b ^ 2 * p.sigma ^ 2 * fFun P X u + c ^ 2 * ellFun P X u / p.K ^ 2)) (Set.Ioi h) ∧
    ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X (X.T ω + h) (Yv X ω) ω) ∂P =
      ENNReal.ofReal (Real.exp (p.nu * h) * ∫ u in Set.Ioi h, p.nu * Real.exp (-(p.nu * u)) *
        (a ^ 2 * gFun p P X u + b ^ 2 * p.sigma ^ 2 * fFun P X u +
          c ^ 2 * ellFun P X u / p.K ^ 2)) := by
  have hPr : IsProbabilityMeasure P := hX.1
  have hZ := frz p hp P X hX
  have hnu : 0 < p.nu := hp.1
  have hXc := hX
  obtain ⟨-, -, -, hWm, -, -, -, hgm, -, -, -, -, -, hJm, -, -⟩ := hXc
  set LY := P.map (Yv X) with hLY
  set G : ℝ → ℝ := fun u => a ^ 2 * gFun p P X u + b ^ 2 * p.sigma ^ 2 * fFun P X u +
    c ^ 2 * ellFun P X u / p.K ^ 2 with hGdef
  set EJ := ∫ ω, X.J ω ^ 2 ∂P with hEJ
  have hEJ0 : 0 ≤ EJ := integral_nonneg (fun ω => sq_nonneg _)
  have hI : ∀ t, ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X t y ω) ∂P ∂LY =
      ENNReal.ofReal (G t) := fun t => (perT p hp P X hX a b c t).2.2.2
  have hf0 : ∀ t, 0 ≤ fFun P X t ∧ fFun P X t ≤ 1 := by
    intro t
    constructor
    · exact integral_nonneg (fun ω => by split_ifs <;> positivity)
    · calc fFun P X t ≤ ∫ ω, (1 : ℝ) ∂P := by
            apply integral_mono_of_nonneg (ae_of_all _ (fun ω => by
              split_ifs <;> positivity)) (integrable_const _)
            refine ae_of_all _ (fun ω => ?_)
            show (if 0 < Nmm X t ω then _ else _) ≤ (1 : ℝ)
            split_ifs with hn
            · have : (1 : ℝ) ≤ Nmm X t ω := by exact_mod_cast hn
              rw [div_le_one (by linarith)]; exact this
            · norm_num
        _ = 1 := by simp
  have hl0 : ∀ t, 0 ≤ ellFun P X t ∧ ellFun P X t ≤ EJ := by
    intro t
    have h1 : 0 ≤ ∫ ω, (if 0 < Nmm X t ω then 1 / (Nmm X t ω : ℝ) ^ 2 else 0) ∂P :=
      integral_nonneg (fun ω => by split_ifs <;> positivity)
    have h2 : ∫ ω, (if 0 < Nmm X t ω then 1 / (Nmm X t ω : ℝ) ^ 2 else 0) ∂P ≤ 1 := by
      calc _ ≤ ∫ ω, (1 : ℝ) ∂P := by
            apply integral_mono_of_nonneg (ae_of_all _ (fun ω => by
              split_ifs <;> positivity)) (integrable_const _)
            refine ae_of_all _ (fun ω => ?_)
            show (if 0 < Nmm X t ω then _ else _) ≤ (1 : ℝ)
            split_ifs with hn
            · have : (1 : ℝ) ≤ Nmm X t ω := by exact_mod_cast hn
              rw [div_le_one (by positivity)]; nlinarith
            · norm_num
        _ = 1 := by simp
    unfold ellFun
    exact ⟨mul_nonneg hEJ0 h1, by nlinarith⟩
  have hg0 : ∀ t, 0 ≤ gFun p P X t ∧ gFun p P X t ≤ p.sigmaF ^ 2 * max t 0 := by
    intro t
    refine ⟨?_, (perT p hp P X hX a b c t).2.2.1⟩
    exact integral_nonneg (fun ω => by split_ifs <;> positivity)
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    have h1 := hg0 t; have h2 := hf0 t; have h3 := hl0 t
    simp only [hGdef]
    have : 0 ≤ c ^ 2 * ellFun P X t / p.K ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg _) h3.1) (sq_nonneg _)
    have : 0 ≤ a ^ 2 * gFun p P X t := mul_nonneg (sq_nonneg _) h1.1
    have : 0 ≤ b ^ 2 * p.sigma ^ 2 * fFun P X t :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h2.1
    linarith
  have hGb : ∀ t, G t ≤ a ^ 2 * (p.sigmaF ^ 2 * max t 0) + b ^ 2 * p.sigma ^ 2 +
      c ^ 2 * EJ / p.K ^ 2 := by
    intro t
    have h1 := hg0 t; have h2 := hf0 t; have h3 := hl0 t
    simp only [hGdef]
    have e1 : a ^ 2 * gFun p P X t ≤ a ^ 2 * (p.sigmaF ^ 2 * max t 0) :=
      mul_le_mul_of_nonneg_left h1.2 (sq_nonneg _)
    have e2 : b ^ 2 * p.sigma ^ 2 * fFun P X t ≤ b ^ 2 * p.sigma ^ 2 :=
      mul_le_of_le_one_right (by positivity) h2.2
    have e3 : c ^ 2 * ellFun P X t / p.K ^ 2 ≤ c ^ 2 * EJ / p.K ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left h3.2 (sq_nonneg _)
    linarith
  -- measurability of G
  have hHm : Measurable (fun q : (ℝ × (ℕ → ℝ)) × Ω =>
      ENNReal.ofReal (Hφ a b c p X q.1.1 q.1.2 q.2)) :=
    (measurable_Hφ a b c p X hZ.hWc hWm hgm hJm (fun z : ℝ × (ℕ → ℝ) => z.1) measurable_fst
      (fun z => z.2) measurable_snd).ennreal_ofReal
  have hK1 : Measurable (fun z : ℝ × (ℕ → ℝ) => ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X z.1 z.2 ω) ∂P) :=
    hHm.lintegral_prod_right'
  have hK : Measurable (fun t => ∫⁻ y, ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X t y ω) ∂P ∂LY) :=
    hK1.lintegral_prod_right'
  have hGm : Measurable G := by
    have e : G = fun t => (∫⁻ y, ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X t y ω) ∂P ∂LY).toReal := by
      ext t; rw [hI t, ENNReal.toReal_ofReal (hG0 t)]
    rw [e]; exact hK.ennreal_toReal
  -- integrability on (h, ∞)
  have hint : IntegrableOn (fun u => p.nu * Real.exp (-(p.nu * u)) * G u) (Set.Ioi h) := by
    have hd1 : IntegrableOn (fun u : ℝ => u * Real.exp (-(p.nu * u))) (Set.Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := p.nu)
        (by norm_num) one_pos hnu
      refine this.congr_fun (fun u hu => ?_) measurableSet_Ioi
      simp [Real.rpow_one, neg_mul]
    have hd2 : IntegrableOn (fun u : ℝ => Real.exp (-(p.nu * u))) (Set.Ioi 0) := by
      have := exp_neg_integrableOn_Ioi 0 hnu
      simpa [neg_mul] using this
    set C := b ^ 2 * p.sigma ^ 2 + c ^ 2 * EJ / p.K ^ 2 with hC
    have hdom : IntegrableOn (fun u : ℝ => p.nu * (a ^ 2 * p.sigmaF ^ 2) *
        (u * Real.exp (-(p.nu * u))) + p.nu * C * Real.exp (-(p.nu * u))) (Set.Ioi h) := by
      have hsum : IntegrableOn (fun u : ℝ => p.nu * (a ^ 2 * p.sigmaF ^ 2) *
          (u * Real.exp (-(p.nu * u))) + p.nu * C * Real.exp (-(p.nu * u))) (Set.Ioi 0) :=
        (hd1.const_mul _).add (hd2.const_mul _)
      exact hsum.mono_set (Set.Ioi_subset_Ioi hh)
    refine Integrable.mono' hdom ?_ ?_
    · exact ((measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul measurable_id).neg)).mul hGm).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ (fun u hu => ?_))
      have hu0 : 0 ≤ u := hh.trans (le_of_lt hu)
      have hb := hGb u
      rw [max_eq_left hu0] at hb
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hG0 u; positivity)]
      have hE : 0 < p.nu * Real.exp (-(p.nu * u)) := by positivity
      have := mul_le_mul_of_nonneg_left hb hE.le
      simp only [hC]
      nlinarith [Real.exp_pos (-(p.nu * u))]
  refine ⟨hint, ?_⟩
  -- freezing over (T, Y)
  have hFm := (@measurable_Hφ Ω (ℝ × (ℕ → ℝ)) (sigG X) _ a b c p X hZ.hWc hZ.hWG hZ.hgG hZ.hJG
    (fun z => z.1 + h) (measurable_fst.add_const h) (fun z => z.2) measurable_snd).ennreal_ofReal
  have hfr := lintegral_freeze (sigG X) P hZ.hG (fun ω => (X.T ω, Yv X ω))
    (hZ.hT.prodMk hZ.hY) hZ.indZ (fun z ω => ENNReal.ofReal (Hφ a b c p X (z.1 + h) z.2 ω)) hFm
  rw [hfr, hZ.lawZ]
  have hQm : Measurable (fun z : ℝ × (ℕ → ℝ) =>
      ∫⁻ ω, ENNReal.ofReal (Hφ a b c p X (z.1 + h) z.2 ω) ∂P) :=
    ((measurable_Hφ a b c p X hZ.hWc hWm hgm hJm (fun z : ℝ × (ℕ → ℝ) => z.1 + h)
      (measurable_fst.add_const h) (fun z => z.2) measurable_snd).ennreal_ofReal).lintegral_prod_right'
  rw [lintegral_prod _ hQm.aemeasurable]
  rw [lintegral_congr (g := fun t => ENNReal.ofReal (G (t + h))) (fun t => hI (t + h))]
  have hGh : Measurable (fun t => ENNReal.ofReal (G (t + h))) :=
    (hGm.comp (measurable_id.add_const h)).ennreal_ofReal
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (gammaPDF 1 p.nu) from (measurable_gammaPDFReal 1 p.nu).ennreal_ofReal) hGh]
  set ψ : ℝ → ℝ≥0∞ := (Set.Ici h).indicator (fun u => ENNReal.ofReal (Real.exp (p.nu * h)) *
    ENNReal.ofReal (p.nu * Real.exp (-(p.nu * u)) * G u)) with hψ
  have hpt : ∀ t, (gammaPDF 1 p.nu * fun t => ENNReal.ofReal (G (t + h))) t = ψ (t + h) := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · have : t + h ∉ Set.Ici h := by simp; linarith
      simp only [Pi.mul_apply, hψ, Set.indicator_of_notMem this, gammaPDF_of_neg ht, zero_mul]
    · have : t + h ∈ Set.Ici h := by simp; linarith
      rw [hψ, Set.indicator_of_mem this, Pi.mul_apply]
      have he : gammaPDF 1 p.nu t = exponentialPDF p.nu t := rfl
      rw [he, exponentialPDF_of_nonneg ht, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      have : Real.exp (p.nu * h) * Real.exp (-(p.nu * (t + h))) = Real.exp (-(p.nu * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [← this]; ring
  simp_rw [hpt]
  rw [lintegral_add_right_eq_self ψ h, hψ, lintegral_indicator measurableSet_Ici,
    lintegral_const_mul _ (by
      exact ((measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul measurable_id).neg)).mul hGm).ennreal_ofReal),
    ← setLIntegral_congr Ioi_ae_eq_Ici,
    ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ (fun u _ => by
        have := hG0 u; positivity))),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]


theorem final_gen {Ω : Type*} [mΩ : MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) (c : ℝ)
    (D : Ω → ℝ) (hD : ∀ ω ∈ OmegaT X h, D ω = (1 * Aφ p X (X.T ω + h) (Yv X ω) ω +
      1 * Bφ X (X.T ω + h) (Yv X ω) ω + c * (X.J ω / p.K)) / (cnt (X.T ω + h) (Yv X ω) : ℝ)) :
    Integrable (fun ω => D ω ^ 2) (P[|OmegaT X h]) ∧
    IntegrableOn (fun u => p.nu * Real.exp (-(p.nu * u)) * (1 ^ 2 * gFun p P X u +
        1 ^ 2 * p.sigma ^ 2 * fFun P X u + c ^ 2 * ellFun P X u / p.K ^ 2)) (Set.Ioi h) ∧
    ∫ ω, D ω ^ 2 ∂(P[|OmegaT X h]) = ((P (OmegaT X h)).toReal)⁻¹ * Real.exp (p.nu * h) *
      ∫ u in Set.Ioi h, p.nu * Real.exp (-(p.nu * u)) * (1 ^ 2 * gFun p P X u +
        1 ^ 2 * p.sigma ^ 2 * fFun P X u + c ^ 2 * ellFun P X u / p.K ^ 2) := by
  have hPr : IsProbabilityMeasure P := hX.1
  have hZ := frz p hp P X hX
  have hT := Tlevel p hp P X hX h hh 1 1 c
  have hXc := hX
  obtain ⟨-, -, -, hWm, hA, -, -, hgm, -, -, -, -, -, hJm, -, -⟩ := hXc
  set I := ∫ u in Set.Ioi h, p.nu * Real.exp (-(p.nu * u)) * (1 ^ 2 * gFun p P X u +
        1 ^ 2 * p.sigma ^ 2 * fFun P X u + c ^ 2 * ellFun P X u / p.K ^ 2) with hI
  -- the measurable set Ω̃
  have hNm : Measurable (fun ω => Nmm X (tauCl X h ω) ω) :=
    countingProcess_measurable_at X.A hA.measurable (fun ω => X.T ω + h)
      (hZ.hT.add_const h)
  have hOm : MeasurableSet (OmegaT X h) := hNm (measurableSet_Ioi (a := 0))
  -- the frozen integrand
  set Q : Ω → ℝ := fun ω => Hφ 1 1 c p X (X.T ω + h) (Yv X ω) ω with hQ
  have hQm : Measurable Q := by
    have h0 := measurable_Hφ (β := Ω) 1 1 c p X hZ.hWc hWm hgm hJm (fun ω => X.T ω + h)
      (hZ.hT.add_const h) (Yv X) hZ.hY
    exact h0.comp (f := fun ω : Ω => (ω, ω)) (measurable_id.prodMk measurable_id)
  have hQ0 : ∀ ω, 0 ≤ Q ω := fun ω => Hφ_nonneg _ _ _ _ _ _ _ _
  have hind : (OmegaT X h).indicator (fun ω => D ω ^ 2) = Q := by
    ext ω
    by_cases hω : ω ∈ OmegaT X h
    · rw [Set.indicator_of_mem hω, hD ω hω, hQ]
      simp only [Hφ]
      have : 0 < cnt (X.T ω + h) (Yv X ω) := hω
      rw [if_pos this]
    · rw [Set.indicator_of_notMem hω, hQ]
      simp only [Hφ]
      have : ¬ 0 < cnt (X.T ω + h) (Yv X ω) := hω
      rw [if_neg this]
  have hQint : Integrable Q P := by
    refine ⟨hQm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hQ0), hT.2]
    exact ENNReal.ofReal_lt_top
  have hQI : ∫ ω, Q ω ∂P = Real.exp (p.nu * h) * I := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hQ0) hQm.aestronglyMeasurable, hT.2,
      ENNReal.toReal_ofReal]
    apply mul_nonneg (Real.exp_pos _).le
    apply setIntegral_nonneg measurableSet_Ioi
    intro u _
    have h1 : 0 ≤ gFun p P X u := by
      unfold gFun; exact integral_nonneg (fun ω => by split_ifs <;> positivity)
    have h2 : 0 ≤ fFun P X u := by
      unfold fFun; exact integral_nonneg (fun ω => by split_ifs <;> positivity)
    have h3 : 0 ≤ ellFun P X u := by
      unfold ellFun
      exact mul_nonneg (integral_nonneg (fun ω => sq_nonneg _))
        (integral_nonneg (fun ω => by split_ifs <;> positivity))
    have : 0 ≤ c ^ 2 * ellFun P X u / p.K ^ 2 :=
      div_nonneg (mul_nonneg (sq_nonneg _) h3) (sq_nonneg _)
    have : 0 ≤ p.nu * Real.exp (-(p.nu * u)) := mul_nonneg hp.1.le (Real.exp_pos _).le
    have : 0 ≤ 1 ^ 2 * gFun p P X u + 1 ^ 2 * p.sigma ^ 2 * fFun P X u +
        c ^ 2 * ellFun P X u / p.K ^ 2 := by
      have := mul_nonneg (sq_nonneg p.sigma) h2
      nlinarith
    positivity
  have hDon : IntegrableOn (fun ω => D ω ^ 2) (OmegaT X h) P := by
    rw [← integrable_indicator_iff hOm, hind]; exact hQint
  have hset : ∫ ω in OmegaT X h, D ω ^ 2 ∂P = Real.exp (p.nu * h) * I := by
    rw [← integral_indicator hOm, hind, hQI]
  refine ⟨?_, hT.1, ?_⟩
  · by_cases h0 : P (OmegaT X h) = 0
    · have : P[|OmegaT X h] = 0 := by
        rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 h0, smul_zero]
      rw [this]; exact integrable_zero_measure
    · exact hDon.smul_measure (ENNReal.inv_ne_top.2 h0)
  · rw [ProbabilityTheory.cond, integral_smul_measure, hset, ENNReal.toReal_inv, smul_eq_mul]
    ring

end ADCore

namespace ADIncr

theorem expMeasure_Iic {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    expMeasure lam (Set.Iic x) = ENNReal.ofReal (if 0 ≤ x then 1 - Real.exp (-(lam * x)) else 0) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← cdf_expMeasure_eq hlam, cdf_eq_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem ae_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {lam : ℝ}
    (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) :
    ∀ᵐ ω ∂μ, ∀ k, 0 < T k ω := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have e : {ω | ¬ 0 < T k ω} = T k ⁻¹' Set.Iic 0 := by ext ω; simp
  rw [e, ← Measure.map_apply (hT.measurable k) measurableSet_Iic, hT.law k, expMeasure_Iic hlam]
  simp

theorem arrivalTime_mono {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (hpos : ∀ k, 0 < T k ω)
    {m n : ℕ} (h : m ≤ n) : arrivalTime T m ω ≤ arrivalTime T n ω := by
  unfold arrivalTime
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
    (fun i _ _ => (hpos i).le)

theorem le_arrivalTime {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (hpos : ∀ k, 0 < T k ω)
    {k n : ℕ} (h : k < n) : T k ω ≤ arrivalTime T n ω := by
  unfold arrivalTime
  exact Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_range.2 h)

theorem ae_fin {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {lam : ℝ}
    (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (t : ℝ) :
    ∀ᵐ ω ∂μ, {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite := by
  have hpos := ae_pos μ hlam T hT
  set B := ⋂ k, {ω | T k ω ≤ t} with hB
  have hsub : ∀ ω, (∀ k, 0 < T k ω) → ¬ {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite →
      ω ∈ B := by
    intro ω hp hinf
    simp only [hB, Set.mem_iInter, Set.mem_setOf_eq]
    intro k
    obtain ⟨m, hm, hkm⟩ := Set.Infinite.exists_gt hinf k
    exact (le_arrivalTime T ω hp hkm).trans hm.2
  have hq : expMeasure lam (Set.Iic t) < 1 := by
    rw [expMeasure_Iic hlam]
    split_ifs
    · rw [ENNReal.ofReal_lt_one]; linarith [Real.exp_pos (-(lam * t))]
    · simp
  have hBn : ∀ n, μ B ≤ expMeasure lam (Set.Iic t) ^ n := by
    intro n
    have hind := hT.indep.measure_inter_preimage_eq_mul (Finset.range n)
      (sets := fun _ => Set.Iic t) (fun _ _ => measurableSet_Iic)
    calc μ B ≤ μ (⋂ i ∈ Finset.range n, T i ⁻¹' Set.Iic t) := by
          apply measure_mono
          intro ω hω
          simp only [hB, Set.mem_iInter, Set.mem_setOf_eq] at hω
          simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
          exact fun i _ => hω i
      _ = ∏ i ∈ Finset.range n, μ (T i ⁻¹' Set.Iic t) := hind
      _ = expMeasure lam (Set.Iic t) ^ n := by
          rw [Finset.prod_congr rfl (fun i _ => by
            rw [← Measure.map_apply (hT.measurable i) measurableSet_Iic, hT.law i]),
            Finset.prod_const, Finset.card_range]
  have hB0 : μ B = 0 := by
    apply le_antisymm _ (zero_le)
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Filter.Eventually.of_forall hBn)
  have hBae : ∀ᵐ ω ∂μ, ω ∉ B := by
    rw [ae_iff]; simpa using hB0
  filter_upwards [hpos, hBae] with ω hp hnB
  by_contra hinf
  exact hnB (hsub ω hp hinf)

/-- pathwise description of the counting process -/
theorem count_ge {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (hpos : ∀ k, 0 < T k ω) (t : ℝ)
    (hfin : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite) (s : ℝ) (hst : s ≤ t) (m : ℕ)
    (hm : 1 ≤ m) : m ≤ countingProcess T s ω ↔ arrivalTime T m ω ≤ s := by
  set A := {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ s} with hA
  have hAfin : A.Finite := hfin.subset (fun n hn => ⟨hn.1, hn.2.trans hst⟩)
  unfold countingProcess
  rw [← hA]
  constructor
  · intro hmK
    by_contra hnot
    have hsub : A ⊆ (Finset.Icc 1 (m - 1) : Set ℕ) := by
      intro n hn
      simp only [Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hn.1, ?_⟩
      by_contra hnm
      push Not at hnm
      exact hnot ((arrivalTime_mono T ω hpos (by omega)).trans hn.2)
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega
  · intro hms
    have hsub : (Finset.Icc 1 m : Set ℕ) ⊆ A := by
      intro n hn
      simp only [Finset.coe_Icc, Set.mem_Icc] at hn
      exact ⟨hn.1, (arrivalTime_mono T ω hpos hn.2).trans hms⟩
    have := Set.ncard_le_ncard hsub hAfin
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega

theorem count_eq {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (hpos : ∀ k, 0 < T k ω) (t : ℝ)
    (hfin : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite) (s : ℝ) (hs0 : 0 ≤ s) (hst : s ≤ t)
    (i : ℕ) :
    countingProcess T s ω = i ↔ arrivalTime T i ω ≤ s ∧ s < arrivalTime T (i + 1) ω := by
  have h1 := count_ge T ω hpos t hfin s hst (i + 1) (by omega)
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [arrivalTime, hs0]
      · exact (count_ge T ω hpos t hfin s hst i hi).1 hN.ge
    · by_contra hc; push Not at hc; have := h1.2 hc; omega
  · rintro ⟨ha, hb⟩
    have hlt : ¬ i + 1 ≤ countingProcess T s ω := fun h => absurd (h1.1 h) (not_le.2 hb)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · omega
    · have := (count_ge T ω hpos t hfin s hst i hi).2 ha
      omega

theorem exp_Ioc {lam : ℝ} (hlam : 0 < lam) (c b : ℝ) (hc : 0 ≤ c) :
    expMeasure lam (Set.Ioc c b) =
      ENNReal.ofReal (Real.exp (-(lam * c))) * expMeasure lam (Set.Iic (b - c)) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rcases le_or_gt b c with hbc | hbc
  · rw [Set.Ioc_eq_empty (not_lt.2 hbc), measure_empty, expMeasure_Iic hlam]
    split_ifs with h
    · have : b - c = 0 := by linarith
      simp [this]
    · simp
  · have hm : expMeasure lam (Set.Ioc c b) = ENNReal.ofReal
        (cdf (expMeasure lam) b - cdf (expMeasure lam) c) := by
      rw [← StieltjesFunction.measure_Ioc, measure_cdf]
    rw [hm, cdf_expMeasure_eq hlam, cdf_expMeasure_eq hlam, expMeasure_Iic hlam,
      if_pos (by linarith), if_pos hc, if_pos (by linarith), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    have : Real.exp (-(lam * c)) * Real.exp (-(lam * (b - c))) = Real.exp (-(lam * b)) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [this]

theorem memoryless {lam : ℝ} (hlam : 0 < lam) (L3 : Measure ℝ) [SFinite L3] (c d : ℝ)
    (hc : 0 ≤ c) :
    ((expMeasure lam).prod L3) {q | c < q.1 ∧ q.1 + q.2 ≤ d} =
      ENNReal.ofReal (Real.exp (-(lam * c))) *
        ((expMeasure lam).prod L3) {q | q.1 + q.2 ≤ d - c} := by
  haveI := isProbabilityMeasure_expMeasure hlam
  have hm1 : MeasurableSet {q : ℝ × ℝ | c < q.1 ∧ q.1 + q.2 ≤ d} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)
  have hm2 : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 ≤ d - c} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  rw [Measure.prod_apply_symm hm1, Measure.prod_apply_symm hm2, ← lintegral_const_mul]
  · congr 1
    ext v
    have e1 : (fun x => (x, v)) ⁻¹' {q : ℝ × ℝ | c < q.1 ∧ q.1 + q.2 ≤ d} = Set.Ioc c (d - v) := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc]; constructor <;>
        rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    have e2 : (fun x => (x, v)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 ≤ d - c} = Set.Iic (d - v - c) := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic]; constructor <;>
        intro h <;> linarith
    rw [e1, e2, exp_Ioc hlam c (d - v) hc]
  · exact measurable_measure_prodMk_right hm2

theorem arr_split {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (i j : ℕ) (hj : 1 ≤ j) :
    arrivalTime T (i + j) ω = arrivalTime T i ω + T i ω + ∑ k ∈ Finset.Ico (i + 1) (i + j), T k ω ∧
    arrivalTime (fun k => T (i + k)) j ω = T i ω + ∑ k ∈ Finset.Ico (i + 1) (i + j), T k ω ∧
    arrivalTime T (i + 1) ω = arrivalTime T i ω + T i ω := by
  have hIco : ∑ k ∈ Finset.Ico i (i + j), T k ω = T i ω + ∑ k ∈ Finset.Ico (i + 1) (i + j), T k ω :=
    Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  refine ⟨?_, ?_, ?_⟩
  · unfold arrivalTime
    rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ i + j by omega), hIco, add_assoc]
  · unfold arrivalTime
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [add_zero, zero_add]
    rw [Finset.sum_Ico_add (fun m => T m ω) 1 j i, add_comm 1 i, add_comm j i]
  · unfold arrivalTime
    rw [Finset.sum_range_succ]

theorem shifted {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}
    (hT : IsExpInterarrivals μ lam T) (i : ℕ) : IsExpInterarrivals μ lam (fun k => T (i + k)) :=
  ⟨fun k => hT.measurable _, hT.indep.precomp (g := fun k => i + k) (fun a b h => by simpa using h),
    fun k => hT.law _⟩

theorem countingProcess_measurable {Ω : Type*} [MeasurableSpace Ω] (T : ℕ → Ω → ℝ)
    (hT : ∀ i, Measurable (T i)) (t : ℝ) : Measurable (countingProcess T t) := by
  set A : Ω → Set ℕ := fun ω => {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t} with hA
  set F : Ω → ℝ≥0∞ := fun ω => ∑' n : ℕ, (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n with hF
  have hFm : Measurable F := by
    refine Measurable.ennreal_tsum (fun n => ?_)
    have hS : Measurable (arrivalTime T n) := by
      unfold arrivalTime
      exact Finset.measurable_sum _ (fun i _ => hT i)
    have hset : MeasurableSet {ω | n ∈ A ω} := by
      by_cases hn : 1 ≤ n
      · simp only [hA, Set.mem_setOf_eq, hn, true_and]
        exact measurableSet_le hS measurable_const
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
  have : countingProcess T t ⁻¹' {k} =
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

theorem exp_Ioi {lam : ℝ} (hlam : 0 < lam) (c : ℝ) (hc : 0 ≤ c) :
    expMeasure lam (Set.Ioi c) = ENNReal.ofReal (Real.exp (-(lam * c))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, expMeasure_Iic hlam, if_pos hc,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by
      have := Real.exp_le_one_iff.2 (show -(lam * c) ≤ 0 by nlinarith); linarith)]
  congr 1; ring

/-- The increments of the counting process: conditioning on `N_u = i`, the remaining arrivals
form a fresh renewal sequence. -/
theorem incr {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {lam : ℝ}
    (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (u t : ℝ) (hu : 0 ≤ u)
    (hut : u ≤ t) (i j : ℕ) :
    μ {ω | countingProcess T u ω = i ∧ i + j ≤ countingProcess T t ω} =
      μ {ω | countingProcess T u ω = i} *
        μ {ω | j ≤ countingProcess (fun k => T (i + k)) (t - u) ω} := by
  haveI := isProbabilityMeasure_expMeasure hlam
  have hT' := shifted hT i
  have hgood := (ae_pos μ hlam T hT).and (ae_fin μ hlam T hT t)
  have hgood' := (ae_pos μ hlam _ hT').and (ae_fin μ hlam _ hT' (t - u))
  set X1 : Ω → ℝ := arrivalTime T i with hX1
  set X2 : Ω → ℝ := T i with hX2
  set X3 : Ω → ℝ := fun ω => ∑ k ∈ Finset.Ico (i + 1) (i + j), T k ω with hX3
  have hm1 : Measurable X1 := by
    rw [hX1]; unfold arrivalTime; exact Finset.measurable_sum _ (fun k _ => hT.measurable k)
  have hm2 : Measurable X2 := hT.measurable i
  have hm3 : Measurable X3 := Finset.measurable_sum _ (fun k _ => hT.measurable k)
  -- the event {N_u = i}
  have hEi : {ω | countingProcess T u ω = i} =ᵐ[μ] {ω | X1 ω ≤ u ∧ u < X1 ω + X2 ω} := by
    filter_upwards [hgood] with ω hω
    apply propext
    show (countingProcess T u ω = i) ↔ (X1 ω ≤ u ∧ u < X1 ω + X2 ω)
    rw [count_eq T ω hω.1 t hω.2 u hu hut i, (arr_split T ω i 1 le_rfl).2.2]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- j = 0
    have hmono : {ω | countingProcess T u ω = i ∧ i + 0 ≤ countingProcess T t ω} =ᵐ[μ]
        {ω | countingProcess T u ω = i} := by
      filter_upwards [hgood] with ω hω
      apply propext
      show (countingProcess T u ω = i ∧ i + 0 ≤ countingProcess T t ω) ↔ countingProcess T u ω = i
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        rcases Nat.eq_zero_or_pos i with hi | hi
        · omega
        · have h1 := (count_ge T ω hω.1 t hω.2 u hut i hi).1 h.ge
          have h2 := (count_ge T ω hω.1 t hω.2 t le_rfl i hi).2 (h1.trans hut)
          omega
    rw [measure_congr hmono]
    simp
  -- j ≥ 1: the events in terms of X1, X2, X3
  have hEij : {ω | countingProcess T u ω = i ∧ i + j ≤ countingProcess T t ω} =ᵐ[μ]
      {ω | X1 ω ≤ u ∧ u < X1 ω + X2 ω ∧ X1 ω + X2 ω + X3 ω ≤ t} := by
    filter_upwards [hgood] with ω hω
    apply propext
    show (countingProcess T u ω = i ∧ i + j ≤ countingProcess T t ω) ↔
      (X1 ω ≤ u ∧ u < X1 ω + X2 ω ∧ X1 ω + X2 ω + X3 ω ≤ t)
    rw [count_eq T ω hω.1 t hω.2 u hu hut i, (arr_split T ω i 1 le_rfl).2.2,
      count_ge T ω hω.1 t hω.2 t le_rfl (i + j) (by omega), (arr_split T ω i j hj).1]
    tauto
  have hEj : {ω | j ≤ countingProcess (fun k => T (i + k)) (t - u) ω} =ᵐ[μ]
      {ω | X2 ω + X3 ω ≤ t - u} := by
    filter_upwards [hgood'] with ω hω
    apply propext
    show (j ≤ countingProcess (fun k => T (i + k)) (t - u) ω) ↔ (X2 ω + X3 ω ≤ t - u)
    rw [count_ge _ ω hω.1 (t - u) hω.2 (t - u) le_rfl j hj, (arr_split T ω i j hj).2.1]
  -- independence
  have hI23 : IndepFun X2 X3 μ := by
    have := hT.indep.indepFun_finsetSum_of_notMem hT.measurable
      (s := Finset.Ico (i + 1) (i + j)) (i := i) (by simp)
    have e : (∑ k ∈ Finset.Ico (i + 1) (i + j), T k) = X3 := by
      ext ω; simp [hX3, Finset.sum_apply]
    rw [e] at this
    exact this.symm
  have hI1 : IndepFun X1 (fun ω => (X2 ω, X3 ω)) μ := by
    have hdisj : Disjoint (Finset.range i) (Finset.Ico i (i + j)) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      simp only [Finset.mem_range] at hk1; simp only [Finset.mem_Ico] at hk2; omega
    have h0 := hT.indep.indepFun_finset _ _ hdisj hT.measurable
    have hi : i ∈ Finset.Ico i (i + j) := by simp; omega
    set φ1 : (Finset.range i → ℝ) → ℝ := fun x => ∑ k, x k with hφ1
    set φ2 : (Finset.Ico i (i + j) → ℝ) → ℝ × ℝ := fun x =>
      (x ⟨i, hi⟩, ∑ k : ↥(Finset.Ico i (i + j)), if k.1 = i then 0 else x k) with hφ2
    have hφ1m : Measurable φ1 := Finset.measurable_sum _ (fun k _ => measurable_pi_apply k)
    have hφ2m : Measurable φ2 := (measurable_pi_apply _).prodMk
      (Finset.measurable_sum _ (fun k _ => Measurable.ite (by simp) measurable_const
        (measurable_pi_apply k)))
    have h1 := h0.comp hφ1m hφ2m
    have e1 : φ1 ∘ (fun a (k : Finset.range i) => T k a) = X1 := by
      ext ω; simp only [Function.comp, hφ1, hX1, arrivalTime]
      exact Finset.sum_coe_sort (Finset.range i) (fun k => T k ω)
    have e2 : φ2 ∘ (fun a (k : Finset.Ico i (i + j)) => T k a) = fun ω => (X2 ω, X3 ω) := by
      ext ω
      · rfl
      · simp only [Function.comp, hφ2, hX3]
        rw [Finset.sum_coe_sort (Finset.Ico i (i + j)) (fun k => if k = i then 0 else T k ω),
          Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        simp only [if_true, zero_add]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Ico] at hk
        rw [if_neg (by omega)]
    rw [e1, e2] at h1
    exact h1
  have hI12 : IndepFun X1 X2 μ := hI1.comp measurable_id measurable_fst
  -- laws
  have hL2 : μ.map X2 = expMeasure lam := hT.law i
  have hprod1 := (indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable
    (hm2.prodMk hm3).aemeasurable).1 hI1
  have hprod23 := (indepFun_iff_map_prod_eq_prod_map_map hm2.aemeasurable hm3.aemeasurable).1 hI23
  have hprod12 := (indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable hm2.aemeasurable).1 hI12
  rw [hprod23, hL2] at hprod1
  rw [hL2] at hprod12 hprod23
  set L1 := μ.map X1 with hL1
  set L3 := μ.map X3 with hL3
  set K := ((expMeasure lam).prod L3) {q | q.1 + q.2 ≤ t - u} with hK
  set ind : ℝ → ℝ≥0∞ := (Set.Iic u).indicator (fun x => ENNReal.ofReal (Real.exp (-(lam * (u - x)))))
    with hind
  -- the three probabilities
  have hB : MeasurableSet {q : ℝ × ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2.1 ∧ q.1 + q.2.1 + q.2.2 ≤ t} :=
    (measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const (measurable_fst.add (measurable_fst.comp measurable_snd))).inter
        (measurableSet_le ((measurable_fst.add (measurable_fst.comp measurable_snd)).add
          (measurable_snd.comp measurable_snd)) measurable_const))
  have hB2 : MeasurableSet {q : ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
  have hB3 : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 ≤ t - u} :=
    measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hP1 : μ {ω | X1 ω ≤ u ∧ u < X1 ω + X2 ω ∧ X1 ω + X2 ω + X3 ω ≤ t} = (∫⁻ x, ind x ∂L1) * K := by
    have e : {ω | X1 ω ≤ u ∧ u < X1 ω + X2 ω ∧ X1 ω + X2 ω + X3 ω ≤ t} =
        (fun ω => (X1 ω, (X2 ω, X3 ω))) ⁻¹'
          {q : ℝ × ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2.1 ∧ q.1 + q.2.1 + q.2.2 ≤ t} := rfl
    have hindm : Measurable ind :=
      (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(lam * (u - x)))))).indicator
        measurableSet_Iic
    rw [e, ← Measure.map_apply (hm1.prodMk (hm2.prodMk hm3)) hB, hprod1, Measure.prod_apply hB,
      ← lintegral_mul_const K hindm]
    · congr 1
      ext x
      by_cases hx : x ≤ u
      · have es : Prod.mk x ⁻¹' {q : ℝ × ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2.1 ∧ q.1 + q.2.1 + q.2.2 ≤ t}
            = {q : ℝ × ℝ | u - x < q.1 ∧ q.1 + q.2 ≤ t - x} := by
          ext q; simp only [Set.mem_preimage, Set.mem_setOf_eq]
          constructor
          · rintro ⟨-, h2, h3⟩; exact ⟨by linarith, by linarith⟩
          · rintro ⟨h2, h3⟩; exact ⟨hx, by linarith, by linarith⟩
        rw [es, memoryless hlam L3 (u - x) (t - x) (by linarith), hind,
          Set.indicator_of_mem (show x ∈ Set.Iic u from hx)]
        congr 2; ring
      · have es : Prod.mk x ⁻¹' {q : ℝ × ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2.1 ∧ q.1 + q.2.1 + q.2.2 ≤ t}
            = ∅ := by
          ext q; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hx h.1
        rw [es, measure_empty, hind, Set.indicator_of_notMem (show x ∉ Set.Iic u from hx), zero_mul]
  have hP2 : μ {ω | X1 ω ≤ u ∧ u < X1 ω + X2 ω} = ∫⁻ x, ind x ∂L1 := by
    have e : {ω | X1 ω ≤ u ∧ u < X1 ω + X2 ω} =
        (fun ω => (X1 ω, X2 ω)) ⁻¹' {q : ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2} := rfl
    rw [e, ← Measure.map_apply (hm1.prodMk hm2) hB2, hprod12, Measure.prod_apply hB2]
    congr 1
    ext x
    by_cases hx : x ≤ u
    · have es : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2} = Set.Ioi (u - x) := by
        ext q; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
        constructor
        · rintro ⟨-, h2⟩; linarith
        · intro h; exact ⟨hx, by linarith⟩
      rw [es, exp_Ioi hlam _ (by linarith), hind, Set.indicator_of_mem (show x ∈ Set.Iic u from hx)]
    · have es : Prod.mk x ⁻¹' {q : ℝ × ℝ | q.1 ≤ u ∧ u < q.1 + q.2} = ∅ := by
        ext q; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [es, measure_empty, hind, Set.indicator_of_notMem (show x ∉ Set.Iic u from hx)]
  have hP3 : μ {ω | X2 ω + X3 ω ≤ t - u} = K := by
    have e : {ω | X2 ω + X3 ω ≤ t - u} =
        (fun ω => (X2 ω, X3 ω)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 ≤ t - u} := rfl
    rw [e, ← Measure.map_apply (hm2.prodMk hm3) hB3, hprod23]
  rw [measure_congr hEij, measure_congr hEi, measure_congr hEj, hP1, hP2, hP3]

theorem count_mono_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (u t : ℝ)
    (hut : u ≤ t) : ∀ᵐ ω ∂μ, countingProcess T u ω ≤ countingProcess T t ω := by
  filter_upwards [(ae_pos μ hlam T hT).and (ae_fin μ hlam T hT t)] with ω hω
  rcases Nat.eq_zero_or_pos (countingProcess T u ω) with h0 | hpos
  · omega
  · have h1 := (count_ge T ω hω.1 t hω.2 u hut _ hpos).1 le_rfl
    exact (count_ge T ω hω.1 t hω.2 t le_rfl _ hpos).2 (h1.trans hut)

theorem count_pmf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (s : ℝ)
    (hs : 0 ≤ s) (n : ℕ) :
    μ {ω | countingProcess T s ω = n} = poissonMeasure (lam * s).toNNReal {n} := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), poissonMeasure_singleton]
  congr 1
  rw [(poisson_count_cdf μ lam hlam T hT n s hs).2.2, Real.coe_toNNReal _ (mul_nonneg hlam.le hs)]
  ring

theorem joint_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (u t : ℝ)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    μ.map (fun ω => (countingProcess T u ω, countingProcess T t ω - countingProcess T u ω)) =
      (poissonMeasure (lam * u).toNNReal).prod (poissonMeasure (lam * (t - u)).toNNReal) := by
  have hmono := count_mono_ae μ hlam T hT u t hut
  have hmu := countingProcess_measurable T hT.measurable u
  have hmt := countingProcess_measurable T hT.measurable t
  have hR : Measurable (fun ω => (countingProcess T u ω, countingProcess T t ω - countingProcess T u ω)) :=
    hmu.prodMk ((measurable_of_countable (fun p : ℕ × ℕ => p.2 - p.1)).comp (hmu.prodMk hmt))
  rw [Measure.ext_iff_singleton]
  rintro ⟨i, j⟩
  rw [Measure.map_apply hR (measurableSet_singleton _), ← Set.singleton_prod_singleton,
    Measure.prod_prod, Set.singleton_prod_singleton]
  have hT' := shifted hT i
  -- reduce to the event {N_u = i ∧ N_t = i + j}
  have e1 : (fun ω => (countingProcess T u ω, countingProcess T t ω - countingProcess T u ω)) ⁻¹'
      {(i, j)} =ᵐ[μ] {ω | countingProcess T u ω = i ∧ countingProcess T t ω = i + j} := by
    filter_upwards [hmono] with ω hω
    apply propext
    show ((countingProcess T u ω, countingProcess T t ω - countingProcess T u ω) = (i, j)) ↔
      (countingProcess T u ω = i ∧ countingProcess T t ω = i + j)
    rw [Prod.mk.injEq]
    omega
  rw [measure_congr e1]
  set A : ℕ → Set Ω := fun j => {ω | countingProcess T u ω = i ∧ i + j ≤ countingProcess T t ω}
    with hA
  set B : ℕ → Set Ω := fun j => {ω | j ≤ countingProcess (fun k => T (i + k)) (t - u) ω} with hB
  have hmt' := countingProcess_measurable _ hT'.measurable (t - u)
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    (hmu (measurableSet_singleton i)).inter (hmt measurableSet_Ici)
  have hBm : ∀ j, MeasurableSet (B j) := fun j => hmt' measurableSet_Ici
  have eA : {ω | countingProcess T u ω = i ∧ countingProcess T t ω = i + j} = A j \ A (j + 1) := by
    ext ω; simp only [hA, Set.mem_setOf_eq, Set.mem_diff]; omega
  have eB : {ω | countingProcess (fun k => T (i + k)) (t - u) ω = j} = B j \ B (j + 1) := by
    ext ω; simp only [hB, Set.mem_setOf_eq, Set.mem_diff]; omega
  have hsubA : A (j + 1) ⊆ A j := fun ω h => ⟨h.1, by have := h.2; omega⟩
  have hsubB : B (j + 1) ⊆ B j := fun ω h => by
    simp only [hB, Set.mem_setOf_eq] at h ⊢; omega
  rw [eA, measure_diff hsubA (hAm _).nullMeasurableSet (measure_ne_top _ _),
    incr μ hlam T hT u t hu hut i j, incr μ hlam T hT u t hu hut i (j + 1),
    ← ENNReal.mul_sub (fun _ _ => measure_ne_top _ _), ← measure_diff hsubB
      (hBm _).nullMeasurableSet (measure_ne_top _ _), ← eB,
    count_pmf μ hlam T hT u hu i, count_pmf μ hlam _ hT' (t - u) (by linarith) j]

end ADIncr

namespace ADPois
open scoped Nat

noncomputable def phiN (n : ℕ) : ℝ := if 0 < n then 1 / (n : ℝ) ^ 2 else 0

theorem summable_p (a : ℝ≥0) (ψ : ℕ → ℝ) (C : ℝ) (hψ : ∀ n, |ψ n| ≤ C) :
    Summable (fun n => Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / (n ! : ℝ) * ψ n) := by
  refine Summable.of_norm_bounded ((hasSum_one_poissonMeasure a).summable.mul_left C) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hψ n) (by positivity)

theorem stein1 (a : ℝ≥0) (ψ : ℕ → ℝ) (C : ℝ) (hψ : ∀ n, |ψ n| ≤ C) :
    ∫ n, (n : ℝ) * ψ n ∂(poissonMeasure a) = (a : ℝ) * ∫ n, ψ (n + 1) ∂(poissonMeasure a) := by
  rw [integral_poissonMeasure, integral_poissonMeasure]
  simp only [smul_eq_mul]
  have hS := (summable_p a (fun n => ψ (n + 1)) C (fun n => hψ _)).hasSum.mul_left (a : ℝ)
  set f : ℕ → ℝ := fun n => Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / (n ! : ℝ) * ((n : ℝ) * ψ n) with hf
  have e : (fun m => (a : ℝ) * (Real.exp (-(a : ℝ)) * (a : ℝ) ^ m / (m ! : ℝ) * ψ (m + 1))) =
      fun m => f (m + 1) := by
    funext m
    simp only [hf, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [e] at hS
  have h := (hasSum_nat_add_iff (f := f) 1).mp hS
  rw [Finset.sum_range_one] at h
  simp only [hf, CharP.cast_eq_zero, zero_mul, mul_zero, add_zero] at h
  exact h.tsum_eq

theorem stein2 (a : ℝ≥0) (ψ : ℕ → ℝ) (C : ℝ) (hψ : ∀ n, |ψ n| ≤ C) :
    ∫ n, (n : ℝ) * ((n : ℝ) - 1) * ψ n ∂(poissonMeasure a) =
      (a : ℝ) ^ 2 * ∫ n, ψ (n + 2) ∂(poissonMeasure a) := by
  rw [integral_poissonMeasure, integral_poissonMeasure]
  simp only [smul_eq_mul]
  have hS := (summable_p a (fun n => ψ (n + 2)) C (fun n => hψ _)).hasSum.mul_left ((a : ℝ) ^ 2)
  set f : ℕ → ℝ := fun n => Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / (n ! : ℝ) *
    ((n : ℝ) * ((n : ℝ) - 1) * ψ n) with hf
  have e : (fun m => (a : ℝ) ^ 2 * (Real.exp (-(a : ℝ)) * (a : ℝ) ^ m / (m ! : ℝ) * ψ (m + 2))) =
      fun m => f (m + 2) := by
    funext m
    simp only [hf, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [e] at hS
  have h := (hasSum_nat_add_iff (f := f) 2).mp hS
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf] at h
  norm_num at h
  exact h.tsum_eq

theorem phiN_bound (i j : ℕ) : |((i : ℝ)) ^ 2 * phiN (i + j)| ≤ 1 ∧ |(i : ℝ) * phiN (i + j)| ≤ 1 ∧
    |(i : ℝ) * ((i : ℝ) - 1) * phiN (i + j)| ≤ 1 ∧ |phiN (i + j)| ≤ 1 := by
  unfold phiN
  split_ifs with h
  · have hpos : (0 : ℝ) < ((i + j : ℕ) : ℝ) := by exact_mod_cast h
    have hij : (i : ℝ) ≤ ((i + j : ℕ) : ℝ) := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
    have h1 : (1 : ℝ) ≤ ((i + j : ℕ) : ℝ) := by exact_mod_cast h
    have hsq : (0 : ℝ) < ((i + j : ℕ) : ℝ) ^ 2 := by positivity
    have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_of_nonneg (by positivity), mul_one_div, div_le_one hsq]
      exact pow_le_pow_left₀ hi0 hij 2
    · rw [abs_of_nonneg (by positivity), mul_one_div, div_le_one hsq]
      nlinarith
    · rw [abs_le]
      constructor
      · rcases Nat.eq_zero_or_pos i with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ i := by exact_mod_cast h0
          have : 0 ≤ (i : ℝ) * ((i : ℝ) - 1) * (1 / ((i + j : ℕ) : ℝ) ^ 2) := by
            apply mul_nonneg (mul_nonneg hi0 (by linarith)) (by positivity)
          linarith
      · rw [mul_one_div, div_le_one hsq]
        nlinarith
    · rw [abs_of_nonneg (by positivity), div_le_one hsq]
      nlinarith
  · simp

theorem prod_id (a b : ℝ≥0) :
    ∫ q, ((q.1 : ℕ) : ℝ) ^ 2 * phiN (q.1 + q.2) ∂((poissonMeasure a).prod (poissonMeasure b)) =
      (a : ℝ) ^ 2 * ∫ n, phiN (n + 2) ∂(poissonMeasure (a + b)) +
        (a : ℝ) * ∫ n, phiN (n + 1) ∂(poissonMeasure (a + b)) := by
  have hint : ∀ (g : ℕ × ℕ → ℝ), (∀ q, |g q| ≤ 1) →
      Integrable g ((poissonMeasure a).prod (poissonMeasure b)) := fun g hg =>
    Integrable.mono' (integrable_const 1) (measurable_of_countable g).aestronglyMeasurable
      (ae_of_all _ (fun q => by rw [Real.norm_eq_abs]; exact hg q))
  have hint1 : ∀ (g : ℕ → ℝ) (c : ℝ≥0), (∀ q, |g q| ≤ 1) → Integrable g (poissonMeasure c) :=
    fun g c hg => Integrable.mono' (integrable_const 1)
      (measurable_of_countable g).aestronglyMeasurable
      (ae_of_all _ (fun q => by rw [Real.norm_eq_abs]; exact hg q))
  rw [integral_prod_symm _ (hint _ (fun q => (phiN_bound q.1 q.2).1))]
  have inner : ∀ j : ℕ, ∫ i, ((i : ℕ) : ℝ) ^ 2 * phiN (i + j) ∂(poissonMeasure a) =
      (a : ℝ) ^ 2 * ∫ i, phiN (i + 2 + j) ∂(poissonMeasure a) +
        (a : ℝ) * ∫ i, phiN (i + 1 + j) ∂(poissonMeasure a) := by
    intro j
    have e : ∀ i : ℕ, ((i : ℕ) : ℝ) ^ 2 * phiN (i + j) =
        (i : ℝ) * ((i : ℝ) - 1) * phiN (i + j) + (i : ℝ) * phiN (i + j) := fun i => by ring
    simp_rw [e]
    rw [integral_add (hint1 _ a (fun i => (phiN_bound i j).2.2.1))
      (hint1 _ a (fun i => (phiN_bound i j).2.1)),
      stein2 a (fun i => phiN (i + j)) 1 (fun i => (phiN_bound i j).2.2.2),
      stein1 a (fun i => phiN (i + j)) 1 (fun i => (phiN_bound i j).2.2.2)]
  simp_rw [inner]
  have hb : ∀ (k : ℕ) (j : ℕ), |∫ i, phiN (i + k + j) ∂(poissonMeasure a)| ≤ 1 := by
    intro k j
    calc |∫ i, phiN (i + k + j) ∂(poissonMeasure a)| ≤ ∫ i, |phiN (i + k + j)| ∂(poissonMeasure a) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ i, (1 : ℝ) ∂(poissonMeasure a) := by
          apply integral_mono (hint1 _ a (fun i => by
            rw [abs_abs]; exact (phiN_bound 0 (i + k + j)).2.2.2.trans_eq' (by simp)))
            (integrable_const _)
          intro i
          have := (phiN_bound 0 (i + k + j)).2.2.2
          simpa using this
      _ = 1 := by simp
  rw [integral_add ((hint1 _ b (fun j => hb 2 j)).const_mul _)
      ((hint1 _ b (fun j => hb 1 j)).const_mul _), integral_const_mul, integral_const_mul]
  have conv : ∀ k : ℕ, ∫ j, ∫ i, phiN (i + k + j) ∂(poissonMeasure a) ∂(poissonMeasure b) =
      ∫ n, phiN (n + k) ∂(poissonMeasure (a + b)) := by
    intro k
    rw [← poissonMeasure_conv_poissonMeasure, Measure.conv,
      integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable,
      integral_prod_symm _ (hint _ (fun q => (phiN_bound 0 (q.1 + q.2 + k)).2.2.2.trans_eq'
        (by simp)))]
    congr 1; ext j; congr 1; ext i
    congr 1; ring
  rw [conv 2, conv 1]
end ADPois


namespace ADA1
open ADCore

theorem inc_prod {Ω : Type*} [MeasurableSpace Ω] {p : Params} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Auction Ω} (hF : ModelFacts p P X) (a b c : ℝ≥0) :
    ∫ ω, (X.W a ω - X.W c ω) * (X.W b ω - X.W c ω) ∂P =
      min (a : ℝ) b - min (a : ℝ) c - min (c : ℝ) b + min (c : ℝ) c := by
  have e : ∀ ω, (X.W a ω - X.W c ω) * (X.W b ω - X.W c ω) =
      X.W a ω * X.W b ω - X.W a ω * X.W c ω - X.W c ω * X.W b ω + X.W c ω * X.W c ω :=
    fun ω => by ring
  simp_rw [e]
  have i1 : Integrable (fun ω => X.W a ω * X.W b ω) P := (hF.memW a).integrable_mul (hF.memW b)
  have i2 : Integrable (fun ω => X.W a ω * X.W c ω) P := (hF.memW a).integrable_mul (hF.memW c)
  have i3 : Integrable (fun ω => X.W c ω * X.W b ω) P := (hF.memW c).integrable_mul (hF.memW b)
  have i4 : Integrable (fun ω => X.W c ω * X.W c ω) P := (hF.memW c).integrable_mul (hF.memW c)
  have j1 : Integrable (fun ω => X.W a ω * X.W b ω - X.W a ω * X.W c ω) P := i1.sub i2
  have j2 : Integrable (fun ω => X.W a ω * X.W b ω - X.W a ω * X.W c ω - X.W c ω * X.W b ω) P :=
    j1.sub i3
  rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2,
    hF.mulW, hF.mulW, hF.mulW, hF.mulW]

theorem integral_Aφ_sq_eq {Ω : Type*} [MeasurableSpace Ω] {p : Params} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Auction Ω} (hF : ModelFacts p P X) (t : ℝ) (y : ℕ → ℝ)
    (hy : ∀ i, 0 < y i) :
    ∫ ω, Aφ p X t y ω ^ 2 ∂P = p.sigmaF ^ 2 * ∑ k ∈ Finset.range (cnt t y),
      ∑ l ∈ Finset.range (cnt t y), (t - max (sT (k + 1) y) (sT (l + 1) y)) := by
  set n := cnt t y with hn
  set D : ℕ → Ω → ℝ := fun k ω => X.W (sT (k + 1) y).toNNReal ω - X.W t.toNNReal ω with hD
  have eA : ∀ ω, Aφ p X t y ω ^ 2 = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      p.sigmaF ^ 2 * (D k ω * D l ω) := by
    intro ω
    have : Aφ p X t y ω = ∑ k ∈ Finset.range n, p.sigmaF * D k ω := by
      unfold Aφ; apply Finset.sum_congr rfl; intro k _; simp only [hD]; unfold Peff; ring
    rw [this, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring
  simp_rw [eA]
  have hDL : ∀ k, MemLp (D k) 2 P := fun k => (hF.memW _).sub (hF.memW _)
  have hI : ∀ k l, Integrable (fun ω => p.sigmaF ^ 2 * (D k ω * D l ω)) P := fun k l =>
    ((hDL k).integrable_mul (hDL l)).const_mul _
  have hI2 : ∀ k, Integrable (fun ω => ∑ l ∈ Finset.range n, p.sigmaF ^ 2 * (D k ω * D l ω)) P :=
    fun k => integrable_finset_sum _ (fun l _ => hI k l)
  rw [integral_finset_sum _ (fun k _ => hI2 k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_finset_sum _ (fun l _ => hI k l), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [integral_const_mul]
  congr 1
  have hbk := sT_bounds t y hy k (Finset.mem_range.1 hk)
  have hbl := sT_bounds t y hy l (Finset.mem_range.1 hl)
  have ht0 : 0 ≤ t := hbk.1.le.trans hbk.2
  simp only [hD]
  rw [inc_prod hF, Real.coe_toNNReal _ hbk.1.le, Real.coe_toNNReal _ hbl.1.le,
    Real.coe_toNNReal _ ht0, min_eq_left hbk.2, min_eq_right hbl.2, min_self]
  rcases le_total (sT (k + 1) y) (sT (l + 1) y) with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

end ADA1


namespace ADA1
open ADCore

theorem cnt_sum (t : ℝ) (y : ℕ → ℝ) (hy : ∀ i, 0 < y i)
    (hfin : {n : ℕ | 1 ≤ n ∧ sT n y ≤ t}.Finite) (u : ℝ) (hu : u ≤ t) :
    (cnt u y : ℝ) = ∑ k ∈ Finset.range (cnt t y), (if sT (k + 1) y ≤ u then (1 : ℝ) else 0) := by
  have hge := fun s hs m hm => ADIncr.count_ge (fun n (y : ℕ → ℝ) => y n) y hy t hfin s hs m hm
  rw [Finset.sum_boole]
  congr 1
  have : (Finset.range (cnt t y)).filter (fun k => sT (k + 1) y ≤ u) = Finset.range (cnt u y) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h⟩
      have := (hge u hu (k + 1) (by omega)).2 h
      change k + 1 ≤ cnt u y at this
      omega
    · intro h
      have h1 : sT (k + 1) y ≤ u := (hge u hu (k + 1) (by omega)).1 (by change k + 1 ≤ cnt u y; omega)
      have h2 := (hge t le_rfl (k + 1) (by omega)).2 (h1.trans hu)
      change k + 1 ≤ cnt t y at h2
      exact ⟨by omega, h1⟩
  rw [this, Finset.card_range]

theorem integral_step (m t : ℝ) (hm : 0 < m) (hmt : m ≤ t) :
    ∫ u in (0 : ℝ)..t, (if m ≤ u then (1 : ℝ) else 0) = t - m := by
  rw [intervalIntegral.integral_of_le (hm.le.trans hmt)]
  have e : (fun u : ℝ => if m ≤ u then (1 : ℝ) else 0) = (Set.Ici m).indicator (fun _ => 1) := by
    ext u; simp [Set.indicator, Set.mem_Ici]
  rw [e, setIntegral_indicator measurableSet_Ici]
  have : Set.Ioc 0 t ∩ Set.Ici m = Set.Icc m t := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [this, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

theorem pathwise (t : ℝ) (ht : 0 ≤ t) (y : ℕ → ℝ) (hy : ∀ i, 0 < y i)
    (hfin : {n : ℕ | 1 ≤ n ∧ sT n y ≤ t}.Finite) :
    ∑ k ∈ Finset.range (cnt t y), ∑ l ∈ Finset.range (cnt t y),
      (t - max (sT (k + 1) y) (sT (l + 1) y)) = ∫ u in (0 : ℝ)..t, ((cnt u y : ℝ)) ^ 2 := by
  set n := cnt t y with hn
  have hb : ∀ k ∈ Finset.range n, 0 < sT (k + 1) y ∧ sT (k + 1) y ≤ t := fun k hk =>
    sT_bounds t y hy k (Finset.mem_range.1 hk)
  have hcongr : ∀ u ∈ Set.uIcc (0 : ℝ) t, ((cnt u y : ℝ)) ^ 2 =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (if max (sT (k + 1) y) (sT (l + 1) y) ≤ u then (1 : ℝ) else 0) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    rw [cnt_sum t y hy hfin u hu.2, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
    by_cases h1 : sT (k + 1) y ≤ u <;> by_cases h2 : sT (l + 1) y ≤ u <;>
      simp [h1, h2]
  rw [intervalIntegral.integral_congr hcongr]
  have hII : ∀ m : ℝ, IntervalIntegrable (fun u : ℝ => if m ≤ u then (1 : ℝ) else 0) volume 0 t :=
    fun m => by
      refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
        (Measurable.ite measurableSet_Ici measurable_const measurable_const).aestronglyMeasurable
        (ae_of_all _ (fun u => ?_))
      simp only [Real.norm_eq_abs]
      split_ifs <;> simp
  have hII2 : ∀ k, IntervalIntegrable (fun u => ∑ l ∈ Finset.range n,
      if max (sT (k + 1) y) (sT (l + 1) y) ≤ u then (1 : ℝ) else 0) volume 0 t := fun k => by
    have := IntervalIntegrable.sum (Finset.range n)
      (fun l _ => hII (max (sT (k + 1) y) (sT (l + 1) y)))
    rwa [Finset.sum_fn] at this
  rw [intervalIntegral.integral_finset_sum (f := fun k u => ∑ l ∈ Finset.range n,
    if max (sT (k + 1) y) (sT (l + 1) y) ≤ u then (1 : ℝ) else 0) (fun k _ => hII2 k)]
  apply Finset.sum_congr rfl; intro k hk
  rw [intervalIntegral.integral_finset_sum (f := fun l u =>
    if max (sT (k + 1) y) (sT (l + 1) y) ≤ u then (1 : ℝ) else 0) (fun l _ => hII _)]
  apply Finset.sum_congr rfl; intro l hl
  rw [integral_step _ t (lt_max_of_lt_left (hb k hk).1) (max_le (hb k hk).2 (hb l hl).2)]

end ADA1


namespace ADA1
open ADCore

theorem count_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (s : ℝ)
    (hs : 0 ≤ s) :
    μ.map (countingProcess T s) = poissonMeasure (lam * s).toNNReal := by
  have hm := ADIncr.countingProcess_measurable T hT.measurable s
  rw [Measure.ext_iff_singleton]
  intro n
  rw [Measure.map_apply hm (measurableSet_singleton n)]
  exact ADIncr.count_pmf μ hlam T hT s hs n

theorem moment_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T) (u t : ℝ)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    ∫ ω, ADPois.phiN (countingProcess T t ω) * ((countingProcess T u ω : ℕ) : ℝ) ^ 2 ∂μ =
      (lam * u) ^ 2 * ∫ ω, 1 / ((countingProcess T t ω : ℝ) + 2) ^ 2 ∂μ +
        (lam * u) * ∫ ω, 1 / ((countingProcess T t ω : ℝ) + 1) ^ 2 ∂μ := by
  have hmono := ADIncr.count_mono_ae μ hlam T hT u t hut
  have hmu := ADIncr.countingProcess_measurable T hT.measurable u
  have hmt := ADIncr.countingProcess_measurable T hT.measurable t
  have hR : Measurable (fun ω => (countingProcess T u ω, countingProcess T t ω - countingProcess T u ω)) :=
    hmu.prodMk ((measurable_of_countable (fun p : ℕ × ℕ => p.2 - p.1)).comp (hmu.prodMk hmt))
  have e1 : (fun ω => ADPois.phiN (countingProcess T t ω) * ((countingProcess T u ω : ℕ) : ℝ) ^ 2)
      =ᵐ[μ] fun ω => ((countingProcess T u ω : ℕ) : ℝ) ^ 2 *
        ADPois.phiN (countingProcess T u ω + (countingProcess T t ω - countingProcess T u ω)) := by
    filter_upwards [hmono] with ω hω
    rw [Nat.add_sub_cancel' hω, mul_comm]
  have hmap := integral_map hR.aemeasurable (μ := μ)
    (f := fun q : ℕ × ℕ => ((q.1 : ℕ) : ℝ) ^ 2 * ADPois.phiN (q.1 + q.2))
    (measurable_of_countable _).aestronglyMeasurable
  simp only at hmap
  rw [integral_congr_ae e1, ← hmap, ADIncr.joint_law μ hlam T hT u t hu hut, ADPois.prod_id]
  have hsum : (lam * u).toNNReal + (lam * (t - u)).toNNReal = (lam * t).toNNReal := by
    rw [← Real.toNNReal_add (mul_nonneg hlam.le hu) (mul_nonneg hlam.le (by linarith))]
    congr 1; ring
  rw [hsum, ← count_law μ hlam T hT t (hu.trans hut),
    integral_map hmt.aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    integral_map hmt.aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    Real.coe_toNNReal _ (mul_nonneg hlam.le hu)]
  congr 2
  · congr 1; ext ω; simp [ADPois.phiN]
  · congr 1; ext ω; simp [ADPois.phiN]

end ADA1

open AuctionDuration.ClearingError in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (t : ℝ) (ht : 0 < t) :
    Integrable (fun ω => if 0 < Nmm X t ω then
        ((∑ k ∈ Finset.range (Nmm X t ω),
            (Peff p X (arrivalTime X.A (k + 1) ω) ω - Peff p X t ω)) / (Nmm X t ω : ℝ)) ^ 2
      else 0) P ∧
    gFun p P X t =
      p.sigmaF ^ 2 * (t ^ 2 / 2) * p.mu * ∫ ω, 1 / ((Nmm X t ω : ℝ) + 1) ^ 2 ∂P +
        p.sigmaF ^ 2 * (t ^ 3 / 3) * p.mu ^ 2 * ∫ ω, 1 / ((Nmm X t ω : ℝ) + 2) ^ 2 ∂P := by
  have hPr : IsProbabilityMeasure P := hX.1
  have hF := ADCore.modelFacts p P X hX
  have hZ := ADCore.frz p hp P X hX
  have hmu : 0 < p.mu := hp.2.1
  have hT := ADCore.perT p hp P X hX 1 0 0 t
  refine ⟨hT.1, ?_⟩
  have hXc := hX
  obtain ⟨-, -, -, hWm, hA, -, -, hgm, -, -, -, -, -, hJm, -, -⟩ := hXc
  set LY := P.map (ADCore.Yv X) with hLY
  -- measurability of Φ1
  have hHm : Measurable (fun q : (ℕ → ℝ) × Ω => ADCore.Hφ 1 0 0 p X t q.1 q.2) :=
    ADCore.measurable_Hφ 1 0 0 p X hZ.hWc hWm hgm hJm (fun _ => t) measurable_const id measurable_id
  have hΦ1m : Measurable (ADCore.Φ1 p P X t) := by
    have e : ADCore.Φ1 p P X t = fun y => ∫ ω, ADCore.Hφ 1 0 0 p X t y ω ∂P := by
      ext y; rw [ADCore.integral_Hφ' p P X hF]; ring
    rw [e]
    exact (StronglyMeasurable.integral_prod_right' (f := fun q : (ℕ → ℝ) × Ω =>
      ADCore.Hφ 1 0 0 p X t q.1 q.2) hHm.stronglyMeasurable).measurable
  rw [hT.2.1, hLY, integral_map hZ.hY.aemeasurable hΦ1m.aestronglyMeasurable]
  -- pathwise rewriting
  have hgood := (ADIncr.ae_pos P hmu X.A hA).and (ADIncr.ae_fin P hmu X.A hA t)
  have hpt : (fun ω => ADCore.Φ1 p P X t (ADCore.Yv X ω)) =ᵐ[P] fun ω =>
      p.sigmaF ^ 2 * ∫ u in Set.Ioc 0 t,
        ADPois.phiN (Nmm X t ω) * ((Nmm X u ω : ℕ) : ℝ) ^ 2 := by
    filter_upwards [hgood] with ω hω
    have hy : ∀ i, 0 < ADCore.Yv X ω i := hω.1
    have hfin : {n : ℕ | 1 ≤ n ∧ ADCore.sT n (ADCore.Yv X ω) ≤ t}.Finite := hω.2
    have hpw := ADA1.pathwise t ht.le (ADCore.Yv X ω) hy hfin
    unfold ADCore.Φ1
    rw [integral_const_mul, ← intervalIntegral.integral_of_le ht.le,
      show (∫ u in (0 : ℝ)..t, ((Nmm X u ω : ℕ) : ℝ) ^ 2) =
        ∫ u in (0 : ℝ)..t, ((ADCore.cnt u (ADCore.Yv X ω) : ℕ) : ℝ) ^ 2 from rfl, ← hpw]
    unfold ADPois.phiN
    change (if 0 < Nmm X t ω then _ else _) = _
    split_ifs with hn
    · rw [ADA1.integral_Aφ_sq_eq hF t (ADCore.Yv X ω) hy]
      change p.sigmaF ^ 2 * _ / ((Nmm X t ω : ℕ) : ℝ) ^ 2 = _
      ring
    · simp
  rw [integral_congr_ae hpt, integral_const_mul]
  -- Fubini
  set ν := volume.restrict (Set.Ioc (0 : ℝ) t) with hν
  have hjm : Measurable (fun q : Ω × ℝ => countingProcess X.A q.2 q.1) :=
    ADCore.countingProcess_measurable_at (fun n (q : Ω × ℝ) => X.A n q.1)
      (fun n => (hA.measurable n).comp measurable_fst) (fun q => q.2) measurable_snd
  have hFm : Measurable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ADPois.phiN (Nmm X t ω) * ((Nmm X u ω : ℕ) : ℝ) ^ 2) := by
    have h1 : Measurable (fun q : Ω × ℝ => ADPois.phiN (Nmm X t q.1)) :=
      (measurable_of_countable ADPois.phiN).comp
        ((ADIncr.countingProcess_measurable X.A hA.measurable t).comp measurable_fst)
    exact h1.mul ((measurable_from_nat.comp hjm).pow_const 2)
  have hFint : Integrable (Function.uncurry fun (ω : Ω) (u : ℝ) =>
      ADPois.phiN (Nmm X t ω) * ((Nmm X u ω : ℕ) : ℝ) ^ 2) (P.prod ν) := by
    haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
    refine Integrable.mono' (integrable_const 1) hFm.aestronglyMeasurable ?_
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hgood
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := ν)).ae
      (ae_restrict_mem (μ := volume) measurableSet_Ioc)
    filter_upwards [h1, h2] with q hq1 hq2
    simp only [Function.uncurry]
    have hle : Nmm X q.2 q.1 ≤ Nmm X t q.1 := by
      rcases Nat.eq_zero_or_pos (Nmm X q.2 q.1) with h0 | hpos
      · omega
      · have := (ADIncr.count_ge X.A q.1 hq1.1 t hq1.2 q.2 hq2.2 _ hpos).1 le_rfl
        exact (ADIncr.count_ge X.A q.1 hq1.1 t hq1.2 t le_rfl _ hpos).2 (this.trans hq2.2)
    have hb := (ADPois.phiN_bound (Nmm X q.2 q.1) (Nmm X t q.1 - Nmm X q.2 q.1)).1
    rw [Nat.add_sub_cancel' hle] at hb
    rw [Real.norm_eq_abs, mul_comm]; exact hb
  have hswap := integral_integral_swap hFint
  rw [hswap]
  -- inner integrals
  have hinner : ∀ u ∈ Set.Ioc (0 : ℝ) t,
      ∫ ω, ADPois.phiN (Nmm X t ω) * ((Nmm X u ω : ℕ) : ℝ) ^ 2 ∂P =
        (p.mu * u) ^ 2 * ∫ ω, 1 / ((Nmm X t ω : ℝ) + 2) ^ 2 ∂P +
          (p.mu * u) * ∫ ω, 1 / ((Nmm X t ω : ℝ) + 1) ^ 2 ∂P := fun u hu =>
    ADA1.moment_identity P hmu X.A hA u t hu.1.le hu.2
  rw [setIntegral_congr_fun measurableSet_Ioc hinner, ← intervalIntegral.integral_of_le ht.le]
  set E1 := ∫ ω, 1 / ((Nmm X t ω : ℝ) + 1) ^ 2 ∂P
  set E2 := ∫ ω, 1 / ((Nmm X t ω : ℝ) + 2) ^ 2 ∂P
  have e : (fun u : ℝ => (p.mu * u) ^ 2 * E2 + (p.mu * u) * E1) =
      fun u => (p.mu ^ 2 * E2) * u ^ 2 + (p.mu * E1) * u := by
    ext u; ring
  rw [e, intervalIntegral.integral_add (f := fun u : ℝ => p.mu ^ 2 * E2 * u ^ 2)
    (g := fun u : ℝ => p.mu * E1 * u)
    ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
    integral_id]
  ring

