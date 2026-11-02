-- Prove2me | solution 1 for AuctionDuration.ClearingError.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:57:32.213262+00:00
-- url     : https://prove2.me/submissions/8db3731e-d65c-44e3-a48e-646a0c672a38

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

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

theorem modelFacts {Ω : Type*} [MeasurableSpace Ω] (p : Params) (P : Measure Ω) (X : Auction Ω)
    (hX : IsModel p P X) : ModelFacts p P X := by
  obtain ⟨hPr, hBM, hWc, hWm, hA, hTm, hTlaw, hgm, hgind, hgid, hg0L, hg0mean, hgvar, hJm, hJL,
    hind⟩ := hX
  refine ⟨fun s => (hBM.isGaussianProcess.hasGaussianLaw_eval s).memLp_two,
    fun s => hBM.integral_eval s, fun k => (hgid k).symm.memLp_snd hg0L,
    fun k => by rw [(hgid k).integral_eq]; exact hg0mean, fun k => ?_,
    fun s => measurable_iff_comap_le.2 (le_iSup (fun t => MeasurableSpace.comap (X.W t) _) s),
    fun k => measurable_iff_comap_le.2 (le_iSup (fun t => MeasurableSpace.comap (X.g t) _) k),
    measurable_iff_comap_le.2 le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

open AuctionDuration.ClearingError in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    Integrable (fun ω => (Pcl p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    IntegrableOn (fun t => p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t + ellFun P X t / p.K ^ 2)) (Set.Ioi h) ∧
    E p P X h = ((P (OmegaT X h)).toReal)⁻¹ * Real.exp (p.nu * h) *
      ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t + ellFun P X t / p.K ^ 2) := by
  have key := ADCore.final_gen p hp P X hX h hh 1
    (fun ω => Pcl p X h ω - Peff p X (tauCl X h ω) ω) (by
      intro ω hω
      have hN : (0 : ℝ) < (Nmm X (tauCl X h ω) ω : ℝ) := by exact_mod_cast hω
      show Pcl p X h ω - Peff p X (tauCl X h ω) ω =
        (1 * ∑ k ∈ Finset.range (Nmm X (tauCl X h ω) ω),
            (Peff p X (arrivalTime X.A (k + 1) ω) ω - Peff p X (tauCl X h ω) ω) +
          1 * ∑ k ∈ Finset.range (Nmm X (tauCl X h ω) ω), X.g k ω + 1 * (X.J ω / p.K)) /
          (Nmm X (tauCl X h ω) ω : ℝ)
      unfold Pcl Pmid view
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      have hK : p.K ≠ 0 := hp.2.2.2.2.ne'
      field_simp
      ring)
  simp only [one_pow, one_mul] at key
  exact key
