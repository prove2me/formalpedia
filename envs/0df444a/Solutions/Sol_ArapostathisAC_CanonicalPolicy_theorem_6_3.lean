-- Prove2me | solution 1 for ArapostathisAC.CanonicalPolicy.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:16:45.291647+00:00
-- url     : https://prove2.me/submissions/97e590cf-d159-49d3-9eee-78599e80280b

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Filter Topology Preorder
open scoped ENNReal

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

instance initMeasure_isProb' (M : BorelCMP S A) (π : Policy M) (x : S) :
    IsProbabilityMeasure (initMeasure π x) := by
  unfold initMeasure
  exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable

lemma pm_map_zero (M : BorelCMP S A) (π : Policy M) (x : S) :
    (pathMeasure M π x).map (fun ω => ω 0) = initMeasure π x := by
  have hf : (fun ω : ℕ → S × A => ω 0) =
      (fun y : (Π _ : Finset.Iic 0, S × A) => y ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe 0 := rfl
  unfold pathMeasure Kernel.trajMeasure
  rw [hf, ← Measure.map_map (g := fun y : (Π _ : Finset.Iic 0, S × A) =>
      y ⟨0, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _) (measurable_frestrictLe 0),
    Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map (measurable_pi_apply _)
    (MeasurableEquiv.measurable _)]
  exact Measure.map_id

instance pathMeasure_isProb' (M : BorelCMP S A) (π : Policy M) (x : S) :
    IsProbabilityMeasure (pathMeasure M π x) := by
  unfold pathMeasure; infer_instance

lemma stepKernel_eq (M : BorelCMP S A) (π : Policy M) (t : ℕ) :
    stepKernel M π t = (M.P.comap (lastPair t) (measurable_pi_apply _)) ⊗ₖ
      ((π.rule (t + 1)).comap (fun p => (histFin t p.1, p.2))
        (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) := rfl

instance comapP_markov (M : BorelCMP S A) (t : ℕ) :
    IsMarkovKernel (M.P.comap (lastPair (S := S) (A := A) t) (measurable_pi_apply _)) :=
  Kernel.IsMarkovKernel.comap _ _

instance comapRule_markov (M : BorelCMP S A) (π : Policy M) (t : ℕ) :
    IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, S × A) × S =>
      (histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
  Kernel.IsMarkovKernel.comap _ _

lemma lintegral_step (M : BorelCMP S A) (π : Policy M) (x : S) (t : ℕ)
    (F : (Π _ : Finset.Iic t, S × A) × (S × A) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (frestrictLe t ω, ω (t + 1)) ∂(pathMeasure M π x) =
      ∫⁻ h, ∫⁻ y, F (h, y) ∂(stepKernel M π t h) ∂((pathMeasure M π x).map (frestrictLe t)) := by
  have key := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => S × A) (μ₀ := initMeasure π x) (κ := stepKernel M π) (a := t)
  unfold pathMeasure
  rw [← Measure.lintegral_compProd hF, key, lintegral_map hF (by fun_prop)]

/-- Along the controlled process, `(X_t, A_t) ∈ K` almost surely. -/
lemma ae_memK (M : BorelCMP S A) (π : Policy M) (x : S) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M π x), (ω t).2 ∈ M.U (ω t).1 := by
  have hB : MeasurableSet {p : S × A | p.2 ∈ M.U p.1} := M.K_meas
  cases t with
  | zero =>
    have h0 : ∀ᵐ p ∂(initMeasure π x), p.2 ∈ M.U p.1 := by
      unfold initMeasure
      rw [ae_map_iff (show Measurable (fun a : A => (x, a)) from
        measurable_const.prodMk measurable_id).aemeasurable hB]
      rw [ae_iff]
      exact π.adm 0 (fun j => j.elim0, x)
    rw [← pm_map_zero M π x] at h0
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h0
  | succ t =>
    have hBc : MeasurableSet {p : S × A | p.2 ∈ M.U p.1}ᶜ := hB.compl
    have hk : ∀ h, stepKernel M π t h {p : S × A | p.2 ∈ M.U p.1}ᶜ = 0 := by
      intro h
      rw [stepKernel_eq, Kernel.compProd_apply hBc]
      have : ∀ y : S, (π.rule (t + 1)) (histFin t h, y)
          (Prod.mk y ⁻¹' {p : S × A | p.2 ∈ M.U p.1}ᶜ) = 0 :=
        fun y => π.adm (t + 1) (histFin t h, y)
      simp only [Kernel.comap_apply, this, lintegral_zero]
    have e : (pathMeasure M π x) {ω | ¬ (ω (t + 1)).2 ∈ M.U (ω (t + 1)).1} =
        ∫⁻ ω, ({p : S × A | p.2 ∈ M.U p.1}ᶜ).indicator 1 (ω (t + 1)) ∂(pathMeasure M π x) := by
      rw [← lintegral_map (measurable_one.indicator hBc) (measurable_pi_apply (t + 1)),
        lintegral_indicator_one hBc, Measure.map_apply (measurable_pi_apply (t + 1)) hBc]
      rfl
    rw [ae_iff, e]
    have h1 := lintegral_step M π x t (fun p => ({p : S × A | p.2 ∈ M.U p.1}ᶜ).indicator 1 p.2)
      ((measurable_one.indicator hBc).comp measurable_snd)
    simp only at h1
    rw [h1]
    simp only [lintegral_indicator_one hBc, hk, lintegral_zero]

lemma cost_integrable (M : BorelCMP S A) (hc : CostBounded M) (π : Policy M) (x : S) (N : ℕ) :
    Integrable (fun ω : ℕ → S × A => ∑ t ∈ Finset.range N, M.c (ω t)) (pathMeasure M π x) := by
  obtain ⟨C, hC⟩ := hc
  refine integrable_finsetSum _ (fun t _ => ?_)
  refine Integrable.of_bound (M.c_meas.comp (measurable_pi_apply t)).aestronglyMeasurable C ?_
  filter_upwards [ae_memK M π x t] with ω hω
  rw [Real.norm_eq_abs]
  exact hC (ω t).1 (ω t).2 hω

lemma JN0_nonneg (M : BorelCMP S A) (π : Policy M) (N : ℕ) (x : S) : 0 ≤ JN0 M π N x := by
  unfold JN0 JN
  simp only [add_zero]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_all_iff.2 (fun t => ae_memK M π x t)] with ω hω
  exact Finset.sum_nonneg (fun t _ => M.c_nonneg _ _ (hω t))

lemma term_integrable (M : BorelCMP S A) (H : S → ℝ) (hHm : Measurable H) (CH : ℝ)
    (hCH : ∀ y, |H y| ≤ CH) (π : Policy M) (x : S) (N : ℕ) :
    Integrable (fun ω : ℕ → S × A => H (ω N).1) (pathMeasure M π x) :=
  Integrable.of_bound (hHm.comp (measurable_fst.comp (measurable_pi_apply N))).aestronglyMeasurable
    CH (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hCH _))

lemma JN_eq (M : BorelCMP S A) (hc : CostBounded M) (H : S → ℝ) (hHm : Measurable H) (CH : ℝ)
    (hCH : ∀ y, |H y| ≤ CH) (π : Policy M) (N : ℕ) (x : S) :
    JN M π N H x = JN0 M π N x + ∫ ω, H (ω N).1 ∂(pathMeasure M π x) := by
  unfold JN0 JN
  simp only [add_zero]
  exact integral_add (cost_integrable M hc π x N) (term_integrable M H hHm CH hCH π x N)

theorem main (M : BorelCMP S A) (hc : CostBounded M) (ρ H : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ H πs) :
    (∀ (x : S) (N : ℕ) (π : Policy M), JN0 M πs N x ≤ JN0 M π N x + span H) ∧
    IsStrongAvgOptimal M πs ∧
    (∀ x : S, avgCost M πs x = optAvg M x ∧ optAvg M x = (ρ x : EReal)) := by
  obtain ⟨_, ⟨hHm, CH, hCH⟩, heq⟩ := hcan
  have hbA : BddAbove (Set.range H) :=
    ⟨CH, by rintro _ ⟨y, rfl⟩; exact (abs_le.1 (hCH y)).2⟩
  have hbB : BddBelow (Set.range H) :=
    ⟨-CH, by rintro _ ⟨y, rfl⟩; exact (abs_le.1 (hCH y)).1⟩
  have hJ : ∀ π N x, JN M π N H x = JN0 M π N x + ∫ ω, H (ω N).1 ∂(pathMeasure M π x) :=
    fun π N x => JN_eq M hc H hHm CH hCH π N x
  have hsup : ∀ (π : Policy M) (N : ℕ) (x : S),
      ∫ ω, H (ω N).1 ∂(pathMeasure M π x) ≤ ⨆ y, H y := by
    intro π N x
    have := integral_mono (term_integrable M H hHm CH hCH π x N) (integrable_const (⨆ y, H y))
      (fun ω => le_ciSup hbA (ω N).1)
    simpa using this
  have hinf : ∀ (π : Policy M) (N : ℕ) (x : S),
      ⨅ y, H y ≤ ∫ ω, H (ω N).1 ∂(pathMeasure M π x) := by
    intro π N x
    have := integral_mono (integrable_const (⨅ y, H y)) (term_integrable M H hHm CH hCH π x N)
      (fun ω => ciInf_le hbB (ω N).1)
    simpa using this
  have hbddJ : ∀ (N : ℕ) (x : S), BddBelow (Set.range fun π : Policy M => JN M π N H x) := by
    intro N x
    refine ⟨⨅ y, H y, ?_⟩
    rintro _ ⟨π, rfl⟩
    show ⨅ y, H y ≤ JN M π N H x
    rw [hJ]
    have := JN0_nonneg M π N x
    have := hinf π N x
    linarith
  have hopt : ∀ (π : Policy M) (N : ℕ) (x : S), H x + N * ρ x ≤ JN M π N H x := by
    intro π N x
    rw [← (heq N x).2]
    exact ciInf_le (hbddJ N x) π
  have hs : ∀ (N : ℕ) (x : S),
      JN0 M πs N x = H x + N * ρ x - ∫ ω, H (ω N).1 ∂(pathMeasure M πs x) := by
    intro N x
    have := hJ πs N x
    rw [(heq N x).1, (heq N x).2] at this
    linarith
  have hlow : ∀ (π : Policy M) (N : ℕ) (x : S), H x + N * ρ x - ⨆ y, H y ≤ JN0 M π N x := by
    intro π N x
    have := hJ π N x
    have := hopt π N x
    have := hsup π N x
    linarith
  have hup : ∀ (N : ℕ) (x : S), JN0 M πs N x ≤ H x + N * ρ x - ⨅ y, H y := by
    intro N x
    rw [hs]
    linarith [hinf πs N x]
  have hlowdiv : ∀ (π : Policy M) (x : S) (N : ℕ), 0 < N →
      (H x - ⨆ y, H y) / N + ρ x ≤ JN0 M π N x / N := by
    intro π x N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [le_div_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
    linarith [hlow π N x]
  have hupdiv : ∀ (x : S) (N : ℕ), 0 < N →
      JN0 M πs N x / N ≤ (H x - ⨅ y, H y) / N + ρ x := by
    intro x N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [div_le_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
    linarith [hup N x]
  have hconv : ∀ (x : S) (D : ℝ), Tendsto (fun N : ℕ => (H x - D) / N + ρ x) atTop (𝓝 (ρ x)) := by
    intro x D
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (H x - D)).add_const (ρ x)
  have hlim : ∀ x, Tendsto (fun N : ℕ => JN0 M πs N x / N) atTop (𝓝 (ρ x)) := by
    intro x
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hconv x (⨆ y, H y)) (hconv x (⨅ y, H y))
      ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact hlowdiv πs x N hN
    · filter_upwards [eventually_gt_atTop 0] with N hN
      exact hupdiv x N hN
  have havg : ∀ x, avgCost M πs x = (ρ x : EReal) := fun x =>
    ((continuous_coe_real_ereal.tendsto _).comp (hlim x)).limsup_eq
  have hliminf : ∀ (x : S) (π : Policy M),
      (ρ x : EReal) ≤ liminf (fun N : ℕ => ((JN0 M π N x / N : ℝ) : EReal)) atTop := by
    intro x π
    have hl : Tendsto (fun N : ℕ => (((H x - ⨆ y, H y) / N + ρ x : ℝ) : EReal)) atTop
        (𝓝 (ρ x : EReal)) := (continuous_coe_real_ereal.tendsto _).comp (hconv x _)
    rw [← hl.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact EReal.coe_le_coe_iff.2 (hlowdiv π x N hN)
  refine ⟨?_, ?_, ?_⟩
  · intro x N π
    have := hs N x
    have := hJ π N x
    have := hopt π N x
    have := hsup π N x
    have := hinf πs N x
    unfold span
    linarith
  · intro x π
    show avgCost M πs x ≤ _
    rw [havg]
    exact hliminf x π
  · intro x
    have hopt' : optAvg M x = (ρ x : EReal) := by
      unfold optAvg
      refine le_antisymm ((iInf_le (fun π => avgCost M π x) πs).trans (havg x).le) ?_
      refine le_iInf (fun π => (hliminf x π).trans ?_)
      unfold avgCost
      exact liminf_le_limsup
    exact ⟨(havg x).trans hopt'.symm, hopt'⟩

end ArapostathisAC.CanonicalPolicy

open MeasureTheory ProbabilityTheory Filter Topology ArapostathisAC.CanonicalPolicy in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) :
    (∀ (x : S) (N : ℕ) (π : Policy M), JN0 M πs N x ≤ JN0 M π N x + span h) ∧
    IsStrongAvgOptimal M πs ∧
    (∀ x : S, avgCost M πs x = optAvg M x ∧ optAvg M x = (ρ x : EReal)) := by
  exact main M hc ρ h πs hcan
