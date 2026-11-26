-- Prove2me | solution 1 for Arxivcond_mat_0004049.rayleigh_law_eq_large_N
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:32:59.339814+00:00
-- url     : https://prove2.me/submissions/990cfe8b-0238-40b6-ba2d-1ea13d5786a2

import Theorems.Thm_Arxivcond_mat_0004049_clt_sum_sq_circular_gaussian
import Theorems.Thm_Arxivcond_mat_0004049_intensityEq_law_coupling
import Theorems.Thm_MathlibGap_gaussianReal_prod_map_sq_add_sq
import Theorems.Thm_Arxivcond_mat_0004049_localizedModel_isProbabilityMeasure

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxivcond_mat_0004049

/-- The complex Gaussian with independent `N(0, v)` real and imaginary parts. -/
private noncomputable abbrev cGauss (v : NNReal) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map Complex.measurableEquivRealProd.symm

private instance cGauss_isProb (v : NNReal) : IsProbabilityMeasure (cGauss v) :=
  Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- The i.i.d. sequence of standard circular complex Gaussians. -/
private noncomputable abbrev iidC : Measure (ℕ → ℂ) := Measure.infinitePi fun _ : ℕ => cGauss (1 / 2)

/-- Numerator `n^{-1/2} ∑_{k<n} z_k²` and denominator `n⁻¹ ∑_{k<n} |z_k|²`. -/
private noncomputable def Wn (n : ℕ) (z : ℕ → ℂ) : ℂ :=
  ((Real.sqrt n)⁻¹ : ℂ) * ∑ k ∈ Finset.range n, z k ^ 2
private noncomputable def Yn (n : ℕ) (z : ℕ → ℂ) : ℝ :=
  (∑ k ∈ Finset.range n, Complex.normSq (z k)) / n

private lemma measurable_Wn (n : ℕ) : Measurable (Wn n) := by unfold Wn; fun_prop
private lemma measurable_Yn (n : ℕ) : Measurable (Yn n) :=
  (Finset.measurable_sum _ fun k _ =>
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply k)).div_const _

private lemma normSq_comp_symm :
    (fun p : ℝ × ℝ => Complex.normSq (Complex.measurableEquivRealProd.symm p)) =
      fun p => p.1 ^ 2 + p.2 ^ 2 := by
  funext p; simp [Complex.normSq_apply, Complex.measurableEquivRealProd_symm_apply, sq]

private lemma integral_sq_gaussianReal (v : NNReal) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) ∧
      ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have hL : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 v) := by
    have h := memLp_id_gaussianReal (μ := 0) (v := v) 2
    simp only [ENNReal.coe_ofNat] at h
    exact h
  refine ⟨hL.integrable_sq, ?_⟩
  rw [← variance_fun_id_gaussianReal (μ := 0) (v := v), variance_of_integral_eq_zero hL.aemeasurable
    (by simp [integral_id_gaussianReal])]

/-- Law of large numbers for `|z_k|²`. -/
private lemma tendstoInMeasure_Yn : TendstoInMeasure iidC Yn atTop (fun _ => 1) := by
  have hXm : ∀ k, Measurable (fun z : ℕ → ℂ => Complex.normSq (z k)) := fun k =>
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply k)
  have hind : iIndepFun (fun k (z : ℕ → ℂ) => Complex.normSq (z k)) iidC :=
    iIndepFun_infinitePi (P := fun _ : ℕ => cGauss (1 / 2)) (X := fun _ => Complex.normSq)
      (fun _ => Complex.continuous_normSq.measurable)
  have hlaw : ∀ k, iidC.map (fun z : ℕ → ℂ => Complex.normSq (z k)) =
      (cGauss (1 / 2)).map Complex.normSq := by
    intro k
    have : (fun z : ℕ → ℂ => Complex.normSq (z k)) = Complex.normSq ∘ (fun z => z k) := rfl
    rw [this, ← Measure.map_map Complex.continuous_normSq.measurable (measurable_pi_apply k),
      Measure.infinitePi_map_eval (fun _ : ℕ => cGauss (1 / 2)) k]
  have hident : ∀ k, IdentDistrib (fun z : ℕ → ℂ => Complex.normSq (z k))
      (fun z : ℕ → ℂ => Complex.normSq (z 0)) iidC iidC := fun k =>
    ⟨(hXm k).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw k, hlaw 0]⟩
  have hsq := integral_sq_gaussianReal (1 / 2)
  have hint0 : Integrable Complex.normSq (cGauss (1 / 2)) := by
    unfold cGauss
    rw [integrable_map_equiv, Function.comp_def, normSq_comp_symm]
    exact (hsq.1.comp_fst _).add (hsq.1.comp_snd _)
  have hmean0 : ∫ w, Complex.normSq w ∂(cGauss (1 / 2)) = 1 := by
    unfold cGauss
    rw [integral_map_equiv, normSq_comp_symm, integral_add (hsq.1.comp_fst _)
      (hsq.1.comp_snd _), integral_fun_fst (f := fun x : ℝ => x ^ 2),
      integral_fun_snd (f := fun x : ℝ => x ^ 2), hsq.2]
    norm_num
  have hint : Integrable (fun z : ℕ → ℂ => Complex.normSq (z 0)) iidC := by
    have h := hint0
    rw [← Measure.infinitePi_map_eval (fun _ : ℕ => cGauss (1 / 2)) 0] at h
    exact h.comp_measurable (measurable_pi_apply 0)
  have hmean : ∫ z, Complex.normSq (z 0) ∂iidC = 1 := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable
      Complex.continuous_normSq.aestronglyMeasurable,
      Measure.infinitePi_map_eval (fun _ : ℕ => cGauss (1 / 2)) 0, hmean0]
  have hae := strong_law_ae_real (fun k (z : ℕ → ℂ) => Complex.normSq (z k)) hint
    (fun i j hij => hind.indepFun hij) hident
  rw [hmean] at hae
  exact tendstoInMeasure_of_tendsto_ae (fun n => (measurable_Yn n).aestronglyMeasurable) hae


/-- The CLT child in `TendstoInDistribution` form. -/
private lemma tendstoInDistribution_Wn :
    TendstoInDistribution Wn atTop id (fun _ => iidC) (cGauss 1) := by
  refine ⟨fun n => (measurable_Wn n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id]
  simp_rw [integral_map (measurable_Wn _).aemeasurable f.continuous.aestronglyMeasurable]
  exact clt_sum_sq_circular_gaussian f

/-- The limit law: `|W|²` for `W` with i.i.d. `N(0,1)` parts has density `e^{-x/2}/2`. -/
private lemma cGauss_one_map_normSq :
    (cGauss 1).map Complex.normSq = (volume : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x / 2) / 2 else 0)) := by
  unfold cGauss
  rw [Measure.map_map Complex.continuous_normSq.measurable
    Complex.measurableEquivRealProd.symm.measurable, Function.comp_def, normSq_comp_symm,
    MathlibGap.gaussianReal_prod_map_sq_add_sq 1 one_ne_zero]
  congr 1
  funext x
  split_ifs
  · congr 1; simp only [NNReal.coe_one]; ring_nf
  · rfl

/-- Slutsky with a continuous cutoff: `|W_n|² / Y_n² ⇒ |W|²`. -/
private lemma tendstoInDistribution_ratio :
    TendstoInDistribution (fun n z => Complex.normSq (Wn n z) / Yn n z ^ 2) atTop
      Complex.normSq (fun _ => iidC) (cGauss 1) := by
  set g : ℂ × ℝ → ℝ := fun p => Complex.normSq p.1 / (max p.2 (1 / 2)) ^ 2 with hg
  have hgc : Continuous g := by
    refine (Complex.continuous_normSq.comp continuous_fst).div
      ((continuous_snd.max continuous_const).pow 2) fun p => ?_
    have : (1 / 2 : ℝ) ≤ max p.2 (1 / 2) := le_max_right _ _
    positivity
  have h1 := tendstoInDistribution_Wn.continuous_comp_prodMk_of_tendstoInMeasure_const hgc
    tendstoInMeasure_Yn (fun n => (measurable_Yn n).aemeasurable)
  have hZ : (fun w : ℂ => g (id w, 1)) = Complex.normSq := by
    have hmax : max (1 : ℝ) (1 / 2) = 1 := max_eq_left (by norm_num)
    funext w; simp only [hg, id, hmax]; simp
  rw [hZ] at h1
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h1 ?_ fun n =>
    ((Complex.continuous_normSq.measurable.comp (measurable_Wn n)).div
      ((measurable_Yn n).pow_const 2)).aemeasurable
  -- the two sequences differ only where `Y_n < 1/2`, an event of vanishing probability
  intro ε hε
  have hYε := tendstoInMeasure_Yn (1 / 2) (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hYε (fun n => zero_le)
    fun n => measure_mono fun z hz => ?_
  simp only [Set.mem_ofPred_eq] at hz ⊢
  by_contra hlt
  push Not at hlt
  have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp
  rw [hhalf, edist_lt_ofReal, Real.dist_eq] at hlt
  have hYn : 1 / 2 ≤ Yn n z := by linarith [(abs_lt.1 hlt).1]
  have hmax : max (Yn n z) (1 / 2) = Yn n z := max_eq_left hYn
  have hdiff : ((fun n z => Complex.normSq (Wn n z) / Yn n z ^ 2) -
      fun n ω => g (Wn n ω, Yn n ω)) n z = 0 := by
    simp only [Pi.sub_apply, hg, hmax, sub_self]
  rw [hdiff, Pi.zero_apply, edist_self] at hz
  exact (not_le.2 hε) hz

private theorem rayleigh_law_eq_large_N_aux (γ : ℝ) (hγ : 0 < γ) :
    LawTendsto γ (fun N (ω : Sample N) => (N : ℝ) * intensityEq ω)
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x / 2) / 2 else 0))) := by
  intro f
  have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
    tendstoInDistribution_ratio.tendsto) f
  have hlim' : Tendsto (fun n => ∫ x, f x ∂(iidC.map (fun z => Complex.normSq (Wn n z) / Yn n z ^ 2)))
      atTop (𝓝 (∫ x, f x ∂((cGauss 1).map Complex.normSq))) := by
    simpa using hlim
  rw [← cGauss_one_map_normSq]
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hmeas : Measurable (fun ω : Sample N => (N : ℝ) * intensityEq ω) := by
    unfold intensityEq ampC uVec tau; fun_prop
  rw [← integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable,
    intensityEq_law_coupling γ hγ N hN]
  rfl

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (γ : ℝ) (hγ : 0 < γ) :
    LawTendsto γ (fun N (ω : Sample N) => (N : ℝ) * intensityEq ω)
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x / 2) / 2 else 0))) :=
  rayleigh_law_eq_large_N_aux γ hγ
