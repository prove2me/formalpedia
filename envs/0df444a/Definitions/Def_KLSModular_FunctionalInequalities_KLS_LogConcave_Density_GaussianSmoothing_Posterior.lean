-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Posterior
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Posterior
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:20:38.370002+00:00
-- url     : https://prove2.me/theorems/c0947a91-14e7-452f-abb0-92bfe4256f3b
-- title:
--   Gaussian posterior and centered posterior
-- statement:
--   `posteriorLaw μ hs x` is the probability measure $P_x=\mu.\operatorname{tilted}(-s\|x-\cdot\|^2)$ for $s>0$, and `centeredPosteriorLaw` is its translate by the negative barycenter. For a probability law with Borell density, the posterior and centered posterior are log-concave, and the posterior density is explicitly $\rho(y)e^{-s\|x-y\|^2}/Z_x$. The centered posterior has mean zero, finite second moment, directional variance at most $\|v\|^2/(2s)$, trace bound $(\dim E)/(2s)$, and the stated uniform polynomial and exponential moment bounds.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Hessian
--   import FunctionalInequalities.KLS.LogConcave.Translation
--   import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def posteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) (x : E) :
--       ProbabilityMeasure E :=
--     ⟨μ.tilted (fun y => -s * ‖x - y‖ ^ 2),
--       isProbabilityMeasure_posterior μ hs x⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/Hessian`](https://prove2.me/theorems/def61c78-d51b-42a2-afd5-1e802be8c868), [`KLS/LogConcave/Translation`](https://prove2.me/theorems/90dffb15-6ccb-4069-ada2-b620f287fe68), [`KLS/LogConcave/Density/BorellRepresentation/Moments`](https://prove2.me/theorems/e5df2dc6-6ebd-4244-bfb5-41d46b1c70d1).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Posterior.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Posterior` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Posterior.lean#L26-L280 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Posterior`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Posterior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Hessian
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments

open MeasureTheory ProbabilityTheory Set FunctionalInequalities
open scoped RealInnerProductSpace Topology
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The Gaussian posterior `P_x = μ.tilted (-s‖x-·‖²)` of a probability law `μ`, as a probability law. -/
noncomputable def posteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) (x : E) :
    ProbabilityMeasure E :=
  ⟨μ.tilted (fun y => -s * ‖x - y‖ ^ 2),
    isProbabilityMeasure_posterior μ hs x⟩
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
 theorem upperSemicontinuous_mul_positive {f g : E → ℝ}
    (hf : UpperSemicontinuous f) (hg : Continuous g) (hgpos : ∀ y, 0 < g y) :
    UpperSemicontinuous (fun y => f y * g y) := by
  intro y c hc
  obtain ⟨a, ha, hac⟩ := exists_between hc
  have hfu : f y < a / g y := (lt_div_iff₀ (hgpos y)).2 ha
  have htc : a / g y * g y < c := by
    simpa only [div_mul_cancel₀ a (hgpos y).ne'] using hac
  have hgc : ∀ᶠ z in 𝓝 y, a / g y * g z < c :=
    (hg.const_mul (a / g y)).continuousAt.eventually (isOpen_Iio.mem_nhds htc)
  filter_upwards [hf y _ hfu, hgc] with z hz hgz
  exact (mul_le_mul_of_nonneg_right hz.le (hgpos z).le).trans_lt hgz
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
 theorem gaussian_weight_logConcave {s Z : ℝ} (hs : 0 ≤ s) (hZ : 0 < Z)
    (x a b : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.exp (-s * ‖x - a‖ ^ 2) / Z) ^ t *
      (Real.exp (-s * ‖x - b‖ ^ 2) / Z) ^ (1 - t) ≤
      Real.exp (-s * ‖x - (t • a + (1 - t) • b)‖ ^ 2) / Z := by
  have hden : Z ^ t * Z ^ (1 - t) = Z := by rw [← Real.rpow_add hZ]; simp
  have heq : t • (x - a) + (1 - t) • (x - b) = x - (t • a + (1 - t) • b) := by
    simp only [smul_sub, sub_smul, one_smul]
    module
  have hker := kernel_logConcave hs (x - a) (x - b) ht0 ht1
  rw [heq] at hker
  simp only [kernel] at hker
  rw [Real.div_rpow (Real.exp_pos _).le hZ.le, Real.div_rpow (Real.exp_pos _).le hZ.le]
  calc
    Real.exp (-s * ‖x - a‖ ^ 2) ^ t / Z ^ t *
        (Real.exp (-s * ‖x - b‖ ^ 2) ^ (1 - t) / Z ^ (1 - t)) =
      (Real.exp (-s * ‖x - a‖ ^ 2) ^ t * Real.exp (-s * ‖x - b‖ ^ 2) ^ (1 - t)) /
        (Z ^ t * Z ^ (1 - t)) := by ring
    _ = _ / Z := by rw [hden]
    _ ≤ _ := div_le_div_of_nonneg_right hker hZ.le
omit [CompleteSpace E] in
/-- The posterior has the Borell density `ρ(y) e^{-s‖x-y‖²}/Z_x` with respect to Lebesgue measure. -/
theorem posteriorLaw_isBorellDensity {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) :
    KLS.IsBorellDensity (posteriorLaw μ hs x : Measure E) volume
      (fun y => ρ y * (Real.exp (-s * ‖x - y‖ ^ 2) /
        ∫ z, Real.exp (-s * ‖x - z‖ ^ 2) ∂μ)) := by
  let Z : ℝ := ∫ z, Real.exp (-s * ‖x - z‖ ^ 2) ∂μ
  have hZ : 0 < Z := integral_exp_pos (integrable_shiftedKernel μ hs x)
  let g : E → ℝ := fun y => Real.exp (-s * ‖x - y‖ ^ 2) / Z
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgpos : ∀ y, 0 < g y := fun y => div_pos (Real.exp_pos _) hZ
  refine ⟨hρ.measurable.mul hg.measurable, fun y => mul_nonneg (hρ.nonneg y) (hgpos y).le,
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.upperSemicontinuous_mul_positive hρ.upperSemicontinuous hg hgpos, ?_, ?_⟩
  · intro a b t ht0 ht1
    have hgLC := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_weight_logConcave hs.le hZ x a b ht0 ht1
    have hρLC := hρ.logConcave a b t ht0 ht1
    change (ρ a * g a) ^ t * (ρ b * g b) ^ (1 - t) ≤ _
    rw [Real.mul_rpow (hρ.nonneg a) (hgpos a).le,
      Real.mul_rpow (hρ.nonneg b) (hgpos b).le]
    calc
      ρ a ^ t * g a ^ t * (ρ b ^ (1 - t) * g b ^ (1 - t)) =
          (ρ a ^ t * ρ b ^ (1 - t)) * (g a ^ t * g b ^ (1 - t)) := by ring
      _ ≤ ρ (t • a + (1 - t) • b) * g (t • a + (1 - t) • b) :=
        mul_le_mul hρLC hgLC (mul_nonneg (Real.rpow_nonneg (hgpos a).le _)
          (Real.rpow_nonneg (hgpos b).le _)) (hρ.nonneg _)
  · change volume.withDensity (fun y => ENNReal.ofReal (ρ y * g y)) =
      μ.withDensity (fun y => ENNReal.ofReal (g y))
    have heq : (fun y => ENNReal.ofReal (ρ y * g y)) =
        (fun y => ENNReal.ofReal (ρ y)) * fun y => ENNReal.ofReal (g y) := by
      funext y
      exact ENNReal.ofReal_mul (hρ.nonneg y)
    rw [heq, withDensity_mul _ hρ.measurable.ennreal_ofReal hg.measurable.ennreal_ofReal,
      hρ.withDensity_eq]
omit [CompleteSpace E] in
/-- The Gaussian posterior of a law with a Borell density is log-concave. -/
theorem posteriorLaw_logConcave {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) :
    KLS.LogConcave (posteriorLaw μ hs x) :=
  (posteriorLaw_isBorellDensity hρ hs x).compactLogConcave
/-- The centered posterior `(y ↦ y − ∫ y dP_x)_* P_x`. -/
noncomputable def centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s) (x : E) :
    ProbabilityMeasure E :=
  Probability.translateLaw (posteriorLaw μ hs x)
    (-∫ y, y ∂(posteriorLaw μ hs x : Measure E))
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The centered posterior is the pushforward of `P_x` under `y ↦ y − ∫ z dP_x`. -/
theorem coe_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (x : E) : (centeredPosteriorLaw μ hs x : Measure E) =
      (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)).map
        (fun y => y - ∫ z, z ∂(μ.tilted (fun z => -s * ‖x - z‖ ^ 2))) := by
  rw [centeredPosteriorLaw, Probability.coe_translateLaw]
  congr 1
  funext y
  change -∫ z, z ∂(μ.tilted (fun z => -s * ‖x - z‖ ^ 2)) + y =
    y - ∫ z, z ∂(μ.tilted (fun z => -s * ‖x - z‖ ^ 2))
  abel
omit [CompleteSpace E] in
/-- The centered posterior is log-concave. -/
theorem centeredPosteriorLaw_logConcave {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) :
    KLS.LogConcave (centeredPosteriorLaw μ hs x) :=
  (posteriorLaw_logConcave hρ hs x).translateLaw _
omit [CompleteSpace E] in
theorem memLp_two_id_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (x : E) : MemLp id 2 (centeredPosteriorLaw μ hs x : Measure E) := by
  let P : ProbabilityMeasure E := posteriorLaw μ hs x
  let c : E := -∫ y, y ∂(P : Measure E)
  have hp : MemLp id 2 (P : Measure E) := memLp_two_id_posterior μ hs x
  have hc : MemLp (fun _ : E => c) 2 (P : Measure E) := memLp_const c
  change MemLp id 2 ((P : Measure E).map (fun y => c + y))
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (measurable_const_add c).aemeasurable).2
  exact hc.add hp
/-- The centered posterior has mean zero (the barycenter is integrable). -/
theorem integral_id_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (x : E) : (∫ y, y ∂(centeredPosteriorLaw μ hs x : Measure E)) = 0 := by
  exact Probability.integral_id_translateLaw_neg_integral (posteriorLaw μ hs x)
    ((memLp_two_id_posterior μ hs x).integrable one_le_two)
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Directional variances are unchanged by centering. -/
theorem variance_inner_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (x v : E) : variance (fun y => ⟪y, v⟫) (centeredPosteriorLaw μ hs x : Measure E) =
      variance (fun y => ⟪y, v⟫) (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) := by
  rw [coe_centeredPosteriorLaw, variance_map (by fun_prop : AEMeasurable (fun y : E => ⟪y, v⟫) _)
    (by fun_prop : AEMeasurable (fun y : E => y - ∫ z, z ∂(μ.tilted (fun z => -s * ‖x - z‖ ^ 2))) _)]
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let _ : IsProbabilityMeasure P := isProbabilityMeasure_posterior μ hs x
  have hY : AEStronglyMeasurable (fun y : E => ⟪y, v⟫) P :=
    ((by fun_prop : Continuous (fun y : E => ⟪y, v⟫))).aestronglyMeasurable
  simpa only [Function.comp_def, inner_sub_left] using
    variance_sub_const hY ⟪∫ z, z ∂P, v⟫
omit [CompleteSpace E] in
theorem variance_inner_centeredPosteriorLaw_le {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x v : E) :
    variance (fun y => ⟪y, v⟫) (centeredPosteriorLaw μ hs x : Measure E) ≤ ‖v‖ ^ 2 / (2 * s) := by
  rw [variance_inner_centeredPosteriorLaw]
  exact variance_inner_posterior_le hρ hs x v
/-- Trace bound `∫‖y‖² dQ_x ≤ n/(2s)` for the centered posterior, uniform in the base point `x`
(dimension zero included). -/
theorem integral_norm_sq_centeredPosteriorLaw_le {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) :
    (∫ y, ‖y‖ ^ 2 ∂(centeredPosteriorLaw μ hs x : Measure E)) ≤ (Module.finrank ℝ E : ℝ) / (2 * s) := by
  let Q := centeredPosteriorLaw μ hs x
  let b := stdOrthonormalBasis ℝ E
  have hQ2 : MemLp id 2 (Q : Measure E) := memLp_two_id_centeredPosteriorLaw μ hs x
  have hQi : Integrable id (Q : Measure E) := hQ2.integrable one_le_two
  have hmean : (∫ y, y ∂(Q : Measure E)) = 0 := integral_id_centeredPosteriorLaw μ hs x
  have hproj (v : E) : MemLp (fun y : E => ⟪y, v⟫) 2 (Q : Measure E) := by
    have hleft : MemLp (fun y : E => ⟪v, y⟫) 2 (Q : Measure E) := by
      simpa only [id_eq, innerSL_apply_apply] using hQ2.continuousLinearMap_comp (innerSL ℝ v)
    exact hleft.ae_eq (ae_of_all _ fun y => (real_inner_comm v y).symm)
  have hsq (i : Fin (Module.finrank ℝ E)) : Integrable (fun y : E => ⟪y, b i⟫ ^ 2) (Q : Measure E) :=
    (memLp_two_iff_integrable_sq (hproj (b i)).aestronglyMeasurable).1 (hproj (b i))
  have hmproj (v : E) : (∫ y, ⟪y, v⟫ ∂(Q : Measure E)) = 0 := by
    calc (∫ y, ⟪y, v⟫ ∂(Q : Measure E)) = ∫ y, (innerSL ℝ v) y ∂(Q : Measure E) := by
          apply integral_congr_ae
          exact ae_of_all _ fun y => real_inner_comm _ _
      _ = (innerSL ℝ v) (∫ y, y ∂(Q : Measure E)) :=
        (innerSL ℝ v).integral_comp_comm hQi
      _ = 0 := by rw [hmean]; simp
  have hv (v : E) : (∫ y, ⟪y, v⟫ ^ 2 ∂(Q : Measure E)) =
      variance (fun y => ⟪y, v⟫) (Q : Measure E) := by
    rw [variance_eq_sub (hproj v), hmproj]
    simp
  have heq : (fun y : E => ‖y‖ ^ 2) = fun y => ∑ i, ⟪y, b i⟫ ^ 2 := by
    funext y
    exact (b.sum_sq_inner_left y).symm
  rw [heq, integral_finsetSum Finset.univ (fun i _ => hsq i)]
  calc
    ∑ i, (∫ y, ⟪y, b i⟫ ^ 2 ∂(Q : Measure E)) =
        ∑ i, variance (fun y => ⟪y, b i⟫) (Q : Measure E) := by simp_rw [hv]
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), 1 / (2 * s) := by
      apply Finset.sum_le_sum
      intro i _
      have h := variance_inner_centeredPosteriorLaw_le hρ hs x (b i)
      simpa only [b.norm_eq_one, one_pow] using h
    _ = (Module.finrank ℝ E : ℝ) / (2 * s) := by simp; ring
/-- **Uniform moments of the centered posterior**: every order `p` is bounded by `p!/q^p · C₀` with the
rate `q = log 3/(4R)`, `R = 2√(n/(2s)+1)`, independent of the base point `x` (BKL Section 2, p. 5). -/
theorem integral_norm_pow_centeredPosteriorLaw_le {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) (p : ℕ) :
    let R : ℝ := 2 * Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * s) + 1)
    Integrable (fun y : E => ‖y‖ ^ p) (centeredPosteriorLaw μ hs x : Measure E) ∧
      (∫ y, ‖y‖ ^ p ∂(centeredPosteriorLaw μ hs x : Measure E)) ≤
        (p.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ p *
          ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have hb := (KLS.LogConcave.borel_iff _).1 (centeredPosteriorLaw_logConcave hρ hs x)
  have h2 := memLp_two_id_centeredPosteriorLaw μ hs x
  have hi : Integrable (fun y : E => ‖y‖ ^ 2) (centeredPosteriorLaw μ hs x : Measure E) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).1 h2
  exact hb.integral_norm_pow_le_of_second_bound hi
    (integral_norm_sq_centeredPosteriorLaw_le hρ hs x) p
/-- Uniform exponential moment `∫ e^{q‖y‖} dQ_x ≤ C₀` of the centered posterior, same rate `q`. -/
theorem integral_exp_norm_centeredPosteriorLaw_le {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) :
    let R : ℝ := 2 * Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * s) + 1)
    Integrable (fun y : E => Real.exp ((Real.log 3 / (4 * R)) * ‖y‖))
        (centeredPosteriorLaw μ hs x : Measure E) ∧
      (∫ y, Real.exp ((Real.log 3 / (4 * R)) * ‖y‖) ∂(centeredPosteriorLaw μ hs x : Measure E)) ≤
        (3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) := by
  dsimp only
  let M : ℝ := (Module.finrank ℝ E : ℝ) / (2 * s)
  have hM : 0 ≤ M := div_nonneg (Nat.cast_nonneg _) (mul_pos (by norm_num) hs).le
  have hplus : 0 < M + 1 := by positivity
  have hR : 0 < 2 * Real.sqrt (M + 1) := mul_pos (by norm_num) (Real.sqrt_pos.2 hplus)
  have hR2 : (2 * Real.sqrt (M + 1)) ^ 2 = 4 * (M + 1) := by
    rw [mul_pow, Real.sq_sqrt hplus.le]; norm_num
  have hi : Integrable (fun y : E => ‖y‖ ^ 2) (centeredPosteriorLaw μ hs x : Measure E) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).1 (memLp_two_id_centeredPosteriorLaw μ hs x)
  have hsecond : (∫ y, ‖y‖ ^ 2 ∂(centeredPosteriorLaw μ hs x : Measure E)) ≤
      (2 * Real.sqrt (M + 1)) ^ 2 / 4 := by
    rw [hR2]
    have h := integral_norm_sq_centeredPosteriorLaw_le hρ hs x
    change _ ≤ M at h
    nlinarith
  have hb := (KLS.LogConcave.borel_iff _).1 (centeredPosteriorLaw_logConcave hρ hs x)
  exact hb.integral_exp_norm_le_of_ball hR
    (Probability.measure_ball_ge_of_integral_norm_sq_le hR hi hsecond)
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The common rate `q = log 3/(8√(n/(2s)+1))` is positive (also in dimension zero). -/
theorem centeredPosteriorRate_pos {s : ℝ} (hs : 0 < s) :
    0 < Real.log 3 /
      (4 * (2 * Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * s) + 1))) := by
  have hM : 0 ≤ (Module.finrank ℝ E : ℝ) / (2 * s) := by positivity
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)
end GaussianSmoothing
end LogConcave
end KLS
end FunctionalInequalities


