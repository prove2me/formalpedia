-- Prove2me | Definitions.Def_OAIQWBDR000
-- name    : OAIQWBDR000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T20:35:54.075317+00:00
-- url     : https://prove2.me/theorems/ecd43c4d-791f-4a2a-a20c-685d56b1427d
-- title:
--   OpenAI bounded modular recovery split: definitions bundle OAIQWBDR000
-- statement:
--   A definitions bundle of the split of OpenAI's proof of the bounded recovery theorem for modular spectral averages (`OAI.BoundedRecovery.bounded_recovery`, the paper's Theorem 4.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/ModularRecovery` (OpenAI, *Bounded recovery for modular spectral averages*, OpenAI Math Release, September 23, 2026, result family 290, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   This bundle holds the operator-theoretic machinery: the real spectral calculus as continuous linear maps (`calculusCLM`), the half resolvents and mixed resolvents of the modular operator (`halfResolvent`, `modularResolvent`, `modularMixedResolvent`), the polar cutoffs (`polarCutoff`, `cutoffLeft`, `cutoffRight`), the orbit graph of the modular action on the Hilbert pair (`orbitGraph`, `graphBlock`, `graphApproximant`), the commutant data (`commutantData`) and the weighted matrix functionals of the positive-kernel arguments.
--
--   The definitions of the published statement (`StandardModularData`, `RealSpectralCalculus`, `fixedMean`, `RecoveryConclusion` and the rest) are not repeated: the bundle imports them from the published bundle `Def_BoundedRecovery`. It imports no other bundle of this split.
--
--   Modules: `Commutant`, `ErgodicAverages`, `FourierKernels`, `FourierLocalization`, `GaussianAverages`, `KernelContinuity`, `Mean`, `ModularCovariance`, `PolarCutoff`, `PositiveKernels`, `RealGraph`, `SpectralCalculus`, `StrongIntegrals`, `StrongLimits`, `TomitaFundamental`, `TomitaResolvent`.
--
--   The theorems of the development that the definitions do not need are proved in the single solution of this split, which imports the bundle `OAIQWBDR002` (and through it the other two) and proves `OAI.BoundedRecovery.bounded_recovery`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Bounded recovery for modular spectral averages, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 290; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-recovery-for-modular-spectral-averages-September-23-2026/Bounded-recovery-for-modular-spectral-averages-September-23-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/ModularRecovery at commit adc7f12

import Mathlib
import Definitions.Def_BoundedRecovery

section
-- module Solutions.OAIQW_BoundedRecovery.SpectralCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unitary spectral characters, spectral support, and half-exponential bounds. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] lemma spectralCharacter_apply (t u : ℝ) :
    spectralCharacter t u = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := rfl

@[simp] lemma spectralCharacter_zero : spectralCharacter 0 = 1 := by
  ext u
  simp

lemma spectralCharacter_add (t r : ℝ) :
    spectralCharacter (t + r) = spectralCharacter t * spectralCharacter r := by
  ext u
  simp [add_mul, Complex.exp_add]

@[simp] lemma spectralCharacter_norm (t u : ℝ) : ‖spectralCharacter t u‖ = 1 := by
  simp [spectralCharacter, Complex.norm_exp]

lemma spectralCharacter_star (t : ℝ) : star (spectralCharacter t) = spectralCharacter (-t) := by
  ext u
  simp [← Complex.exp_conj]

lemma spectralCharacter_sub_norm_le (t r u : ℝ) :
    ‖spectralCharacter t u - spectralCharacter r u‖ ≤ 2 * |t - r| * |u| := by
  change ‖Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
    Complex.exp (((r * u : ℝ) : ℂ) * Complex.I)‖ ≤ _
  have h := Complex.norm_le_abs_re_add_abs_im
    (Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((r * u : ℝ) : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    mul_one, add_zero, Real.exp_zero, one_mul] at h
  have hc := Real.abs_cos_sub_cos_le (t * u) (r * u)
  have hs := Real.abs_sin_sub_sin_le (t * u) (r * u)
  rw [← sub_mul, abs_mul] at hc hs
  linarith

namespace RealSpectralCalculus

@[simp] lemma unitary_zero (D : RealSpectralCalculus H) : D.unitary 0 = 1 := by
  simp [unitary]

lemma unitary_add (D : RealSpectralCalculus H) (t r : ℝ) :
    D.unitary (t + r) = D.unitary t * D.unitary r := by
  simp [unitary, spectralCharacter_add]

@[simp] lemma unitary_star (D : RealSpectralCalculus H) (t : ℝ) :
    star (D.unitary t) = D.unitary (-t) := by
  simp [unitary, ← map_star, spectralCharacter_star]

@[simp] lemma unitary_neg_mul (D : RealSpectralCalculus H) (t : ℝ) :
    D.unitary (-t) * D.unitary t = 1 := by
  rw [← unitary_add, neg_add_cancel, unitary_zero]

@[simp] lemma unitary_mul_neg (D : RealSpectralCalculus H) (t : ℝ) :
    D.unitary t * D.unitary (-t) = 1 := by
  rw [← unitary_add, add_neg_cancel, unitary_zero]

lemma norm_unitary_apply (D : RealSpectralCalculus H) (t : ℝ) (h : H) :
    ‖D.unitary t h‖ = ‖h‖ := by
  have he : inner ℂ (D.unitary t h) (D.unitary t h) = inner ℂ h h := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ h ((star (D.unitary t) * D.unitary t) h) = _
    rw [unitary_star, unitary_neg_mul]
    rfl
  have he' : ‖D.unitary t h‖ ^ 2 = ‖h‖ ^ 2 := by
    simpa only [← norm_sq_eq_re_inner] using congrArg (@RCLike.re ℂ _) he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he'

lemma norm_calculus_le (D : RealSpectralCalculus H) (f : BoundedContinuousFunction ℝ ℂ) :
    ‖D.calculus f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le D.calculus f

def calculusCLM (D : RealSpectralCalculus H) :
    BoundedContinuousFunction ℝ ℂ →L[ℂ] (H →L[ℂ] H) :=
  D.calculus.toAlgHom.toLinearMap.mkContinuous 1 (by
    intro f
    change ‖D.calculus f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using D.norm_calculus_le f)

@[simp] lemma calculusCLM_apply (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) : D.calculusCLM f = D.calculus f := rfl

lemma norm_calculus_apply_le (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (h : H) :
    ‖D.calculus f h‖ ≤ ‖f‖ * ‖h‖ :=
  (D.calculus f).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (D.norm_calculus_le f)
    (norm_nonneg _))

lemma HasSpectralSupport.calculus {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (g : BoundedContinuousFunction ℝ ℂ) :
    D.HasSpectralSupport I (D.calculus g h) := by
  intro f hf
  change (D.calculus f * D.calculus g) h = 0
  rw [← map_mul]
  exact hh (f * g) (by intro u hu; simp [hf u hu])

lemma HasSpectralSupport.unitary {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) (t : ℝ) : D.HasSpectralSupport I (D.unitary t h) :=
  hh.calculus (spectralCharacter t)

lemma HasSpectralSupport.congr {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) {f g : BoundedContinuousFunction ℝ ℂ}
    (heq : ∀ u ∈ I, f u = g u) : D.calculus f h = D.calculus g h := by
  have hz := hh (f - g) (by intro u hu; simp [heq u hu])
  simpa only [map_sub, sub_apply, sub_eq_zero] using hz

lemma continuous_character_mul (f : BoundedContinuousFunction ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    Continuous (fun t : ℝ => spectralCharacter t * f) := by
  obtain ⟨R, hR, hRn⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  have hl : LipschitzWith ⟨2 * R * ‖f‖, by positivity⟩
      (fun t : ℝ => spectralCharacter t * f) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    rw [dist_eq_norm]
    change ‖spectralCharacter t * f - spectralCharacter r * f‖ ≤
      (2 * R * ‖f‖) * dist t r
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro u
    change ‖spectralCharacter t u * f u - spectralCharacter r u * f u‖ ≤ _
    rw [← sub_mul, norm_mul]
    by_cases hu : u ∈ tsupport (f : ℝ → ℂ)
    · have hu' : |u| ≤ R := by simpa only [Real.norm_eq_abs] using hRn u hu
      calc
        _ ≤ (2 * |t - r| * R) * ‖f‖ := by
          apply mul_le_mul
          · exact (spectralCharacter_sub_norm_le t r u).trans
              (mul_le_mul_of_nonneg_left hu' (by positivity))
          · exact f.norm_coe_le_norm u
          · positivity
          · positivity
        _ = (2 * R * ‖f‖) * dist t r := by rw [Real.dist_eq]; ring
    · rw [image_eq_zero_of_notMem_tsupport hu, norm_zero, mul_zero]
      positivity
  exact hl.continuous

lemma continuous_unitary_apply_compact (D : RealSpectralCalculus H)
    (f : BoundedContinuousFunction ℝ ℂ) (hf : HasCompactSupport (f : ℝ → ℂ)) (k : H) :
    Continuous (fun t : ℝ => D.unitary t (D.calculus f k)) := by
  have h : Continuous (fun t : ℝ => D.calculus (spectralCharacter t * f) k) :=
    (D.calculusCLM.continuous.comp (continuous_character_mul f hf)).clm_apply continuous_const
  simpa only [map_mul, mul_apply_eq_comp, unitary] using h

lemma continuous_unitary_apply (D : RealSpectralCalculus H) (h : H) :
    Continuous (fun t : ℝ => D.unitary t h) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨v, ⟨f, hf, k, rfl⟩, hv⟩ := D.nondegenerate.exists_dist_lt h (by positivity : 0 < ε / 3)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
    (D.continuous_unitary_apply_compact f hf k).continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun {r} hr => ?_⟩
  have hes (q : ℝ) : dist (D.unitary q h) (D.unitary q (D.calculus f k)) < ε / 3 := by
    simpa only [dist_eq_norm, ← map_sub, D.norm_unitary_apply] using hv
  have ht := dist_triangle4 (D.unitary r h) (D.unitary r (D.calculus f k))
    (D.unitary t (D.calculus f k)) (D.unitary t h)
  have htr := hes t
  rw [dist_comm] at htr
  linarith [hes r, hd hr]

lemma continuous_unitary_apply_varying (D : RealSpectralCalculus H)
    {F : ℝ → H} (hF : Continuous F) :
    Continuous (fun t => D.unitary t (F t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro eps heps
  obtain ⟨d₁, hd₁, h₁⟩ := Metric.continuousAt_iff.mp hF.continuousAt
    (eps / 2) (by positivity)
  obtain ⟨d₂, hd₂, h₂⟩ := Metric.continuousAt_iff.mp
    (D.continuous_unitary_apply (F t)).continuousAt (eps / 2) (by positivity)
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, fun {r} hr => ?_⟩
  have hdist : dist (D.unitary r (F r)) (D.unitary r (F t)) = dist (F r) (F t) := by
    simp only [dist_eq_norm, ← map_sub, D.norm_unitary_apply]
  have hv := dist_triangle (D.unitary r (F r)) (D.unitary r (F t)) (D.unitary t (F t))
  rw [hdist] at hv
  linarith [h₁ (lt_of_lt_of_le hr (min_le_left _ _)),
    h₂ (lt_of_lt_of_le hr (min_le_right _ _))]

def upperHalfExponential (b : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min b u / 2) : ℂ))
    (by fun_prop) (Real.exp (b / 2)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

lemma HasSpectralSupport.halfGraph {D : RealSpectralCalculus H} {I : Set ℝ} {h : H}
    (hh : D.HasSpectralSupport I h) {b : ℝ} (hb : ∀ u ∈ I, u ≤ b) :
    (h, D.calculus (upperHalfExponential b) h) ∈ D.halfGraph := by
  obtain ⟨N, hN⟩ := exists_nat_gt b
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (hh.congr ?_).symm
  intro u hu
  have hun : u ≤ (n : ℝ) := (hb u hu).trans (hN.le.trans (Nat.cast_le.mpr hn))
  change (Real.exp (min (n : ℝ) u / 2) : ℂ) = (Real.exp (min b u / 2) : ℂ)
  rw [min_eq_right hun, min_eq_right (hb u hu)]

end RealSpectralCalculus

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.TomitaResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvents of the half-exponential and the closed Tomita graph. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def halfResolvent : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (((Real.exp (u/2) + 1)⁻¹ : ℝ) : ℂ))
    (by
      apply Complex.continuous_ofReal.comp
      apply Continuous.inv₀
      · fun_prop
      · intro u
        exact ne_of_gt (add_pos (Real.exp_pos _) zero_lt_one))
    1 (by
      intro u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
      exact inv_le_one_of_one_le₀ (by have := Real.exp_pos (u/2); linarith))

@[simp] lemma halfResolvent_apply (u : ℝ) :
    halfResolvent u = (((Real.exp (u/2) + 1)⁻¹ : ℝ) : ℂ) := rfl

lemma halfResolvent_selfAdjoint : IsSelfAdjoint halfResolvent := by
  ext u
  change star ((((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ)) = _
  simp only [Complex.star_def,Complex.conj_ofReal]
  rfl

lemma halfResolvent_cutoff_norm (n : ℕ) : ‖halfExponentialCutoff n * halfResolvent‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro u
  change ‖(Real.exp (min (n:ℝ) u / 2) : ℂ) * (((Real.exp (u/2) + 1)⁻¹ : ℝ) : ℂ)‖ ≤ 1
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  have hh : Real.exp (min (n:ℝ) u / 2) ≤ Real.exp (u/2) :=
    Real.exp_le_exp.mpr (by linarith [min_le_right (n:ℝ) u])
  linarith

namespace RealSpectralCalculus

lemma tendsto_calculus_of_compact_eventual (D : RealSpectralCalculus H)
    (f : ℕ → BoundedContinuousFunction ℝ ℂ) (g : BoundedContinuousFunction ℝ ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (he : ∀ q : BoundedContinuousFunction ℝ ℂ, HasCompactSupport (q : ℝ → ℂ) →
      ∀ᶠ n in atTop, f n * q = g * q) (h : H) :
    Tendsto (fun n => D.calculus (f n) h) atTop (𝓝 (D.calculus g h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨v,⟨q,hq,k,rfl⟩,hv⟩ := D.nondegenerate.exists_dist_lt h
    (show 0 < eps / (C + ‖g‖ + 1) by positivity)
  have hv' : ‖h - D.calculus q k‖ < eps / (C + ‖g‖ + 1) := by
    simpa only [dist_eq_norm] using hv
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he q hq)
  refine ⟨N,fun n hn => ?_⟩
  have hqeq : D.calculus (f n) (D.calculus q k) = D.calculus g (D.calculus q k) := by
    change (D.calculus (f n) * D.calculus q) k = (D.calculus g * D.calculus q) k
    rw [← map_mul,← map_mul,hN n hn]
  rw [dist_eq_norm]
  have heq : D.calculus (f n) h - D.calculus g h =
      D.calculus (f n) (h - D.calculus q k) - D.calculus g (h - D.calculus q k) := by
    simp only [map_sub,hqeq]
    abel
  rw [heq]
  calc
    _ ≤ ‖D.calculus (f n) (h - D.calculus q k)‖ + ‖D.calculus g (h - D.calculus q k)‖ := norm_sub_le _ _
    _ ≤ C * ‖h-D.calculus q k‖ + ‖g‖ * ‖h-D.calculus q k‖ :=
      add_le_add ((D.norm_calculus_apply_le _ _).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)))
        (D.norm_calculus_apply_le _ _)
    _ ≤ (C + ‖g‖ + 1) * ‖h-D.calculus q k‖ := by nlinarith [norm_nonneg (h-D.calculus q k)]
    _ < (C + ‖g‖ + 1) * (eps / (C+‖g‖+1)) := mul_lt_mul_of_pos_left hv' (by positivity)
    _ = eps := by field_simp

lemma halfResolvent_cutoff_tendsto (D : RealSpectralCalculus H) (h : H) :
    Tendsto (fun n => D.calculus (halfExponentialCutoff n * halfResolvent) h)
      atTop (𝓝 (D.calculus (1-halfResolvent) h)) := by
  apply D.tendsto_calculus_of_compact_eventual _ _ zero_le_one halfResolvent_cutoff_norm _ h
  intro q hq
  obtain ⟨R,_hR,hRq⟩ := hq.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop N] with n hn
  ext u
  by_cases hu : q u = 0
  · simp [hu]
  · have huR : u ≤ R := (le_abs_self u).trans (hRq u (subset_closure hu))
    have hun : u ≤ (n:ℝ) := huR.trans (hN.trans (by exact_mod_cast hn))
    change (Real.exp (min (n:ℝ) u / 2) : ℂ) * (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) * q u =
      (1 - (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ)) * q u
    rw [min_eq_right hun]
    congr 1
    have hp : Real.exp (u/2)+1 ≠ 0 := by positivity
    have heR : Real.exp (u/2) * (Real.exp (u/2)+1)⁻¹ = 1 - (Real.exp (u/2)+1)⁻¹ := by
      field_simp
      ring
    simpa only [Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one] using congrArg Complex.ofReal heR

lemma halfGraph_iff_resolvent (D : RealSpectralCalculus H) (x y : H) :
    (x,y) ∈ D.halfGraph ↔ D.calculus halfResolvent (x+y) = x := by
  constructor
  · intro hxy
    have ht : Tendsto (fun n => D.calculus halfResolvent (D.calculus (halfExponentialCutoff n) x))
      atTop (𝓝 (D.calculus halfResolvent y)) :=
      (D.calculus halfResolvent).continuous.tendsto y |>.comp hxy
    have heq : (fun n => D.calculus halfResolvent (D.calculus (halfExponentialCutoff n) x)) =
        (fun n => D.calculus (halfExponentialCutoff n * halfResolvent) x) := by
      funext n
      change (D.calculus halfResolvent * D.calculus (halfExponentialCutoff n)) x = _
      rw [← map_mul,mul_comm]
    rw [heq] at ht
    have hh := tendsto_nhds_unique ht (D.halfResolvent_cutoff_tendsto x)
    have hh' : D.calculus halfResolvent y = x - D.calculus halfResolvent x := by
      simpa using hh
    simp only [map_add,hh']
    abel
  · intro heq
    have ht := D.halfResolvent_cutoff_tendsto (x+y)
    have hfun : (fun n => D.calculus (halfExponentialCutoff n * halfResolvent) (x+y)) =
        (fun n => D.calculus (halfExponentialCutoff n) x) := by
      funext n
      rw [map_mul]
      change D.calculus (halfExponentialCutoff n) (D.calculus halfResolvent (x+y)) = _
      rw [heq]
    have hv : D.calculus (1-halfResolvent) (x+y) = y := by
      simp only [map_sub,map_one,sub_apply, one_apply_eq_self,heq]
      abel
    rw [hfun,hv] at ht
    exact ht

lemma halfGraph_isClosed (D : RealSpectralCalculus H) : IsClosed D.halfGraph := by
  have he : D.halfGraph = {p : H × H | D.calculus halfResolvent (p.1+p.2) = p.1} := by
    ext p
    exact D.halfGraph_iff_resolvent p.1 p.2
  rw [he]
  exact isClosed_eq ((D.calculus halfResolvent).continuous.comp (continuous_fst.add continuous_snd)) continuous_fst

lemma halfGraph_resolvent (D : RealSpectralCalculus H) (h : H) :
    (D.calculus halfResolvent h, h-D.calculus halfResolvent h) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent]
  congr 1
  abel

lemma halfGraph_unique (D : RealSpectralCalculus H) {x y z : H}
    (hxy : (x,y) ∈ D.halfGraph) (hxz : (x,z) ∈ D.halfGraph) : y=z :=
  tendsto_nhds_unique hxy hxz

lemma halfGraph_add (D : RealSpectralCalculus H) {x y a b : H}
    (hxy : (x,y) ∈ D.halfGraph) (hab : (a,b) ∈ D.halfGraph) : (x+a,y+b) ∈ D.halfGraph := by
  simpa only [halfGraph,mem_ofPred_eq,map_add] using hxy.add hab

lemma halfGraph_sub (D : RealSpectralCalculus H) {x y a b : H}
    (hxy : (x,y) ∈ D.halfGraph) (hab : (a,b) ∈ D.halfGraph) : (x-a,y-b) ∈ D.halfGraph := by
  simpa only [halfGraph,mem_ofPred_eq,map_sub] using hxy.sub hab

lemma halfGraph_symmetric (D : RealSpectralCalculus H) {x y a b : H}
    (hxy : (x,y) ∈ D.halfGraph) (hab : (a,b) ∈ D.halfGraph) :
    inner ℂ y a = inner ℂ x b := by
  have hstar (n : ℕ) : star (D.calculus (halfExponentialCutoff n)) = D.calculus (halfExponentialCutoff n) := by
    rw [← map_star]
    congr 1
    ext u
    change star ((Real.exp (min (n:ℝ) u / 2) : ℝ) : ℂ) = _
    simp only [Complex.star_def,Complex.conj_ofReal]
    rfl
  have he (n : ℕ) : inner ℂ (D.calculus (halfExponentialCutoff n) x) a =
      inner ℂ x (D.calculus (halfExponentialCutoff n) a) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x (star (D.calculus (halfExponentialCutoff n)) a) = _
    rw [hstar]
  exact tendsto_nhds_unique (hxy.inner tendsto_const_nhds)
    (by simpa only [he] using tendsto_const_nhds.inner hab)

lemma halfGraph_adjoint_iff (D : RealSpectralCalculus H) (x y : H) :
    (x,y) ∈ D.halfGraph ↔ ∀ a b, (a,b) ∈ D.halfGraph → inner ℂ y a = inner ℂ x b := by
  refine ⟨fun hxy a b hab => D.halfGraph_symmetric hxy hab, ?_⟩
  intro hh
  have hr : star (D.calculus halfResolvent) = D.calculus halfResolvent :=
    (halfResolvent_selfAdjoint.map D.calculus).star_eq
  rw [D.halfGraph_iff_resolvent]
  apply ext_inner_right ℂ
  intro k
  have hk := hh (D.calculus halfResolvent k) (k - D.calculus halfResolvent k) (D.halfGraph_resolvent k)
  rw [inner_sub_right] at hk
  have hs (u : H) : inner ℂ u (D.calculus halfResolvent k) = inner ℂ (D.calculus halfResolvent u) k := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (star (D.calculus halfResolvent) u) k = _
    rw [hr]
  rw [hs,hs] at hk
  rw [map_add,inner_add_left]
  exact (eq_add_of_sub_eq' hk.symm).symm

end RealSpectralCalculus
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

lemma antiunitary_inner (J : H ≃ₗᵢ⋆[ℂ] H) (x y : H) :
    inner ℂ (J x) (J y) = star (inner ℂ x y) := by
  have hre (a b : H) : (inner ℂ (J a) (J b)).re = (inner ℂ a b).re := by
    change RCLike.re (inner ℂ (J a) (J b)) = RCLike.re (inner ℂ a b)
    simp only [re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      ← map_add, J.norm_map]
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
    exact hre x y
  · have hi := hre x (Complex.I • y)
    have hJy : J (Complex.I • y) = (-Complex.I) • J y := by
      rw [J.map_smulₛₗ]
      congr 1
      exact Complex.conj_I
    rw [hJy] at hi
    rw [Complex.star_def, Complex.conj_im]
    simpa only [inner_smul_right, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_zero, neg_one_mul,
      sub_neg_eq_add, zero_add] using hi

namespace StandardModularData

lemma J_inner_flip (S : StandardModularData H) (x y : H) :
    inner ℂ (S.J x) y = inner ℂ (S.J y) x := by
  rw [← S.conjugation y, antiunitary_inner, S.conjugation]
  exact inner_conj_symm _ _

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

namespace BoundedRecovery
namespace StandardModularData

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tomita_graph_swap (S : StandardModularData H) {x y : H}
    (hxy : (x,y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) :
    (y,x) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
  have hc : IsClosed {p : H × H | p.swap ∈ closure {p : H × H |
      ∃ a : H →L[ℂ] H, a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}} :=
    isClosed_closure.preimage continuous_swap
  apply (closure_minimal (s := {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) ?_ hc) hxy
  rintro p ⟨a, ha, rfl⟩
  apply subset_closure
  exact ⟨star a, star_mem ha, by simp⟩

lemma halfGraph_flip (S : StandardModularData H) {x y : H}
    (hxy : (x,y) ∈ S.D.halfGraph) : (S.J y,S.J x) ∈ S.D.halfGraph := by
  have ht : (x,S.J y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨y,hxy,rfl⟩
  have hs := S.tomita_graph_swap ht
  rw [S.tomita_graph] at hs
  obtain ⟨q,hq,he⟩ := hs
  dsimp only at hq he
  have hqeq : q = S.J x := by rw [he, S.conjugation]
  rwa [hqeq] at hq

lemma commutant_halfGraph (S : StandardModularData H) (b : H →L[ℂ] H)
    (hb : b ∈ S.M.commutant) :
    (S.J (b S.xi), (star b) S.xi) ∈ S.D.halfGraph := by
  rw [S.D.halfGraph_adjoint_iff]
  intro x y hxy
  have ht : (x,S.J y) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨y,hxy,rfl⟩
  have hc : IsClosed {p : H × H |
      inner ℂ ((star b) S.xi) p.1 = inner ℂ p.2 (b S.xi)} :=
    isClosed_eq (continuous_const.inner continuous_fst) (continuous_snd.inner continuous_const)
  have he : inner ℂ ((star b) S.xi) x = inner ℂ (S.J y) (b S.xi) := by
    apply (closure_minimal (s := {p : H × H | ∃ a : H →L[ℂ] H,
        a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)}) ?_ hc) ht
    rintro p ⟨a,ha,rfl⟩
    change inner ℂ (ContinuousLinearMap.adjoint b S.xi) (a S.xi) =
      inner ℂ (ContinuousLinearMap.adjoint a S.xi) (b S.xi)
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ S.xi ((b*a) S.xi) = inner ℂ S.xi ((a*b) S.xi)
    rw [VonNeumannAlgebra.mem_commutant_iff.mp hb a ha]
  rw [he, S.J_inner_flip]

end StandardModularData
end BoundedRecovery

namespace BoundedRecovery

lemma exp_eq_sq_exp_half (u : ℝ) : Real.exp u = Real.exp (u/2) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

def modularResolvent (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (((Real.exp a + Real.exp u)⁻¹ : ℝ) : ℂ))
    (by fun_prop (disch := intros; positivity)) (Real.exp a)⁻¹ (by
      intro u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (inv_le_inv₀ (by positivity) (Real.exp_pos a)).mpr (le_add_of_nonneg_right (Real.exp_pos u).le))

def modularMixedResolvent (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => ((Real.exp (u/2) / (Real.exp a + Real.exp u) : ℝ) : ℂ))
    (by fun_prop (disch := intros; positivity)) ((2 * Real.exp (a/2))⁻¹) (by
      intro u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [← one_div (2 * Real.exp (a/2))]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [exp_eq_sq_exp_half a, exp_eq_sq_exp_half u]
      nlinarith [sq_nonneg (Real.exp (u/2) - Real.exp (a/2))])

namespace RealSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularResolvent_halfGraph (D : RealSpectralCalculus H) (a : ℝ) (h : H) :
    (D.calculus (modularResolvent a) h, D.calculus (modularMixedResolvent a) h) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent]
  change D.calculus halfResolvent ((D.calculus (modularResolvent a) +
    D.calculus (modularMixedResolvent a)) h) = D.calculus (modularResolvent a) h
  rw [← map_add]
  change (D.calculus halfResolvent * D.calculus (modularResolvent a + modularMixedResolvent a)) h = _
  rw [← map_mul]
  congr 2
  ext u
  change (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) *
    ((((Real.exp a+Real.exp u)⁻¹ : ℝ) : ℂ) +
      ((Real.exp (u/2)/(Real.exp a+Real.exp u) : ℝ) : ℂ)) =
    (((Real.exp a+Real.exp u)⁻¹ : ℝ) : ℂ)
  rw [← Complex.ofReal_add, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have h1 : Real.exp (u/2)+1 ≠ 0 := by positivity
  have h2 : Real.exp a+Real.exp u ≠ 0 := by positivity
  field_simp
  ring

lemma modularMixedResolvent_halfGraph (D : RealSpectralCalculus H) (a : ℝ) (h : H) :
    (D.calculus (modularMixedResolvent a) h,
      h - (Real.exp a : ℂ) • D.calculus (modularResolvent a) h) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent]
  have he : D.calculus (modularMixedResolvent a) h +
      (h-(Real.exp a:ℂ) • D.calculus (modularResolvent a) h) =
      D.calculus (modularMixedResolvent a + (1-(Real.exp a:ℂ) • modularResolvent a)) h := by simp
  rw [he]
  change (D.calculus halfResolvent * D.calculus
    (modularMixedResolvent a + (1-(Real.exp a:ℂ) • modularResolvent a))) h = _
  rw [← map_mul]
  congr 2
  ext u
  change (((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ) *
    (((Real.exp (u/2)/(Real.exp a+Real.exp u) : ℝ) : ℂ) +
      (1-(Real.exp a:ℂ)*(((Real.exp a+Real.exp u)⁻¹ : ℝ) : ℂ))) =
    ((Real.exp (u/2)/(Real.exp a+Real.exp u) : ℝ) : ℂ)
  rw [← Complex.ofReal_mul (Real.exp a), ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have h1 : Real.exp (u/2)+1 ≠ 0 := by positivity
  have h2 : Real.exp a+Real.exp u ≠ 0 := by positivity
  field_simp
  rw [exp_eq_sq_exp_half u]
  ring

end RealSpectralCalculus
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.PolarCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous functional calculus and bounded polar truncation in C*-algebras. -/

universe uA

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

namespace BoundedRecovery

def cutoffFunction (K r : ℝ) : ℝ := K / max K (Real.sqrt r)

lemma cutoffFunction_continuous {K : ℝ} (hK : 0 < K) :
    Continuous (cutoffFunction K) := by
  unfold cutoffFunction
  exact continuous_const.div (continuous_const.max Real.continuous_sqrt)
    (fun r => ne_of_gt (lt_of_lt_of_le hK (le_max_left _ _)))

lemma cutoffFunction_nonneg {K r : ℝ} (hK : 0 < K) :
    0 ≤ cutoffFunction K r := by
  exact div_nonneg hK.le (le_trans hK.le (le_max_left _ _))

lemma cutoffFunction_le_one {K r : ℝ} (hK : 0 < K) :
    cutoffFunction K r ≤ 1 := by
  exact (div_le_one (lt_of_lt_of_le hK (le_max_left _ _))).mpr (le_max_left _ _)

lemma cutoffFunction_eq_one {K r : ℝ} (hK : 0 < K) (hr : Real.sqrt r ≤ K) :
    cutoffFunction K r = 1 := by
  simp [cutoffFunction, max_eq_left hr, ne_of_gt hK]

lemma cutoffFunction_norm_bound {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) :
    cutoffFunction K r * r * cutoffFunction K r ≤ K ^ 2 := by
  have hs := Real.sq_sqrt hr
  by_cases h : Real.sqrt r ≤ K
  · rw [cutoffFunction_eq_one hK h]
    simp only [one_mul, mul_one]
    nlinarith [Real.sqrt_nonneg r]
  · have ht : 0 < Real.sqrt r := lt_trans hK (lt_of_not_ge h)
    rw [cutoffFunction, max_eq_right (le_of_not_ge h)]
    have heq : K / Real.sqrt r * r * (K / Real.sqrt r) = K ^ 2 := by
      field_simp
      nlinarith [hs]
    exact heq.le

section CStarCutoff

variable {A : Type uA} [CStarAlgebra A]

def polarCutoff (z : A) (K : ℝ) : A := z * cfc (cutoffFunction K) (star z * z)

lemma polarCutoff_square (z : A) {K : ℝ} (hK : 0 < K) :
    star (polarCutoff z K) * polarCutoff z K =
      cfc (fun r => cutoffFunction K r * r * cutoffFunction K r) (star z * z) := by
  have hc := cutoffFunction_continuous hK
  have ha : IsSelfAdjoint (star z * z) := by
    simp [IsSelfAdjoint]
  have hq : IsSelfAdjoint (cfc (cutoffFunction K) (star z * z)) := IsSelfAdjoint.cfc
  rw [cfc_mul (fun r => cutoffFunction K r * r) (cutoffFunction K) (star z * z)
      (hc.mul continuous_id).continuousOn hc.continuousOn,
    cfc_mul (cutoffFunction K) (fun r => r) (star z * z)
      hc.continuousOn continuous_id.continuousOn, cfc_id' ℝ _ ha]
  simp only [polarCutoff, star_mul, hq.star_eq]
  noncomm_ring

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_polarCutoff_le (z : A) {K : ℝ} (hK : 0 < K) :
    ‖polarCutoff z K‖ ≤ K := by
  have hh : ‖star (polarCutoff z K) * polarCutoff z K‖ ≤ K ^ 2 := by
    rw [polarCutoff_square z hK]
    apply norm_cfc_le (sq_nonneg K)
    intro r hr
    have hpos : 0 ≤ r := spectrum_nonneg_of_nonneg (star_mul_self_nonneg z) hr
    have hq := cutoffFunction_nonneg (r := r) hK
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact cutoffFunction_norm_bound hK hpos
  rw [CStarRing.norm_star_mul_self] at hh
  nlinarith [norm_nonneg (polarCutoff z K)]

end CStarCutoff

end BoundedRecovery

namespace BoundedRecovery

def cutoffLeftFunction (K r : ℝ) : ℝ :=
  Real.sqrt ((1 - cutoffFunction K r) / max K (Real.sqrt r))

def cutoffRightFunction (K r : ℝ) : ℝ :=
  Real.sqrt ((1 - cutoffFunction K r) * max K (Real.sqrt r))

lemma cutoffLeftFunction_continuous {K : ℝ} (hK : 0 < K) :
    Continuous (cutoffLeftFunction K) := by
  unfold cutoffLeftFunction
  exact Real.continuous_sqrt.comp ((continuous_const.sub (cutoffFunction_continuous hK)).div
    (continuous_const.max Real.continuous_sqrt)
    (fun r => ne_of_gt (lt_of_lt_of_le hK (le_max_left _ _))))

lemma cutoffRightFunction_continuous {K : ℝ} (hK : 0 < K) :
    Continuous (cutoffRightFunction K) := by
  unfold cutoffRightFunction
  exact Real.continuous_sqrt.comp ((continuous_const.sub (cutoffFunction_continuous hK)).mul
    (continuous_const.max Real.continuous_sqrt))

lemma cutoffLeftFunction_sq {K r : ℝ} (hK : 0 < K) :
    cutoffLeftFunction K r ^ 2 = (1 - cutoffFunction K r) / max K (Real.sqrt r) := by
  apply Real.sq_sqrt
  exact div_nonneg (sub_nonneg.mpr (cutoffFunction_le_one hK))
    (le_trans hK.le (le_max_left _ _))

lemma cutoffRightFunction_sq {K r : ℝ} (hK : 0 < K) :
    cutoffRightFunction K r ^ 2 = (1 - cutoffFunction K r) * max K (Real.sqrt r) := by
  apply Real.sq_sqrt
  exact mul_nonneg (sub_nonneg.mpr (cutoffFunction_le_one hK))
    (le_trans hK.le (le_max_left _ _))

lemma cutoffLeftFunction_mul_right {K r : ℝ} (hK : 0 < K) :
    cutoffLeftFunction K r * cutoffRightFunction K r = 1 - cutoffFunction K r := by
  have hm : max K (Real.sqrt r) ≠ 0 := ne_of_gt (lt_of_lt_of_le hK (le_max_left _ _))
  have hs : (cutoffLeftFunction K r * cutoffRightFunction K r) ^ 2 =
      (1 - cutoffFunction K r) ^ 2 := by
    rw [mul_pow, cutoffLeftFunction_sq hK, cutoffRightFunction_sq hK]
    field_simp
  have h1 : 0 ≤ cutoffLeftFunction K r * cutoffRightFunction K r :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 := cutoffFunction_le_one (r := r) hK
  nlinarith

lemma cutoff_right_loss {K r : ℝ} (hK : 0 < K) (hr : 0 ≤ r) :
    (2*K) * cutoffRightFunction K r ^ 2 ≤ r - cutoffFunction K r * r * cutoffFunction K r := by
  rw [cutoffRightFunction_sq hK]
  by_cases h : Real.sqrt r ≤ K
  · simp [cutoffFunction_eq_one hK h]
  · have ht : 0 < Real.sqrt r := hK.trans (lt_of_not_ge h)
    rw [cutoffFunction, max_eq_right (le_of_not_ge h)]
    have hs := Real.sq_sqrt hr
    apply (le_of_sub_nonneg ?_)
    have he : r - K / Real.sqrt r * r * (K / Real.sqrt r) -
        (2*K) * ((1-K / Real.sqrt r) * Real.sqrt r) = (Real.sqrt r - K)^2 := by
      field_simp
      nlinarith [hs]
    rw [he]
    positivity

lemma cutoff_left_loss {K r : ℝ} (hK : 0 < K) :
    (2*K) * cutoffLeftFunction K r ^ 2 ≤ 1 - cutoffFunction K r ^ 2 := by
  rw [cutoffLeftFunction_sq hK]
  have hm : 0 < max K (Real.sqrt r) := lt_of_lt_of_le hK (le_max_left _ _)
  rw [cutoffFunction]
  have he : 1 - (K / max K (Real.sqrt r)) ^ 2 -
      (2*K) * ((1-K / max K (Real.sqrt r)) / max K (Real.sqrt r)) =
      (1 - K / max K (Real.sqrt r)) ^ 2 := by ring
  exact le_of_sub_nonneg (he.symm ▸ sq_nonneg _)

section CStar
variable {A : Type uA} [CStarAlgebra A]

def cutoffLeft (a : A) (K : ℝ) : A :=
  a * cfc (cutoffLeftFunction K) (star a * a)

def cutoffRight (a : A) (K : ℝ) : A :=
  cfc (cutoffRightFunction K) (star a * a)

lemma cutoffLeft_mul_right (a : A) {K : ℝ} (hK : 0 < K) :
    cutoffLeft a K * cutoffRight a K = a - polarCutoff a K := by
  have ha : IsSelfAdjoint (star a * a) := by simp [IsSelfAdjoint]
  rw [cutoffLeft, cutoffRight, mul_assoc, ← cfc_mul _ _ _
    (cutoffLeftFunction_continuous hK).continuousOn (cutoffRightFunction_continuous hK).continuousOn]
  have hf : (fun r => cutoffLeftFunction K r * cutoffRightFunction K r) =
      (fun r => 1 - cutoffFunction K r) := funext (fun _ => cutoffLeftFunction_mul_right hK)
  rw [hf, cfc_sub _ _ _ continuous_const.continuousOn (cutoffFunction_continuous hK).continuousOn,
    cfc_const _ _ ha]
  simp [polarCutoff, mul_sub]

variable [PartialOrder A] [StarOrderedRing A]

lemma cutoffRight_loss (a : A) {K : ℝ} (hK : 0 < K) :
    (2*K) • (star (cutoffRight a K) * cutoffRight a K) ≤
      star a * a - star (polarCutoff a K) * polarCutoff a K := by
  have ha : IsSelfAdjoint (star a * a) := by simp [IsSelfAdjoint]
  have hr : IsSelfAdjoint (cutoffRight a K) := IsSelfAdjoint.cfc
  have heL : (2*K) • (star (cutoffRight a K) * cutoffRight a K) =
      cfc (fun r => (2*K) * cutoffRightFunction K r ^ 2) (star a * a) := by
    rw [cfc_const_mul (2*K) (fun r => cutoffRightFunction K r ^ 2) (star a * a)
      ((cutoffRightFunction_continuous hK).pow 2).continuousOn,
      cfc_pow (cutoffRightFunction K) 2 (star a * a)
        (cutoffRightFunction_continuous hK).continuousOn, hr.star_eq]
    simp only [cutoffRight, pow_two]
  have heR : star a * a - star (polarCutoff a K) * polarCutoff a K =
      cfc (fun r => r - cutoffFunction K r * r * cutoffFunction K r) (star a * a) := by
    rw [cfc_sub (fun r : ℝ => r) (fun r => cutoffFunction K r * r * cutoffFunction K r)
      (star a * a) continuous_id.continuousOn
      (((cutoffFunction_continuous hK).mul continuous_id).mul (cutoffFunction_continuous hK)).continuousOn,
      cfc_id' ℝ _ ha, polarCutoff_square a hK]
  rw [heL, heR]
  apply cfc_mono
    (hf := (continuous_const.mul ((cutoffRightFunction_continuous hK).pow 2)).continuousOn)
    (hg := (continuous_id.sub (((cutoffFunction_continuous hK).mul continuous_id).mul
      (cutoffFunction_continuous hK))).continuousOn)
  intro r hr
  exact cutoff_right_loss hK (spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) hr)

lemma cutoffLeft_loss (a : A) {K : ℝ} (hK : 0 < K) :
    (2*K) • (cutoffLeft a K * star (cutoffLeft a K)) ≤
      a * star a - polarCutoff a K * star (polarCutoff a K) := by
  have ha : IsSelfAdjoint (star a * a) := by simp [IsSelfAdjoint]
  have hl : IsSelfAdjoint (cfc (cutoffLeftFunction K) (star a * a)) := IsSelfAdjoint.cfc
  have hq : IsSelfAdjoint (cfc (cutoffFunction K) (star a * a)) := IsSelfAdjoint.cfc
  have hi : (2*K) • (cfc (cutoffLeftFunction K) (star a * a)) ^ 2 ≤
      1 - (cfc (cutoffFunction K) (star a * a)) ^ 2 := by
    have heL : (2*K) • (cfc (cutoffLeftFunction K) (star a * a)) ^ 2 =
        cfc (fun r => (2*K) * cutoffLeftFunction K r ^ 2) (star a * a) := by
      rw [cfc_const_mul (2*K) (fun r => cutoffLeftFunction K r ^ 2) (star a * a)
        ((cutoffLeftFunction_continuous hK).pow 2).continuousOn,
        cfc_pow (cutoffLeftFunction K) 2 (star a * a)
          (cutoffLeftFunction_continuous hK).continuousOn]
    have heR : 1 - (cfc (cutoffFunction K) (star a * a)) ^ 2 =
        cfc (fun r => 1 - cutoffFunction K r ^ 2) (star a * a) := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun r => cutoffFunction K r ^ 2) (star a * a)
        continuous_const.continuousOn ((cutoffFunction_continuous hK).pow 2).continuousOn,
        cfc_const _ _ ha, map_one, cfc_pow (cutoffFunction K) 2 (star a * a)
          (cutoffFunction_continuous hK).continuousOn]
    rw [heL, heR]
    apply cfc_mono
      (hf := (continuous_const.mul ((cutoffLeftFunction_continuous hK).pow 2)).continuousOn)
      (hg := (continuous_const.sub ((cutoffFunction_continuous hK).pow 2)).continuousOn)
    intro r _hr
    exact cutoff_left_loss hK
  have hh := star_right_conjugate_le_conjugate hi a
  simpa only [cutoffLeft, polarCutoff, star_mul, hl.star_eq, hq.star_eq, pow_two,
    mul_smul_comm, smul_mul_assoc, mul_sub, mul_one, sub_mul, mul_assoc] using hh

end CStar
end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.TomitaFundamental
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed Tomita relations and bounded transforms. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularEnergy (lam : ℝ) (b : H) (x y : H) : ℝ :=
  lam * ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (inner ℂ b x).re

namespace RealSpectralCalculus

lemma halfGraph_energy_identity (D : RealSpectralCalculus H) (lam : ℝ) (b : H)
    {z q x y : H} (hzq : (z,q) ∈ D.halfGraph)
    (hqb : (q,b-(lam:ℂ) • z) ∈ D.halfGraph) (hxy : (x,y) ∈ D.halfGraph) :
    modularEnergy lam b x y - modularEnergy lam b z q =
      lam * ‖x-z‖ ^ 2 + ‖y-q‖ ^ 2 := by
  have hh {u v : H} (huv : (u,v) ∈ D.halfGraph) :
      lam * (inner ℂ u z).re + (inner ℂ v q).re = (inner ℂ b u).re := by
    have he := congrArg Complex.re (D.halfGraph_symmetric huv hqb)
    simp only [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
    have hs : (inner ℂ b u).re = (inner ℂ u b).re := inner_re_symm (𝕜 := ℂ) b u
    rw [hs]
    linarith
  have he1 := hh hxy
  have he2 := hh hzq
  have hzsq : (inner ℂ z z).re = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) z
  have hqsq : (inner ℂ q q).re = ‖q‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) q
  rw [hzsq, hqsq] at he2
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  unfold modularEnergy
  change lam * ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (inner ℂ b x).re -
    (lam * ‖z‖ ^ 2 + ‖q‖ ^ 2 - 2 * (inner ℂ b z).re) =
    lam * (‖x‖ ^ 2 - 2 * (inner ℂ x z).re + ‖z‖ ^ 2) +
      (‖y‖ ^ 2 - 2 * (inner ℂ y q).re + ‖q‖ ^ 2)
  rw [← he1, ← he2]
  ring

end RealSpectralCalculus

namespace StandardModularData

lemma core_halfGraph (S : StandardModularData H) (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    (a S.xi, S.J ((star a) S.xi)) ∈ S.D.halfGraph := by
  have hh : (a S.xi, (star a) S.xi) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := subset_closure ⟨a, ha, rfl⟩
  rw [S.tomita_graph] at hh
  rcases hh with ⟨q, hq, he⟩
  change (star a) S.xi = S.J q at he
  rw [he, S.conjugation]
  exact hq

end StandardModularData

def vectorStateLM (xi : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun a := inner ℂ xi (a xi)
  map_add' a b := by simp
  map_smul' c a := by simp

lemma vectorState_star_mul (xi : H) (a : H →L[ℂ] H) :
    vectorStateLM xi (star a * a) = (‖a xi‖ ^ 2 : ℝ) := by
  change inner ℂ xi (ContinuousLinearMap.adjoint a (a xi)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

omit [CompleteSpace H] in
lemma re_vectorState_mono (xi : H) {a b : H →L[ℂ] H} (hab : a ≤ b) :
    (vectorStateLM xi a).re ≤ (vectorStateLM xi b).re := by
  have hp := ((ContinuousLinearMap.le_def _ _).mp hab).re_inner_nonneg_right xi
  change 0 ≤ (inner ℂ xi ((b - a) xi)).re at hp
  change (inner ℂ xi (a xi)).re ≤ (inner ℂ xi (b xi)).re
  simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hp

lemma vonNeumannAlgebra_isClosed (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  have he : (M : Set (H →L[ℂ] H)) =
      ⋂ (a : H →L[ℂ] H) (_ : a ∈ M.commutant), {b | a * b = b * a} := by
    ext b
    simp only [mem_iInter, mem_ofPred_eq, SetLike.mem_coe]
    have hh := @VonNeumannAlgebra.mem_commutant_iff H _ _ _ M.commutant b
    simpa only [M.commutant_commutant] using hh
  rw [he]
  exact isClosed_iInter (fun a => isClosed_iInter (fun _ =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)))

lemma polarCutoff_mem (M : VonNeumannAlgebra H) {z : H →L[ℂ] H} (hz : z ∈ M) (K : ℝ) :
    polarCutoff z K ∈ M := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed M
  have hc : cfc (cutoffFunction K) (star z * z) ∈ M.toStarSubalgebra :=
    cfc_mem (𝕜' := ℂ) (cutoffFunction K) (show star z * z ∈ M.toStarSubalgebra from mul_mem (star_mem hz) hz)
  exact mul_mem hz hc

lemma cutoffLeft_mem (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a ∈ M) (K : ℝ) :
    cutoffLeft a K ∈ M := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := vonNeumannAlgebra_isClosed M
  have hc : cfc (cutoffLeftFunction K) (star a * a) ∈ M.toStarSubalgebra :=
    cfc_mem (𝕜' := ℂ) (cutoffLeftFunction K) (show star a * a ∈ M.toStarSubalgebra from mul_mem (star_mem ha) ha)
  exact mul_mem ha hc

lemma vectorState_mul_star (xi : H) (a : H →L[ℂ] H) :
    vectorStateLM xi (a * star a) = (‖(star a) xi‖ ^ 2 : ℝ) := by
  simpa only [star_star] using vectorState_star_mul xi (star a)

lemma cutoffRight_vector_loss (xi : H) (a : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    (2*K) * ‖cutoffRight a K xi‖ ^ 2 ≤ ‖a xi‖ ^ 2 - ‖polarCutoff a K xi‖ ^ 2 := by
  have hh := re_vectorState_mono xi (cutoffRight_loss a hK)
  simpa only [map_sub, LinearMap.map_smul_of_tower, vectorState_star_mul,
    Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hh

lemma cutoffLeft_vector_loss (xi : H) (a : H →L[ℂ] H) {K : ℝ} (hK : 0 < K) :
    (2*K) * ‖star (cutoffLeft a K) xi‖ ^ 2 ≤
      ‖(star a) xi‖ ^ 2 - ‖star (polarCutoff a K) xi‖ ^ 2 := by
  have hh := re_vectorState_mono xi (cutoffLeft_loss a hK)
  simpa only [map_sub, LinearMap.map_smul_of_tower, vectorState_mul_star,
    Complex.sub_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul] using hh

lemma cutoff_cross_term (M : VonNeumannAlgebra H) (xi : H)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M.commutant) {K : ℝ} (hK : 0 < K) :
    2 * (inner ℂ (b xi) ((a-polarCutoff a K) xi)).re ≤
      ‖b‖ * (‖star (cutoffLeft a K) xi‖ ^ 2 + ‖cutoffRight a K xi‖ ^ 2) := by
  let l := cutoffLeft a K
  let r := cutoffRight a K
  have hc : (star l) * b = b * star l :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hb) (star l) (star_mem (cutoffLeft_mem M ha K))
  have he : inner ℂ (b xi) ((a-polarCutoff a K) xi) =
      inner ℂ (b ((star l) xi)) (r xi) := by
    rw [← cutoffLeft_mul_right a hK]
    change inner ℂ (b xi) (l (r xi)) = _
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (((star l) * b) xi) (r xi) = _
    rw [hc]
    rfl
  rw [he]
  have hh : (inner ℂ (b ((star l) xi)) (r xi)).re ≤ ‖b‖ * ‖(star l) xi‖ * ‖r xi‖ :=
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (b.le_opNorm _) (norm_nonneg _)))
  have hs := mul_nonneg (norm_nonneg b) (sq_nonneg (‖(star l) xi‖ - ‖r xi‖))
  change 2 * (inner ℂ (b ((star l) xi)) (r xi)).re ≤
    ‖b‖ * (‖(star l) xi‖ ^ 2 + ‖r xi‖ ^ 2)
  nlinarith

lemma cutoff_energy_le (M : VonNeumannAlgebra H) (xi : H)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M.commutant)
    {lam K : ℝ} (hlam : 0 ≤ lam) (hK : 0 < K) (h1 : ‖b‖ ≤ 2*K) (h2 : ‖b‖ ≤ lam*(2*K)) :
    modularEnergy lam (b xi) (polarCutoff a K xi) (star (polarCutoff a K) xi) ≤
      modularEnergy lam (b xi) (a xi) ((star a) xi) := by
  have hr := mul_le_mul_of_nonneg_left (cutoffRight_vector_loss xi a hK) hlam
  have hl := cutoffLeft_vector_loss xi a hK
  have hc := cutoff_cross_term M xi a b ha hb hK
  have h1' := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖star (cutoffLeft a K) xi‖)
  have h2' := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖cutoffRight a K xi‖)
  simp only [sub_apply, inner_sub_right, Complex.sub_re] at hc
  unfold modularEnergy
  nlinarith

def operatorOrbit (M : VonNeumannAlgebra H) (xi : H) : Submodule ℂ H where
  carrier := {h | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro h k ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, by simp⟩
  smul_mem' := by
    rintro c h ⟨a, ha, rfl⟩
    exact ⟨c • a, M.toStarSubalgebra.smul_mem ha c, by simp⟩

lemma operatorOrbit_invariant (M : VonNeumannAlgebra H) (xi : H)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    operatorOrbit M xi ∈ Module.End.invtSubmodule a := by
  intro h hh
  rcases hh with ⟨b, hb, rfl⟩
  exact ⟨a * b, mul_mem ha hb, rfl⟩

lemma commutant_cyclic (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0) :
    Dense (operatorOrbit M.commutant xi : Set H) := by
  let K := (operatorOrbit M.commutant xi).topologicalClosure
  have hP : K.starProjection ∈ M := by
    apply (VonNeumannAlgebra.IsStarProjection.mem_iff
      (isStarProjection_starProjection (U := K)) M).mpr
    intro a ha
    rw [Submodule.range_starProjection]
    exact Submodule.topologicalClosure_mem_invtSubmodule (operatorOrbit_invariant _ _ a ha)
  have hxi : xi ∈ K := by
    apply Submodule.le_topologicalClosure
    exact ⟨1, one_mem _, by simp⟩
  have heq : (1 : H →L[ℂ] H) - K.starProjection = 0 := by
    apply hsep _ (sub_mem (one_mem _) hP)
    simp [K.starProjection_eq_self_iff.mpr hxi]
  have htop : K = ⊤ := by
    apply top_unique
    intro h _
    have hp : K.starProjection h = h := by
      have := congrArg (fun a : H →L[ℂ] H => a h) heq
      exact (sub_eq_zero.mp this).symm
    exact K.starProjection_eq_self_iff.mp hp
  exact dense_iff_closure_eq.mpr (show closure (operatorOrbit M.commutant xi : Set H) = univ from
    congrArg (fun S : Submodule ℂ H => (S : Set H)) htop)

def operatorEvaluation (M : VonNeumannAlgebra H) (h : H) : M.toStarSubalgebra →ₗ[ℂ] H where
  toFun a := a.val h
  map_add' a b := by simp
  map_smul' c a := by simp

lemma bounded_orbit_lift (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0)
    {C : ℝ} (hC : 0 ≤ C) {h : H}
    (hh : h ∈ closure {v : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = v}) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = h := by
  let e := operatorEvaluation M.commutant xi
  let f := operatorEvaluation M.commutant h
  have hd : DenseRange e := by
    change Dense (Set.range e)
    have heq : Set.range e = (operatorOrbit M.commutant xi : Set H) := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.property, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    rw [heq]
    exact commutant_cyclic M xi hsep
  have hb : ∀ b : M.commutant.toStarSubalgebra, ‖f b‖ ≤ C * ‖e b‖ := by
    intro b
    change ‖b.val h‖ ≤ C * ‖b.val xi‖
    apply (isClosed_le (b.val.continuous.norm) continuous_const).closure_subset_iff.mpr ?_ hh
    rintro v ⟨a, ha, han, rfl⟩
    have hc := (VonNeumannAlgebra.mem_commutant_iff.mp b.property) a ha
    change ‖(b.val * a) xi‖ ≤ _
    rw [← hc]
    exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_right han (norm_nonneg _))
  let a := f.extendOfNorm e
  have hext (b : M.commutant.toStarSubalgebra) : a (b.val xi) = b.val h :=
    LinearMap.extendOfNorm_eq hd ⟨C, hb⟩ b
  have ham : a ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro b hbm
    let b' : M.commutant.toStarSubalgebra := ⟨b, hbm⟩
    apply ContinuousLinearMap.ext
    have heq : ∀ v ∈ Set.range e, (b * a) v = (a * b) v := by
      rintro v ⟨c, rfl⟩
      change b (a (c.val xi)) = a ((b * c.val) xi)
      rw [hext c]
      exact (hext (b' * c)).symm
    exact fun v => hd.induction heq (isClosed_eq (b * a).continuous (a * b).continuous) v
  refine ⟨a, ham, LinearMap.opNorm_extendOfNorm_le hd hC hb, ?_⟩
  simpa using hext 1

namespace StandardModularData

lemma fundamental_resolvent_lift (S : StandardModularData H) (r : ℝ)
    (b : H →L[ℂ] H) (hb : b ∈ S.M.commutant) :
    ∃ a : H →L[ℂ] H, a ∈ S.M ∧ ‖a‖ ≤ ‖b‖ * (1+(Real.exp r)⁻¹)+1 ∧
      a S.xi = S.D.calculus (modularResolvent r) (b S.xi) := by
  let lam := Real.exp r
  let z := S.D.calculus (modularResolvent r) (b S.xi)
  let q := S.D.calculus (modularMixedResolvent r) (b S.xi)
  let K := ‖b‖ * (1+lam⁻¹)+1
  have hlam : 0 < lam := Real.exp_pos r
  have hK : 0 < K := by dsimp [K]; positivity
  have h1 : ‖b‖ ≤ 2*K := by
    have hh : 0 ≤ ‖b‖ * lam⁻¹ := mul_nonneg (norm_nonneg b) (inv_nonneg.mpr hlam.le)
    dsimp [K]
    nlinarith [norm_nonneg b]
  have h2 : ‖b‖ ≤ lam*(2*K) := by
    have he : lam * K = ‖b‖ * (lam+1)+lam := by
      dsimp [K]
      field_simp
    nlinarith [mul_nonneg (norm_nonneg b) hlam.le, norm_nonneg b]
  have hzq : (z,q) ∈ S.D.halfGraph := S.D.modularResolvent_halfGraph r (b S.xi)
  have hqb : (q,b S.xi-(lam:ℂ) • z) ∈ S.D.halfGraph :=
    S.D.modularMixedResolvent_halfGraph r (b S.xi)
  have hg : (z,S.J q) ∈ closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ S.M ∧ p = (a S.xi, (star a) S.xi)} := by
    rw [S.tomita_graph]
    exact ⟨q,hzq,rfl⟩
  rcases mem_closure_iff_seq_limit.mp hg with ⟨p,hp,hpt⟩
  choose a ha he using hp
  have hxt : Tendsto (fun n => a n S.xi) atTop (𝓝 z) := by
    simpa only [he] using hpt.fst_nhds
  have hyt : Tendsto (fun n => (star (a n)) S.xi) atTop (𝓝 (S.J q)) := by
    simpa only [he] using hpt.snd_nhds
  have hEt : Tendsto (fun n => modularEnergy lam (b S.xi) (a n S.xi) ((star (a n)) S.xi) -
      modularEnergy lam (b S.xi) z q) atTop (𝓝 0) := by
    have hinner : Tendsto (fun n => (inner ℂ (b S.xi) (a n S.xi)).re) atTop
        (𝓝 (inner ℂ (b S.xi) z).re) :=
      Complex.continuous_re.tendsto _ |>.comp
        (tendsto_const_nhds.inner (𝕜 := ℂ) hxt)
    have ht : Tendsto (fun n => lam * ‖a n S.xi‖ ^ 2 +
        ‖(star (a n)) S.xi‖ ^ 2 - 2 * (inner ℂ (b S.xi) (a n S.xi)).re) atTop
        (𝓝 (lam * ‖z‖ ^ 2 + ‖S.J q‖ ^ 2 - 2 * (inner ℂ (b S.xi) z).re)) :=
      ((tendsto_const_nhds.mul (hxt.norm.pow 2)).add (hyt.norm.pow 2)).sub
        (tendsto_const_nhds.mul hinner)
    have ht' := ht.sub_const (modularEnergy lam (b S.xi) z q)
    simpa only [S.J.norm_map, modularEnergy, sub_self] using ht'
  have hbound (n : ℕ) :
      lam * ‖polarCutoff (a n) K S.xi-z‖ ^ 2 ≤
      modularEnergy lam (b S.xi) (a n S.xi) ((star (a n)) S.xi) -
        modularEnergy lam (b S.xi) z q := by
    have hc := cutoff_energy_le S.M S.xi (a n) b (ha n) hb hlam.le hK h1 h2
    have hi := S.D.halfGraph_energy_identity lam (b S.xi) hzq hqb
      (S.core_halfGraph (polarCutoff (a n) K) (polarCutoff_mem S.M (ha n) K))
    simp only [modularEnergy, S.J.norm_map] at hc hi ⊢
    nlinarith [sq_nonneg ‖S.J (star (polarCutoff (a n) K) S.xi) - q‖]
  have hct : Tendsto (fun n => polarCutoff (a n) K S.xi) atTop (𝓝 z) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hsmall := (tendsto_order.mp hEt).2 (lam*ε^2) (mul_pos hlam (sq_pos_of_pos hε))
    rcases eventually_atTop.mp hsmall with ⟨N,hN⟩
    refine ⟨N,fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hn' := (hbound n).trans_lt (hN n hn)
    have hs : ‖polarCutoff (a n) K S.xi-z‖^2 < ε^2 := (mul_lt_mul_iff_right₀ hlam).mp hn'
    nlinarith [norm_nonneg (polarCutoff (a n) K S.xi-z)]
  exact bounded_orbit_lift S.M S.xi S.separating hK.le
    (mem_closure_of_tendsto hct (Filter.Eventually.of_forall (fun n =>
      ⟨polarCutoff (a n) K, polarCutoff_mem S.M (ha n) K, norm_polarCutoff_le _ hK, rfl⟩)))

end StandardModularData
end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.RealGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Hilbert graphs and commutation with orthogonal projections. -/

universe u uE

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertPair (H : Type u) := WithLp 2 (H × H)

namespace HilbertPair

def pair (x y : H) : HilbertPair H := WithLp.toLp 2 (x,y)

def inl : H →L[ℂ] HilbertPair H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)

def inr : H →L[ℂ] HilbertPair H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)

omit [CompleteSpace H] in
@[simp] lemma inl_apply (x : H) : inl x = pair x 0 := rfl
omit [CompleteSpace H] in
@[simp] lemma inr_apply (x : H) : inr x = pair 0 x := rfl

omit [CompleteSpace H] in
@[simp] lemma fst_inl (x : H) : WithLp.fstL 2 ℂ H H (inl x) = x := rfl
omit [CompleteSpace H] in
@[simp] lemma snd_inl (x : H) : WithLp.sndL 2 ℂ H H (inl x) = 0 := rfl
omit [CompleteSpace H] in
@[simp] lemma fst_inr (x : H) : WithLp.fstL 2 ℂ H H (inr x) = 0 := rfl
omit [CompleteSpace H] in
@[simp] lemma snd_inr (x : H) : WithLp.sndL 2 ℂ H H (inr x) = x := rfl

omit [CompleteSpace H] in
@[simp] lemma inner_pair (x y z w : H) :
    inner ℂ (pair x y) (pair z w) = inner ℂ x z + inner ℂ y w := by
  exact WithLp.prod_inner_apply _ _

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma pair_add (x y z w : H) : pair (x+z) (y+w) = pair x y + pair z w := rfl

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma norm_pair_le (x y : H) : ‖pair x y‖ ≤ ‖x‖ + ‖y‖ := by
  have he : pair x y = pair x 0 + pair 0 y := by rw [← pair_add, add_zero, zero_add]
  rw [he]
  simpa only [pair, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using norm_add_le (pair x 0) (pair 0 y)

omit [CompleteSpace H] in
lemma pair_eq_inl_add_inr (x y : H) : pair x y = inl x + inr y := by
  rw [inl_apply, inr_apply, ← pair_add, add_zero, zero_add]

def diag (a : H →L[ℂ] H) : HilbertPair H →L[ℂ] HilbertPair H :=
  (inl.comp a).comp (WithLp.fstL 2 ℂ H H) +
    (inr.comp a).comp (WithLp.sndL 2 ℂ H H)

omit [CompleteSpace H] in
@[simp] lemma diag_pair (a : H →L[ℂ] H) (x y : H) :
    diag a (pair x y) = pair (a x) (a y) := by
  simp only [diag, add_apply, ContinuousLinearMap.comp_apply, inl_apply, inr_apply]
  change pair (a x) 0 + pair 0 (a y) = pair (a x) (a y)
  rw [← pair_add, add_zero, zero_add]

omit [CompleteSpace H] in
@[simp] lemma fst_diag (a : H →L[ℂ] H) (v : HilbertPair H) :
    WithLp.fstL 2 ℂ H H (diag a v) = a (WithLp.fstL 2 ℂ H H v) := by
  rcases v with ⟨x,y⟩
  exact congrArg (WithLp.fstL 2 ℂ H H) (diag_pair a x y)

omit [CompleteSpace H] in
@[simp] lemma snd_diag (a : H →L[ℂ] H) (v : HilbertPair H) :
    WithLp.sndL 2 ℂ H H (diag a v) = a (WithLp.sndL 2 ℂ H H v) := by
  rcases v with ⟨x,y⟩
  exact congrArg (WithLp.sndL 2 ℂ H H) (diag_pair a x y)

lemma star_diag (a : H →L[ℂ] H) : star (diag a) = diag (star a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  change inner ℂ (pair y₁ y₂) (star (diag a) (pair x₁ x₂)) =
    inner ℂ (pair y₁ y₂) (diag (star a) (pair x₁ x₂))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp only [diag_pair, inner_pair, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

lemma star_inl : inl.adjoint = WithLp.fstL 2 ℂ H H := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [inl_apply, pair]

lemma star_inr : inr.adjoint = WithLp.sndL 2 ℂ H H := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rcases x with ⟨x₁,x₂⟩
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [inr_apply, pair]

end HilbertPair

def orbitGraphMap (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    M.toStarSubalgebra →ₗ[ℂ] HilbertPair H where
  toFun a := HilbertPair.pair ((a : H →L[ℂ] H) xi) ((eps : ℂ) • (a : H →L[ℂ] H) z)
  map_add' a b := by
    change HilbertPair.pair _ ((eps:ℂ) • ((a:H →L[ℂ] H) z + (b:H →L[ℂ] H) z)) = _
    rw [smul_add]
    rfl
  map_smul' c a := by
    change HilbertPair.pair (c • (a:H →L[ℂ] H) xi) ((eps:ℂ) • (c • (a:H →L[ℂ] H) z)) = _
    rw [smul_comm (eps:ℂ) c]
    rfl

def orbitGraph (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    Submodule ℂ (HilbertPair H) := (orbitGraphMap M xi z eps).range.topologicalClosure

lemma orbitGraph_core_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    HilbertPair.pair (a xi) ((eps : ℂ) • a z) ∈ orbitGraph M xi z eps := by
  exact Submodule.le_topologicalClosure _ ⟨⟨a,ha⟩, rfl⟩

lemma orbitGraph_invariant (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    orbitGraph M xi z eps ∈ Module.End.invtSubmodule (HilbertPair.diag a) := by
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rintro x ⟨b,rfl⟩
  refine ⟨⟨a*(b : H →L[ℂ] H), mul_mem ha b.property⟩, ?_⟩
  change HilbertPair.pair _ _ = HilbertPair.diag a (HilbertPair.pair _ _)
  simp only [HilbertPair.diag_pair, mul_apply_eq_comp, map_smul]

lemma projection_commute_of_invariant {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (G : Submodule ℂ E)
    [G.HasOrthogonalProjection] (a : E →L[ℂ] E)
    (ha : G ∈ Module.End.invtSubmodule a)
    (hast : G ∈ Module.End.invtSubmodule (star a : E →L[ℂ] E)) : Commute G.starProjection a := by
  have h := G.isIdempotentElem_starProjection
  have hp := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff h).mp
    (by simpa only [Submodule.range_starProjection] using ha)
  have hpst := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff h).mp
    (by simpa only [Submodule.range_starProjection] using hast)
  change G.starProjection * a * G.starProjection = a * G.starProjection at hp
  change G.starProjection * star a * G.starProjection = star a * G.starProjection at hpst
  have hh := congrArg star hpst
  simp only [star_mul, star_star, (isSelfAdjoint_starProjection G).star_eq] at hh
  exact (hp.symm.trans ((mul_assoc _ _ _).trans hh)).symm

instance orbitGraph_hasProjection (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    (orbitGraph M xi z eps).HasOrthogonalProjection := by
  unfold orbitGraph
  infer_instance

lemma orbitGraph_projection_commute (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    Commute (orbitGraph M xi z eps).starProjection (HilbertPair.diag a) := by
  apply projection_commute_of_invariant
  · exact orbitGraph_invariant M xi z eps a ha
  · rw [HilbertPair.star_diag]
    exact orbitGraph_invariant M xi z eps (star a) (star_mem ha)

lemma orbitGraph_block_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (i j : Bool) :
    (if i then WithLp.sndL 2 ℂ H H else WithLp.fstL 2 ℂ H H).comp
      ((orbitGraph M xi z eps).starProjection.comp
        (if j then HilbertPair.inr else HilbertPair.inl)) ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  have hh := orbitGraph_projection_commute M xi z eps a ha
  apply ContinuousLinearMap.ext
  intro h
  have he := congrArg (fun A : HilbertPair H →L[ℂ] HilbertPair H =>
    A ((if j then HilbertPair.inr else HilbertPair.inl) h)) hh.eq
  have he' := congrArg
    (fun x : HilbertPair H => (if i then WithLp.sndL 2 ℂ H H else WithLp.fstL 2 ℂ H H) x) he
  cases i <;> cases j <;>
    simpa only [Bool.false_eq_true, ↓reduceIte, mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply, HilbertPair.inl_apply, HilbertPair.inr_apply,
      HilbertPair.diag_pair, HilbertPair.fst_diag, HilbertPair.snd_diag, map_zero] using he'.symm

def graphBlock (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (i j : Bool) : H →L[ℂ] H :=
  (if i then WithLp.sndL 2 ℂ H H else WithLp.fstL 2 ℂ H H).comp
    ((orbitGraph M xi z eps).starProjection.comp
      (if j then HilbertPair.inr else HilbertPair.inl))

lemma graphBlock_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (i j : Bool) :
    graphBlock M xi z eps i j ∈ M.commutant := orbitGraph_block_mem M xi z eps i j

lemma graphBlock_star (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (i j : Bool) :
    star (graphBlock M xi z eps i j) = graphBlock M xi z eps j i := by
  have hp : (orbitGraph M xi z eps).starProjection.adjoint =
      (orbitGraph M xi z eps).starProjection := (isSelfAdjoint_starProjection _).star_eq
  cases i <;> cases j <;>
    simp only [graphBlock, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ← HilbertPair.star_inl, ← HilbertPair.star_inr,
      ContinuousLinearMap.adjoint_adjoint, hp, ContinuousLinearMap.comp_assoc]

lemma orbitGraph_rot_mem_orthogonal (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    HilbertPair.pair (-(eps:ℂ) • a z) (a xi) ∈ (orbitGraph M xi z eps)ᗮ := by
  rw [orbitGraph, Submodule.orthogonal_closure]
  rintro x ⟨b,rfl⟩
  change inner ℂ (HilbertPair.pair ((b:H →L[ℂ] H) xi) ((eps:ℂ) • (b:H →L[ℂ] H) z))
    (HilbertPair.pair (-(eps:ℂ) • a z) (a xi)) = 0
  rw [HilbertPair.inner_pair, inner_smul_right, inner_smul_left]
  simp only [Complex.conj_ofReal]
  have hs : inner ℂ ((b:H →L[ℂ] H) xi) (a z) =
      inner ℂ ((b:H →L[ℂ] H) z) (a xi) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right]
    exact hz (star (b:H →L[ℂ] H) * a) (mul_mem (star_mem b.property) ha)
  rw [hs]
  ring

lemma projection_distance_le {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (G : Submodule ℂ E) [G.HasOrthogonalProjection]
    (x y : E) (hy : y ∈ G) : ‖G.starProjection x-x‖ ≤ ‖x-y‖ := by
  rw [norm_sub_rev, Submodule.starProjection_minimal]
  exact ciInf_le (show BddBelow (range (fun v : G => ‖x-(v:E)‖)) from
    ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩) (⟨y,hy⟩ : G)

lemma projection_norm_le_distance_orthogonal {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (G : Submodule ℂ E) [G.HasOrthogonalProjection]
    (x y : E) (hy : y ∈ Gᗮ) : ‖G.starProjection x‖ ≤ ‖x-y‖ := by
  have hh := projection_distance_le Gᗮ x y hy
  rw [G.starProjection_orthogonal_val] at hh
  simpa only [sub_sub_cancel_left, norm_neg] using hh

lemma orbitGraph_projection_inl_tendsto (M : VonNeumannAlgebra H) (xi z : H)
    (hcyc : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h})
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0)) (h : H) :
    Tendsto (fun n => (orbitGraph M xi z (eps n)).starProjection (HilbertPair.inl h))
      atTop (𝓝 (HilbertPair.inl h)) := by
  apply Metric.tendsto_atTop.mpr
  intro d hd
  obtain ⟨v,⟨a,ha,rfl⟩,hv⟩ := hcyc.exists_dist_lt h (show 0 < d/2 by positivity)
  have ht : Tendsto (fun n => ‖(eps n : ℂ) • a z‖) atTop (𝓝 0) := by
    have hh := (Complex.continuous_ofReal.tendsto _ |>.comp heps).smul_const (a z)
    convert hh.norm using 1 <;> simp
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (d/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hb := projection_distance_le (orbitGraph M xi z (eps n))
    (HilbertPair.inl h) (HilbertPair.pair (a xi) ((eps n:ℂ) • a z))
    (orbitGraph_core_mem M xi z (eps n) a ha)
  change _ ≤ ‖HilbertPair.pair (h-a xi) (0 - ((eps n:ℂ) • a z))‖ at hb
  rw [zero_sub] at hb
  have hl := hb.trans (HilbertPair.norm_pair_le _ _)
  simp only [norm_neg] at hl
  rw [dist_eq_norm] at hv
  linarith [hN n hn]

lemma orbitGraph_projection_inr_tendsto (M : VonNeumannAlgebra H) (xi z : H)
    (hcyc : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h})
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi))
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0)) (h : H) :
    Tendsto (fun n => (orbitGraph M xi z (eps n)).starProjection (HilbertPair.inr h))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro d hd
  obtain ⟨v,⟨a,ha,rfl⟩,hv⟩ := hcyc.exists_dist_lt h (show 0 < d/2 by positivity)
  have ht : Tendsto (fun n => ‖(eps n : ℂ) • a z‖) atTop (𝓝 0) := by
    have hh := (Complex.continuous_ofReal.tendsto _ |>.comp heps).smul_const (a z)
    convert hh.norm using 1 <;> simp
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (d/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  rw [dist_zero_right]
  have hb := projection_norm_le_distance_orthogonal (orbitGraph M xi z (eps n))
    (HilbertPair.inr h) (HilbertPair.pair (-(eps n:ℂ) • a z) (a xi))
    (orbitGraph_rot_mem_orthogonal M xi z (eps n) hz a ha)
  have he : HilbertPair.inr h - HilbertPair.pair (-(eps n:ℂ) • a z) (a xi) =
      HilbertPair.pair ((eps n:ℂ) • a z) (h-a xi) := by
    change HilbertPair.pair (0 - (-(eps n:ℂ) • a z)) (h-a xi) = _
    simp only [neg_smul, sub_neg_eq_add, zero_add]
  rw [he] at hb
  have hl := hb.trans (HilbertPair.norm_pair_le _ _)
  rw [dist_eq_norm] at hv
  linarith [hN n hn]

lemma graphBlock_offdiag_xi (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ)
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi)) :
    graphBlock M xi z eps true false xi =
        (eps:ℂ) • (z-graphBlock M xi z eps true true z) ∧
    graphBlock M xi z eps false true xi =
        (eps:ℂ) • graphBlock M xi z eps false false z := by
  let G := orbitGraph M xi z eps
  have hc : HilbertPair.pair xi ((eps:ℂ) • z) ∈ G := by
    simpa only [one_apply_eq_self] using orbitGraph_core_mem M xi z eps 1 (one_mem _)
  have ho : HilbertPair.pair (-(eps:ℂ) • z) xi ∈ Gᗮ := by
    simpa only [one_apply_eq_self] using orbitGraph_rot_mem_orthogonal M xi z eps hz 1 (one_mem _)
  have hc' := congrArg (WithLp.sndL 2 ℂ H H) (G.starProjection_eq_self_iff.mpr hc)
  have ho' := congrArg (WithLp.fstL 2 ℂ H H) (G.starProjection_apply_eq_zero_iff.mpr ho)
  rw [HilbertPair.pair_eq_inl_add_inr] at hc' ho'
  simp only [map_add, map_smul, map_zero, neg_smul, map_neg, HilbertPair.snd_inl,
    HilbertPair.snd_inr, zero_add] at hc' ho'
  constructor
  · change graphBlock M xi z eps true false xi +
      (eps:ℂ) • graphBlock M xi z eps true true z = (eps:ℂ) • z at hc'
    rw [smul_sub]
    exact eq_sub_iff_add_eq.mpr hc'
  · change -((eps:ℂ) • graphBlock M xi z eps false false z) +
      graphBlock M xi z eps false true xi = 0 at ho'
    exact (eq_of_neg_add_eq_zero ho').symm

def graphApproximant (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) : H →L[ℂ] H :=
  ((2*eps:ℝ):ℂ)⁻¹ • (graphBlock M xi z eps true false + graphBlock M xi z eps false true)

lemma graphApproximant_mem (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    graphApproximant M xi z eps ∈ M.commutant :=
  M.commutant.toStarSubalgebra.smul_mem
    (add_mem (graphBlock_mem M xi z eps _ _) (graphBlock_mem M xi z eps _ _)) _

lemma graphApproximant_selfAdjoint (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) :
    IsSelfAdjoint (graphApproximant M xi z eps) := by
  change star (graphApproximant M xi z eps) = _
  rw [graphApproximant, star_smul, star_add, graphBlock_star, graphBlock_star]
  simp only [map_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [add_comm]

lemma graphApproximant_xi (M : VonNeumannAlgebra H) (xi z : H) (eps : ℝ) (heps : eps ≠ 0)
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi)) :
    graphApproximant M xi z eps xi = (1/2:ℂ) •
      (z-graphBlock M xi z eps true true z + graphBlock M xi z eps false false z) := by
  rcases graphBlock_offdiag_xi M xi z eps hz with ⟨h1,h2⟩
  simp only [graphApproximant, smul_apply, add_apply, h1,h2, ← smul_add, smul_smul]
  congr 1
  have he : (eps:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr heps
  push_cast
  field_simp

lemma real_commutation (M : VonNeumannAlgebra H) (xi z : H)
    (hcyc : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h})
    (hz : ∀ a : H →L[ℂ] H, a ∈ M → inner ℂ xi (a z) = inner ℂ z (a xi)) :
    z ∈ closure {v : H | ∃ b : H →L[ℂ] H, b ∈ M.commutant ∧ IsSelfAdjoint b ∧ b xi = v} := by
  let eps (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have heps : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepne (n : ℕ) : eps n ≠ 0 := by dsimp [eps]; positivity
  have hf : Tendsto (fun n => graphBlock M xi z (eps n) false false z) atTop (𝓝 z) := by
    exact ((WithLp.fstL 2 ℂ H H).continuous.tendsto _).comp
      (orbitGraph_projection_inl_tendsto M xi z hcyc eps heps z)
  have hs : Tendsto (fun n => graphBlock M xi z (eps n) true true z) atTop (𝓝 0) := by
    convert ((WithLp.sndL 2 ℂ H H).continuous.tendsto _).comp
      (orbitGraph_projection_inr_tendsto M xi z hcyc hz eps heps z) using 1 <;>
      simp [graphBlock, Function.comp_def]
  have ht : Tendsto (fun n => graphApproximant M xi z (eps n) xi) atTop (𝓝 z) := by
    have hh : Tendsto (fun n => (1/2:ℂ) •
        (z-graphBlock M xi z (eps n) true true z + graphBlock M xi z (eps n) false false z))
        atTop (𝓝 ((1/2:ℂ) • (z-0+z))) :=
      ((tendsto_const_nhds.sub hs).add hf).const_smul (1/2:ℂ)
    have he : (1/2:ℂ) • (z-0+z) = z := by module
    simpa only [graphApproximant_xi M xi z _ (hepne _) hz, he] using hh
  exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall (fun n =>
    ⟨graphApproximant M xi z (eps n), graphApproximant_mem _ _ _ _,
      graphApproximant_selfAdjoint _ _ _ _,rfl⟩))

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.Commutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The commutant core and reverse operators. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus
lemma halfGraph_smul (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x,y) ∈ D.halfGraph) (c : ℂ) : (c • x,c • y) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent] at hxy ⊢
  rw [← smul_add, map_smul, hxy]
end RealSpectralCalculus

namespace StandardModularData

lemma fixed_adjoint_core_approx (S : StandardModularData H) {z : H}
    (hz : (S.J z,z) ∈ S.D.halfGraph) :
    z ∈ closure {v : H | ∃ b : H →L[ℂ] H,
      b ∈ S.M.commutant ∧ IsSelfAdjoint b ∧ b S.xi = v} := by
  apply real_commutation S.M S.xi z S.cyclic
  intro a ha
  have hi := S.D.halfGraph_symmetric hz (S.core_halfGraph a ha)
  rw [antiunitary_inner] at hi
  change inner ℂ z (a S.xi) = (starRingEnd ℂ) (inner ℂ z ((star a) S.xi)) at hi
  rw [inner_conj_symm] at hi
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hi.symm

lemma commutant_tomita_graph (S : StandardModularData H) :
    closure {p : H × H | ∃ b : H →L[ℂ] H,
      b ∈ S.M.commutant ∧ p = (b S.xi, (star b) S.xi)} =
      {p | (S.J p.1,p.2) ∈ S.D.halfGraph} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro p ⟨b,hb,rfl⟩
      exact S.commutant_halfGraph b hb
    · exact S.D.halfGraph_isClosed.preimage (S.J.continuous.comp continuous_fst |>.prodMk continuous_snd)
  · rintro ⟨x,y⟩ hxy
    change (S.J x,y) ∈ S.D.halfGraph at hxy
    have hyx : (S.J y,x) ∈ S.D.halfGraph := by
      have hh := S.halfGraph_flip hxy
      change (S.J y,S.J (S.J x)) ∈ S.D.halfGraph at hh
      rwa [S.conjugation x] at hh
    let z₁ := (1/2:ℂ) • (x+y)
    let z₂ := (-Complex.I/2:ℂ) • (x-y)
    have h₁ : (S.J z₁,z₁) ∈ S.D.halfGraph := by
      have he : S.J z₁ = (1/2:ℂ) • (S.J x+S.J y) := by
        simp [z₁, map_smulₛₗ, map_ofNat]
      rw [he]
      convert S.D.halfGraph_smul (S.D.halfGraph_add hxy hyx) (1/2:ℂ) using 1
      exact congrArg (fun v : H => ((1/2:ℂ) • (S.J x+S.J y),v))
        (by dsimp [z₁]; rw [add_comm])
    have h₂ : (S.J z₂,z₂) ∈ S.D.halfGraph := by
      have he : S.J z₂ = (Complex.I/2) • (S.J x-S.J y) := by
        simp [z₂, map_smulₛₗ, map_ofNat]
      rw [he]
      convert S.D.halfGraph_smul (S.D.halfGraph_sub hxy hyx) (Complex.I/2) using 1
      congr 1
      dsimp [z₂]; module
    obtain ⟨f,hf,hft⟩ := mem_closure_iff_seq_limit.mp (S.fixed_adjoint_core_approx h₁)
    obtain ⟨g,hg,hgt⟩ := mem_closure_iff_seq_limit.mp (S.fixed_adjoint_core_approx h₂)
    choose b hb hbs hbxi using hf
    choose c hc hcs hcxi using hg
    have hx : z₁ + Complex.I • z₂ = x := by
      dsimp [z₁,z₂]
      rw [smul_smul]
      have hi : Complex.I * (-Complex.I/2) = (1/2:ℂ) := by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
        norm_num
      rw [hi]
      module
    have hy : z₁ - Complex.I • z₂ = y := by
      dsimp [z₁,z₂]
      rw [smul_smul]
      have hi : Complex.I * (-Complex.I/2) = (1/2:ℂ) := by
        rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
        norm_num
      rw [hi]
      module
    have ht : Tendsto (fun n => ((b n + Complex.I • c n) S.xi,
        (star (b n + Complex.I • c n)) S.xi)) atTop (𝓝 (x,y)) := by
      convert (hft.add (hgt.const_smul Complex.I)).prodMk_nhds
        (hft.sub (hgt.const_smul Complex.I)) using 1
      · ext n <;> simp [star_add, star_smul, (hbs n).star_eq, (hcs n).star_eq,
          hbxi n, hcxi n, sub_eq_add_neg]
      · rw [hx,hy]
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n =>
      ⟨b n + Complex.I • c n,
        add_mem (hb n) (S.M.commutant.toStarSubalgebra.smul_mem (hc n) _), rfl⟩))

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralReflection : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ]
    (BoundedContinuousFunction ℝ ℂ) where
  toFun f := f.compContinuous ⟨Neg.neg,continuous_neg⟩
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' _ := by ext; rfl

@[simp] lemma spectralReflection_apply (f : BoundedContinuousFunction ℝ ℂ) (u : ℝ) :
    spectralReflection f u = f (-u) := rfl

@[simp] lemma spectralReflection_involutive (f : BoundedContinuousFunction ℝ ℂ) :
    spectralReflection (spectralReflection f) = f := by ext; simp

lemma spectralReflection_halfResolvent : spectralReflection halfResolvent = 1-halfResolvent := by
  ext u
  change (((Real.exp (-u/2)+1)⁻¹ : ℝ) : ℂ) = 1-(((Real.exp (u/2)+1)⁻¹ : ℝ) : ℂ)
  have he : -u/2 = -(u/2) := by ring
  rw [he, Real.exp_neg]
  have hpos := Real.exp_pos (u/2)
  have heq : ((Real.exp (u/2))⁻¹+1)⁻¹ = 1-(Real.exp (u/2)+1)⁻¹ := by
    field_simp
    ring
  exact_mod_cast heq

namespace RealSpectralCalculus

def reverse (D : RealSpectralCalculus H) : RealSpectralCalculus H where
  calculus := D.calculus.comp spectralReflection
  nondegenerate := D.nondegenerate.mono (by
    rintro h ⟨f,hf,k,rfl⟩
    exact ⟨spectralReflection f,hf.comp_homeomorph (Homeomorph.neg ℝ),k,
      by simp only [StarAlgHom.comp_apply, spectralReflection_involutive]⟩)

lemma reverse_halfGraph (D : RealSpectralCalculus H) (x y : H) :
    (x,y) ∈ D.reverse.halfGraph ↔ (y,x) ∈ D.halfGraph := by
  rw [D.reverse.halfGraph_iff_resolvent, D.halfGraph_iff_resolvent]
  change D.calculus (spectralReflection halfResolvent) (x+y) = x ↔ _
  rw [spectralReflection_halfResolvent, map_sub, map_one]
  simp only [sub_apply, one_apply_eq_self]
  rw [add_comm x y]
  constructor
  · intro he
    have hz : y+x - D.calculus halfResolvent (y+x) - x = 0 := by rw [he,sub_self]
    have he' : y-D.calculus halfResolvent (y+x) = 0 := by convert hz using 1; abel
    exact (sub_eq_zero.mp he').symm
  · intro he
    rw [he]
    abel

end RealSpectralCalculus

namespace StandardModularData

lemma commutant_separating (S : StandardModularData H) (b : H →L[ℂ] H)
    (hb : b ∈ S.M.commutant) (hbxi : b S.xi = 0) : b = 0 := by
  apply ContinuousLinearMap.ext
  intro h
  change b h = 0
  refine S.cyclic.induction ?_ (isClosed_eq b.continuous continuous_const) h
  rintro v ⟨a,ha,rfl⟩
  have he := congrArg (fun A : H →L[ℂ] H => A S.xi)
    (VonNeumannAlgebra.mem_commutant_iff.mp hb a ha)
  simpa only [mul_apply_eq_comp, hbxi, map_zero] using he.symm

def commutantData (S : StandardModularData H) : StandardModularData H where
  M := S.M.commutant
  xi := S.xi
  norm_xi := S.norm_xi
  cyclic := commutant_cyclic S.M S.xi S.separating
  separating := S.commutant_separating
  D := S.D.reverse
  J := S.J
  conjugation := S.conjugation
  tomita_graph := by
    rw [S.commutant_tomita_graph]
    ext p
    change (S.J p.1,p.2) ∈ S.D.halfGraph ↔ ∃ q,
      (p.1,q) ∈ S.D.reverse.halfGraph ∧ p.2 = S.J q
    constructor
    · intro hp
      refine ⟨S.J p.2,?_,(S.conjugation p.2).symm⟩
      rw [S.D.reverse_halfGraph]
      have hh := S.halfGraph_flip hp
      change (S.J p.2,S.J (S.J p.1)) ∈ S.D.halfGraph at hh
      rwa [S.conjugation p.1] at hh
    · rintro ⟨q,hq,he⟩
      rw [S.D.reverse_halfGraph] at hq
      have hh := S.halfGraph_flip hq
      change (S.J p.1,S.J q) ∈ S.D.halfGraph at hh
      rwa [← he] at hh

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.PositiveKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive operator kernels, matrix pairings, and norm bounds. -/

universe u uA uM uN

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open scoped ComplexConjugate
namespace BoundedRecovery

section Matrices
variable {A : Type uA} {n : Type uN} [CStarAlgebra A] [Fintype n]

def weightedMatrixFunctional (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ) :
    CStarMatrix n n A →ₗ[ℂ] ℂ where
  toFun a := ∑ i, (w i : ℂ) * φ (a i i)
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_left_comm]

end Matrices
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardModularData

def phi (S : StandardModularData H) : S.M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun a := inner ℂ S.xi ((a : H →L[ℂ] H) S.xi)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma phi_star_mul (S : StandardModularData H) (a : S.M.toStarSubalgebra) :
    (S.phi (star a*a)).re = ‖(a : H →L[ℂ] H) S.xi‖^2 := by
  change ((vectorStateLM S.xi) (star (a:H →L[ℂ] H)*(a:H →L[ℂ] H))).re = _
  rw [vectorState_star_mul]
  rfl

lemma phi_nonneg (S : StandardModularData H) (a : S.M.toStarSubalgebra) :
    0 ≤ (S.phi (star a*a)).re := by rw [S.phi_star_mul]; positivity

lemma phi_faithful (S : StandardModularData H) (a : S.M.toStarSubalgebra)
    (ha : (S.phi (star a*a)).re = 0) : a = 0 := by
  apply Subtype.ext
  apply S.separating a a.property
  rw [S.phi_star_mul] at ha
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ha)

lemma phi_star (S : StandardModularData H) (a : S.M.toStarSubalgebra) :
    S.phi (star a) = star (S.phi a) := by
  change inner ℂ S.xi ((star (a : H →L[ℂ] H)) S.xi) = star (inner ℂ S.xi ((a : H →L[ℂ] H) S.xi))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

def commutingPairing (S : StandardModularData H) (b : S.M.commutant.toStarSubalgebra) :
    S.M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun c := inner ℂ S.xi ((b : H →L[ℂ] H) ((c : H →L[ℂ] H) S.xi))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma commutingPairing_star (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) (c : S.M.toStarSubalgebra) :
    S.commutingPairing (star b) (star c) = star (S.commutingPairing b c) := by
  change inner ℂ S.xi (((star (b:H →L[ℂ] H)) * star (c:H →L[ℂ] H)) S.xi) = _
  rw [← star_mul]
  change inner ℂ S.xi (star ((c:H →L[ℂ] H)*(b:H →L[ℂ] H)) S.xi) = _
  rw [VonNeumannAlgebra.mem_commutant_iff.mp b.property c c.property]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

def modularLift (S : StandardModularData H) (r : ℝ) (b : S.M.commutant.toStarSubalgebra) :
    S.M.toStarSubalgebra :=
  ⟨Classical.choose (S.fundamental_resolvent_lift r b b.property),
    (Classical.choose_spec (S.fundamental_resolvent_lift r b b.property)).1⟩

lemma modularLift_xi (S : StandardModularData H) (r : ℝ) (b : S.M.commutant.toStarSubalgebra) :
    (S.modularLift r b : H →L[ℂ] H) S.xi = S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi) :=
  (Classical.choose_spec (S.fundamental_resolvent_lift r b b.property)).2.2

lemma eq_of_xi (S : StandardModularData H) (a c : S.M.toStarSubalgebra)
    (he : (a:H →L[ℂ] H) S.xi = (c:H →L[ℂ] H) S.xi) : a = c := by
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply S.separating (↑(a-c)) (a-c).property
  change (a:H →L[ℂ] H) S.xi - (c:H →L[ℂ] H) S.xi = 0
  exact sub_eq_zero.mpr he

lemma modularLift_add (S : StandardModularData H) (r : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.modularLift r (b+c) = S.modularLift r b + S.modularLift r c := by
  apply S.eq_of_xi
  rw [S.modularLift_xi]
  change S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi+(c:H →L[ℂ] H) S.xi) =
    (S.modularLift r b:H →L[ℂ] H) S.xi+(S.modularLift r c:H →L[ℂ] H) S.xi
  rw [map_add,S.modularLift_xi,S.modularLift_xi]

lemma modularLift_smul (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : ℂ) :
    S.modularLift r (c • b) = c • S.modularLift r b := by
  apply S.eq_of_xi
  rw [S.modularLift_xi]
  change S.D.calculus (modularResolvent r) (c • (b:H →L[ℂ] H) S.xi) =
    c • (S.modularLift r b:H →L[ℂ] H) S.xi
  rw [map_smul,S.modularLift_xi]

lemma modularLift_weakEquation (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : S.M.toStarSubalgebra) :
    (Real.exp r:ℂ) * S.phi (c*S.modularLift r b) + S.phi (S.modularLift r b*c) =
      S.commutingPairing b c := by
  let a := S.modularLift r b
  have ha : (a:H →L[ℂ] H) S.xi = S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi) :=
    S.modularLift_xi r b
  have hq : S.D.calculus (modularMixedResolvent r) ((b:H →L[ℂ] H) S.xi) =
      S.J ((star (a:H →L[ℂ] H)) S.xi) := by
    apply S.D.halfGraph_unique
    · exact S.D.modularResolvent_halfGraph r ((b:H →L[ℂ] H) S.xi)
    · rw [← ha]
      exact S.core_halfGraph a a.property
  have hc := S.core_halfGraph (star (c:H →L[ℂ] H)) (star_mem c.property)
  simp only [star_star] at hc
  have hh := S.D.halfGraph_symmetric hc
    (S.D.modularMixedResolvent_halfGraph r ((b:H →L[ℂ] H) S.xi))
  rw [hq,antiunitary_inner] at hh
  change (starRingEnd ℂ) (inner ℂ ((c:H →L[ℂ] H) S.xi) ((star (a:H →L[ℂ] H)) S.xi)) = _ at hh
  rw [inner_conj_symm, inner_sub_right, inner_smul_right, ← ha] at hh
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] at hh
  have hcomm := congrArg (fun A : H →L[ℂ] H => A S.xi)
    (VonNeumannAlgebra.mem_commutant_iff.mp b.property c c.property)
  change (c:H →L[ℂ] H) ((b:H →L[ℂ] H) S.xi) = (b:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi) at hcomm
  rw [hcomm] at hh
  change (Real.exp r:ℂ)*inner ℂ S.xi ((c:H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)) +
    inner ℂ S.xi ((a:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi)) =
      inner ℂ S.xi ((b:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi))
  linear_combination hh

lemma weakEquation_zero (S : StandardModularData H) (r : ℝ) (a : S.M.toStarSubalgebra)
    (ha : ∀ c : S.M.toStarSubalgebra,
      (Real.exp r:ℂ)*S.phi (c*a) + S.phi (a*c) = 0) : a = 0 := by
  have hh := congrArg Complex.re (ha (star a))
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.zero_re] at hh
  have hp := S.phi_nonneg a
  have hq := S.phi_nonneg (star a)
  rw [star_star] at hq
  apply S.phi_faithful
  nlinarith [Real.exp_pos r]

lemma eq_of_weakEquation (S : StandardModularData H) (r : ℝ)
    (a d : S.M.toStarSubalgebra)
    (he : ∀ c : S.M.toStarSubalgebra,
      (Real.exp r:ℂ)*S.phi (c*a) + S.phi (a*c) =
        (Real.exp r:ℂ)*S.phi (c*d) + S.phi (d*c)) : a = d := by
  apply sub_eq_zero.mp
  apply S.weakEquation_zero r
  intro c
  simp only [mul_sub, sub_mul, map_sub]
  linear_combination he c

def modularKernel (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : S.M.toStarSubalgebra :=
  (Real.exp (r/2):ℂ) • S.modularLift r b

lemma modularKernel_add (S : StandardModularData H) (r : ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.modularKernel r (b+c) = S.modularKernel r b + S.modularKernel r c := by
  simp only [modularKernel,modularLift_add,smul_add]

lemma modularKernel_smul (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : ℂ) :
    S.modularKernel r (c • b) = c • S.modularKernel r b := by
  unfold modularKernel
  rw [modularLift_smul]
  exact smul_comm _ _ _

lemma modularKernel_weakEquation (S : StandardModularData H) (r : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (c : S.M.toStarSubalgebra) :
    (Real.exp r:ℂ) * S.phi (c*S.modularKernel r b) + S.phi (S.modularKernel r b*c) =
      (Real.exp (r/2):ℂ) * S.commutingPairing b c := by
  simp only [modularKernel,mul_smul_comm,smul_mul_assoc,map_smul,smul_eq_mul]
  linear_combination (Real.exp (r/2):ℂ) * S.modularLift_weakEquation r b c

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

section MatrixPairing
variable {A : Type uA} {n : Type uN} [CStarAlgebra A] [Fintype n]

lemma weightedMatrixFunctional_jordan (φ : A →ₗ[ℂ] ℂ) (w : n → ℝ)
    (X Y : CStarMatrix n n A) :
    weightedMatrixFunctional φ w (X*Y+Y*X) =
      ∑ i, ∑ j, ((w i:ℂ)*φ (X i j*Y j i)+(w j:ℂ)*φ (Y j i*X i j)) := by
  simp only [weightedMatrixFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    CStarMatrix.mul_apply, map_add, map_sum,
    Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end MatrixPairing

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
instance vonNeumannAlgebra_cstar (M : VonNeumannAlgebra H) : CStarAlgebra M.toStarSubalgebra :=
  StarSubalgebra.cstarAlgebra _ (h_closed := vonNeumannAlgebra_isClosed M)

namespace StandardModularData

lemma commuting_apply (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) (a : S.M.toStarSubalgebra) (h : H) :
    (b:H →L[ℂ] H) ((a:H →L[ℂ] H) h) = (a:H →L[ℂ] H) ((b:H →L[ℂ] H) h) :=
  (congrArg (fun A : H →L[ℂ] H => A h)
    (VonNeumannAlgebra.mem_commutant_iff.mp b.property a a.property)).symm

lemma commutingPairing_gram (S : StandardModularData H)
    (b d : S.M.commutant.toStarSubalgebra) (a c : S.M.toStarSubalgebra) :
    S.commutingPairing (star d*b) (star c*a) =
      inner ℂ ((d:H →L[ℂ] H) ((c:H →L[ℂ] H) S.xi))
        ((b:H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)) := by
  change inner ℂ S.xi ((star (d:H →L[ℂ] H))
    ((b:H →L[ℂ] H) ((star (c:H →L[ℂ] H)) ((a:H →L[ℂ] H) S.xi)))) = _
  change inner ℂ S.xi ((↑(star d):H →L[ℂ] H)
    ((b:H →L[ℂ] H) ((↑(star c):H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)))) = _
  rw [S.commuting_apply b (star c), S.commuting_apply (star d) (star c)]
  change inner ℂ S.xi ((star (c:H →L[ℂ] H))
    ((star (d:H →L[ℂ] H)) ((b:H →L[ℂ] H) ((a:H →L[ℂ] H) S.xi)))) = _
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

def modularGram {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) : CStarMatrix n n S.M.toStarSubalgebra :=
  CStarMatrix.ofMatrix (fun i j => S.modularKernel (r i-r j) (star (b j)*b i))

@[simp] lemma modularGram_apply {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) (i j : n) :
    S.modularGram r b i j = S.modularKernel (r i-r j) (star (b j)*b i) := rfl

lemma modularGram_equation {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) (i j : n) (c : S.M.toStarSubalgebra) :
    (Real.exp (-r i):ℂ)*S.phi (S.modularGram r b i j*c) +
      (Real.exp (-r j):ℂ)*S.phi (c*S.modularGram r b i j) =
    (Real.exp (-r i/2):ℂ)*(Real.exp (-r j/2):ℂ) *
      S.commutingPairing (star (b j)*b i) c := by
  have he : (Real.exp (-r i):ℂ)*(Real.exp (r i-r j):ℂ) = (Real.exp (-r j):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  have heh : (Real.exp (-r i):ℂ)*(Real.exp ((r i-r j)/2):ℂ) =
      (Real.exp (-r i/2):ℂ)*(Real.exp (-r j/2):ℂ) := by
    rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Real.exp_add,← Real.exp_add]
    congr 2
    ring
  change (Real.exp (-r i):ℂ)*S.phi (S.modularKernel (r i-r j) (star (b j)*b i)*c) +
    (Real.exp (-r j):ℂ)*S.phi (c*S.modularKernel (r i-r j) (star (b j)*b i)) = _
  linear_combination (Real.exp (-r i):ℂ)*S.modularKernel_weakEquation (r i-r j) (star (b j)*b i) c -
    S.phi (c*S.modularKernel (r i-r j) (star (b j)*b i))*he +
    S.commutingPairing (star (b j)*b i) c*heh

lemma modularGram_pairing {n : Type uN} [Fintype n] (S : StandardModularData H) (r : n → ℝ)
    (b : n → S.M.commutant.toStarSubalgebra) (Z : CStarMatrix n n S.M.toStarSubalgebra) :
    weightedMatrixFunctional S.phi (fun i => Real.exp (-r i))
      (S.modularGram r b*(star Z*Z)+(star Z*Z)*S.modularGram r b) =
    ∑ k, inner ℂ (∑ i, (Real.exp (-r i/2):ℂ) • (b i:H →L[ℂ] H) ((Z k i:H →L[ℂ] H) S.xi))
      (∑ i, (Real.exp (-r i/2):ℂ) • (b i:H →L[ℂ] H) ((Z k i:H →L[ℂ] H) S.xi)) := by
  rw [weightedMatrixFunctional_jordan]
  simp only [S.modularGram_equation]
  simp only [CStarMatrix.mul_apply,CStarMatrix.star_eq_conjTranspose,
    CStarMatrix.conjTranspose_apply,map_sum,Finset.mul_sum,S.commutingPairing_gram]
  simp only [inner_sum, sum_inner, inner_smul_left,inner_smul_right,
    Complex.conj_ofReal,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def kernelScalar (r : ℝ) : ℝ := Real.exp (r/2)/(Real.exp r+1)

lemma kernelScalar_pos (r : ℝ) : 0 < kernelScalar r := by unfold kernelScalar; positivity
lemma kernelScalar_le (r : ℝ) : kernelScalar r ≤ 1/2 := by
  unfold kernelScalar
  rw [div_le_iff₀ (by positivity)]
  have he : Real.exp r = Real.exp (r/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he]
  nlinarith [sq_nonneg (Real.exp (r/2)-1)]

namespace StandardModularData

def kernelMatrix {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) : CStarMatrix n n S.M.toStarSubalgebra :=
  CStarMatrix.ofMatrix (fun i j => S.modularKernel (r i-r j) b)

@[simp] lemma kernelMatrix_apply {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b : S.M.commutant.toStarSubalgebra) (i j : n) :
    S.kernelMatrix r b i j = S.modularKernel (r i-r j) b := rfl

lemma kernelMatrix_add {n : Type uN} (S : StandardModularData H) (r : n → ℝ)
    (b c : S.M.commutant.toStarSubalgebra) :
    S.kernelMatrix r (b+c) = S.kernelMatrix r b+S.kernelMatrix r c := by
  apply CStarMatrix.ext
  intro i j
  exact S.modularKernel_add _ b c

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.KernelContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar kernel bounds, continuity, and spectral representations. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma continuous_kernelScalar : Continuous kernelScalar := by
  unfold kernelScalar
  fun_prop (disch := intros; positivity)

lemma kernelScalar_even (r : ℝ) : kernelScalar (-r) = kernelScalar r := by
  unfold kernelScalar
  have he := Real.exp_pos r
  have hh := Real.exp_pos (r/2)
  rw [show -r/2= -(r/2) by ring,Real.exp_neg,Real.exp_neg]
  have hs : Real.exp r = Real.exp (r/2)^2 := exp_eq_sq_exp_half r
  rw [hs]
  field_simp
  ring

lemma kernelScalar_le_exp_neg_abs (r : ℝ) :
    kernelScalar r ≤ Real.exp (-|r|/2) := by
  wlog hr : 0 ≤ r generalizing r
  · simpa only [kernelScalar_even,abs_neg] using this (-r) (by linarith)
  rw [abs_of_nonneg hr]
  unfold kernelScalar
  rw [div_le_iff₀ (by positivity)]
  have he : Real.exp (r/2) = Real.exp (-r/2)*Real.exp r := by rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [Real.exp_pos (-r/2)]

lemma hasDerivAt_kernelScalar (r : ℝ) :
    HasDerivAt kernelScalar
      (kernelScalar r * ((1-Real.exp r)/(2*(Real.exp r+1)))) r := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (x/2)) (Real.exp (r/2)/2) r := by
    convert ((hasDerivAt_id r).div_const 2).exp using 1 <;> simp; ring
  have ht := he.div ((Real.hasDerivAt_exp r).add_const 1) (by positivity : Real.exp r+1 ≠ 0)
  convert ht using 1 <;> try rfl
  unfold kernelScalar
  field_simp
  ring

lemma kernelScalar_deriv_bound (r : ℝ) :
    ‖kernelScalar r * ((1-Real.exp r)/(2*(Real.exp r+1)))‖ ≤ 1 := by
  rw [norm_mul,Real.norm_eq_abs, abs_of_pos (kernelScalar_pos r), Real.norm_eq_abs,
    abs_div,abs_of_pos (by positivity : 0 < 2*(Real.exp r+1))]
  have ha : |1-Real.exp r| ≤ Real.exp r+1 := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos r]
  have hb : |1-Real.exp r|/(2*(Real.exp r+1)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.exp_pos r]
  have hk := kernelScalar_le r
  have hp := kernelScalar_pos r
  nlinarith

lemma kernelScalar_lipschitz : LipschitzWith 1 kernelScalar := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun r => (hasDerivAt_kernelScalar r).differentiableAt)
  intro r
  rw [(hasDerivAt_kernelScalar r).deriv]
  exact_mod_cast kernelScalar_deriv_bound r

lemma integrable_exp_neg_abs_half : Integrable (fun r : ℝ => Real.exp (-|r|/2)) := by
  have hp : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0) 0).congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [abs_of_pos (show 0 < r from hr)]
    congr 1
    ring
  have hn : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Iio 0) := by
    have hp0 : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Ioi (-(0:ℝ))) := by
      simpa only [neg_zero] using hp
    have ht : IntegrableOn (fun r : ℝ => Real.exp (-|-r|/2)) (Iio (0:ℝ)) :=
      hp0.comp_neg_Iio (c := 0)
    simpa only [abs_neg] using ht
  have hp' : IntegrableOn (fun r : ℝ => Real.exp (-|r|/2)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hp
  have hu := hn.union hp'
  rw [Iio_union_Ici] at hu
  simpa only [integrableOn_univ] using hu

lemma integrable_kernelScalar : Integrable kernelScalar := by
  apply integrable_exp_neg_abs_half.mono' continuous_kernelScalar.aestronglyMeasurable
  exact ae_of_all _ fun r => by
    rw [Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r)]
    exact kernelScalar_le_exp_neg_abs r

def translatedKernel (r : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (kernelScalar (r-u):ℂ))
    (Complex.continuous_ofReal.comp (continuous_kernelScalar.comp (continuous_const.sub continuous_id)))
    (1/2) (by intro u; simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (kernelScalar_pos _)]
      using kernelScalar_le (r-u))

@[simp] lemma translatedKernel_apply (r u : ℝ) : translatedKernel r u = (kernelScalar (r-u):ℂ) := rfl

lemma norm_translatedKernel_le (r : ℝ) : ‖translatedKernel r‖ ≤ 1/2 := by
  apply BoundedContinuousFunction.norm_le (by norm_num) |>.mpr
  intro u
  simpa only [translatedKernel_apply,Complex.norm_real,Real.norm_eq_abs, abs_of_pos (kernelScalar_pos _)]
    using kernelScalar_le (r-u)

lemma continuous_translatedKernel : Continuous translatedKernel := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rw [dist_eq_norm]
  apply BoundedContinuousFunction.norm_le (by positivity) |>.mpr
  intro u
  change ‖(kernelScalar (r-u):ℂ)-(kernelScalar (s-u):ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub,Complex.norm_real, Real.norm_eq_abs]
  have ht := kernelScalar_lipschitz.dist_le_mul (r-u) (s-u)
  simpa [Real.dist_eq,sub_sub_sub_cancel_right] using ht

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma modularKernel_sum {ι : Type uι} (S : StandardModularData H) (r : ℝ)
    (s : Finset ι) (b : ι → S.M.commutant.toStarSubalgebra) :
    S.modularKernel r (∑ i ∈ s, b i) = ∑ i ∈ s, S.modularKernel r (b i) := by
  classical
  have hz : S.modularKernel r 0 = 0 := by simpa using S.modularKernel_smul r 0 0
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih => simp only [Finset.sum_insert hi, S.modularKernel_add, ih]

end StandardModularData

lemma modularResolvent_sub_norm_le (r s : ℝ) :
    ‖modularResolvent r-modularResolvent s‖ ≤
      |Real.exp r-Real.exp s|/(Real.exp r*Real.exp s) := by
  apply BoundedContinuousFunction.norm_le (by positivity) |>.mpr
  intro u
  change ‖(((Real.exp r+Real.exp u)⁻¹:ℝ):ℂ)-(((Real.exp s+Real.exp u)⁻¹:ℝ):ℂ)‖ ≤ _
  have heR : (Real.exp r+Real.exp u)⁻¹-(Real.exp s+Real.exp u)⁻¹ =
      (Real.exp s-Real.exp r)/((Real.exp r+Real.exp u)*(Real.exp s+Real.exp u)) := by
    field_simp
    ring
  have he := congrArg (fun x : ℝ => (x:ℂ)) heR
  simp only [Complex.ofReal_sub] at he
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_div,
    abs_of_pos (mul_pos (add_pos (Real.exp_pos r) (Real.exp_pos u))
      (add_pos (Real.exp_pos s) (Real.exp_pos u))),abs_sub_comm]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  nlinarith [Real.exp_pos r,Real.exp_pos s,Real.exp_pos u]

lemma continuous_modularResolvent : Continuous (fun r : ℝ => modularResolvent r) := by
  rw [continuous_iff_continuousAt]
  intro r
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun s => modularResolvent_sub_norm_le s r)
  have ht : Tendsto (fun s : ℝ => |Real.exp s-Real.exp r|/(Real.exp s*Real.exp r))
      (𝓝 r) (𝓝 (|Real.exp r-Real.exp r|/(Real.exp r*Real.exp r))) :=
    ((Real.continuous_exp.tendsto r).sub tendsto_const_nhds).abs.div
      ((Real.continuous_exp.tendsto r).mul tendsto_const_nhds)
      (ne_of_gt (mul_pos (Real.exp_pos r) (Real.exp_pos r)))
  simpa using ht

namespace StandardModularData
lemma continuous_modularKernel_xi (S : StandardModularData H)
    (b : S.M.commutant.toStarSubalgebra) :
    Continuous (fun r : ℝ => (S.modularKernel r b:H →L[ℂ] H) S.xi) := by
  have he : (fun r : ℝ => (S.modularKernel r b:H →L[ℂ] H) S.xi) =
      fun r => (Real.exp (r/2):ℂ) • S.D.calculus (modularResolvent r) ((b:H →L[ℂ] H) S.xi) := by
    funext r
    change (Real.exp (r/2):ℂ) • (S.modularLift r b:H →L[ℂ] H) S.xi = _
    rw [S.modularLift_xi]
  rw [he]
  apply Continuous.smul (by fun_prop)
  exact (S.D.calculusCLM.continuous.comp continuous_modularResolvent).clm_apply continuous_const

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace RealSpectralCalculus
lemma halfGraph_calculus (D : RealSpectralCalculus H) {x y : H}
    (hxy : (x,y) ∈ D.halfGraph) (f : BoundedContinuousFunction ℝ ℂ) :
    (D.calculus f x,D.calculus f y) ∈ D.halfGraph := by
  rw [D.halfGraph_iff_resolvent] at hxy ⊢
  rw [← map_add]
  change (D.calculus halfResolvent*D.calculus f) (x+y)=_
  rw [← map_mul,mul_comm,map_mul]
  change D.calculus f (D.calculus halfResolvent (x+y))=_
  rw [hxy]
end RealSpectralCalculus

end BoundedRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.StrongIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong operator integrals and positivity under Gaussian integration. -/

universe uE uX uY

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoundedRecovery
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma integrable_smul_bounded_orbit {k : ℝ → ℂ} (hk : Integrable k)
    {F : ℝ → E} (hF : Continuous F) {C : ℝ} (hbound : ∀ t, ‖F t‖ ≤ C) :
    Integrable (fun t => k t • F t) := by
  apply (hk.norm.mul_const C).mono'
    (hk.aestronglyMeasurable.smul hF.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖k t • F t‖ ≤ ‖k t‖ * C
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

omit [CompleteSpace E] in
lemma norm_integral_smul_bounded_orbit {k : ℝ → ℂ} (hk : Integrable k)
    {F : ℝ → E} {C : ℝ} (hbound : ∀ t, ‖F t‖ ≤ C) :
    ‖∫ t, k t • F t‖ ≤ (∫ t, ‖k t‖) * C := by
  calc
    _ ≤ ∫ t, ‖k t‖ * C := norm_integral_le_of_norm_le (hk.norm.mul_const C)
      (Filter.Eventually.of_forall (fun t => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)))
    _ = _ := integral_mul_const C _

def strongIntegral (k : ℝ → ℂ) (hk : Integrable k) (F : ℝ → E →L[ℂ] E)
    (hF : ∀ h, Continuous (fun t => F t h)) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C) :
    E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ t, k t • F t h
      map_add' := by
        intro h g
        simp only [map_add, smul_add]
        exact integral_add
          (integrable_smul_bounded_orbit hk (hF h)
            (fun t => (F t).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))))
          (integrable_smul_bounded_orbit hk (hF g)
            (fun t => (F t).le_opNorm g |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))))
      map_smul' := by
        intro c h
        simp only [map_smul, smul_comm (k _) c]
        exact integral_smul c _ }
    ((∫ t, ‖k t‖) * C) (by
      intro h
      calc
        _ ≤ (∫ t, ‖k t‖) * (C * ‖h‖) := norm_integral_smul_bounded_orbit hk
          (fun t => (F t).le_opNorm h |>.trans (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))
        _ = _ := (mul_assoc _ _ _).symm)

omit [CompleteSpace E] in
@[simp] lemma strongIntegral_apply (k : ℝ → ℂ) (hk : Integrable k) (F : ℝ → E →L[ℂ] E)
    (hF : ∀ h, Continuous (fun t => F t h)) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C) (h : E) :
    strongIntegral k hk F hF C hbound h = ∫ t, k t • F t h := rfl

end BoundedRecovery

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate NNReal

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

def gaussianCutoff (n : ℕ) (r : ℝ) : ℝ := Real.exp (-r^2/(4*((n:ℝ)+1)))

def gaussianVariance (n : ℕ) : ℝ≥0 := n+1

def gaussianNormalization (n : ℕ) : ℝ :=
  (gaussianPDFReal 0 (gaussianVariance n+gaussianVariance n) 0)⁻¹

lemma gaussianCutoff_pos (n : ℕ) (r : ℝ) : 0 < gaussianCutoff n r := Real.exp_pos _

lemma gaussianCutoff_le_one (n : ℕ) (r : ℝ) : gaussianCutoff n r ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma continuous_gaussianCutoff (n : ℕ) : Continuous (gaussianCutoff n) := by
  unfold gaussianCutoff
  fun_prop

lemma integrable_gaussianCutoff (n : ℕ) : Integrable (gaussianCutoff n) := by
  have ht := integrable_exp_neg_mul_sq (by positivity : 0 < (4*((n:ℝ)+1))⁻¹)
  convert ht using 1
  ext r
  unfold gaussianCutoff
  congr 1
  ring

lemma gaussianCutoff_tendsto (r : ℝ) : Tendsto (fun n => gaussianCutoff n r) atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ => 4*((n:ℝ)+1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have he := Real.continuous_exp.tendsto 0 |>.comp (tendsto_const_nhds.div_atTop hd :
    Tendsto (fun n : ℕ => -r^2/(4*((n:ℝ)+1))) atTop (𝓝 0))
  simpa only [gaussianCutoff,Real.exp_zero, Function.comp_def] using he

end BoundedRecovery

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.GaussianAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian operator averages and their positivity and adjoint identities. -/

universe u uM uN

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

lemma spectralCharacter_arg_add (t r s : ℝ) :
    spectralCharacter t (r+s) = spectralCharacter t r*spectralCharacter t s := by
  simp [mul_add,add_mul,Complex.exp_add]

def gaussianFourierWeight (n : ℕ) (t r : ℝ) : ℂ :=
  (gaussianCutoff n r:ℂ)*spectralCharacter t r

lemma integrable_gaussianFourierWeight (n : ℕ) (t : ℝ) :
    Integrable (gaussianFourierWeight n t) := by
  exact integrable_smul_bounded_orbit (integrable_gaussianCutoff n).ofReal
    (spectralCharacter t).continuous (C := 1) (by intro r; exact (spectralCharacter_norm t r).le)

lemma integrable_weight_translatedKernel (n : ℕ) (t : ℝ) :
    Integrable (fun r => gaussianFourierWeight n t r • translatedKernel r) :=
  integrable_smul_bounded_orbit (integrable_gaussianFourierWeight n t)
    continuous_translatedKernel norm_translatedKernel_le

def kernelMultiplier (n : ℕ) (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  ∫ r, gaussianFourierWeight n t r • translatedKernel r

lemma kernelMultiplier_apply (n : ℕ) (t u : ℝ) :
    kernelMultiplier n t u = ∫ r, gaussianFourierWeight n t r*(kernelScalar (r-u):ℂ) := by
  exact ((BoundedContinuousFunction.evalCLM ℂ u).integral_comp_comm
    (integrable_weight_translatedKernel n t)).symm

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier kernels and uniform bounds for Gaussian multipliers. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

def kernelMass : ℝ := ∫ r, kernelScalar r

def kernelFourier (t : ℝ) : ℂ := ∫ r, spectralCharacter t r*(kernelScalar r:ℂ)

lemma kernelMass_pos : 0 < kernelMass := by
  apply (integral_pos_iff_support_of_nonneg (fun r => (kernelScalar_pos r).le)
    integrable_kernelScalar).mpr
  have he : Function.support kernelScalar = univ := by
    ext r
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (kernelScalar_pos r).ne'
  rw [he]
  simp

lemma integrable_fourierKernel (t : ℝ) :
    Integrable (fun r => spectralCharacter t r*(kernelScalar r:ℂ)) := by
  apply integrable_kernelScalar.mono'
    ((spectralCharacter t).continuous.mul (Complex.continuous_ofReal.comp continuous_kernelScalar)).aestronglyMeasurable
  filter_upwards [] with r
  change ‖spectralCharacter t r*(kernelScalar r:ℂ)‖ ≤ kernelScalar r
  simp only [norm_mul,spectralCharacter_norm,one_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r),le_refl]

lemma kernelMultiplier_shift (n : ℕ) (t u : ℝ) :
    kernelMultiplier n t u = spectralCharacter t u*
      ∫ r, (gaussianCutoff n (r+u):ℂ)*spectralCharacter t r*(kernelScalar r:ℂ) := by
  rw [kernelMultiplier_apply,← integral_add_right_eq_self _ u,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [gaussianFourierWeight,spectralCharacter_arg_add,add_sub_cancel_right]
  ring

lemma integrable_cutoff_fourierKernel (n : ℕ) (t u : ℝ) :
    Integrable (fun r => (gaussianCutoff n (r+u):ℂ)*spectralCharacter t r*(kernelScalar r:ℂ)) := by
  have hc : Continuous (fun r => (gaussianCutoff n (r+u):ℂ)*spectralCharacter t r*(kernelScalar r:ℂ)) :=
    ((Complex.continuous_ofReal.comp ((continuous_gaussianCutoff n).comp
      (continuous_id.add continuous_const))).mul (spectralCharacter t).continuous).mul
      (Complex.continuous_ofReal.comp continuous_kernelScalar)
  apply integrable_kernelScalar.mono' hc.aestronglyMeasurable
  filter_upwards [] with r
  change ‖(gaussianCutoff n (r+u):ℂ)*spectralCharacter t r*(kernelScalar r:ℂ)‖ ≤ kernelScalar r
  simp only [norm_mul,spectralCharacter_norm,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r),abs_of_pos (gaussianCutoff_pos _ _)]
  exact mul_le_of_le_one_left (kernelScalar_pos r).le (gaussianCutoff_le_one _ _)

lemma norm_kernelMultiplier_le (n : ℕ) (t : ℝ) : ‖kernelMultiplier n t‖ ≤ kernelMass := by
  apply BoundedContinuousFunction.norm_le kernelMass_pos.le |>.mpr
  intro u
  rw [kernelMultiplier_shift,norm_mul,spectralCharacter_norm,one_mul]
  apply norm_integral_le_of_norm_le integrable_kernelScalar
  filter_upwards [] with r
  simp only [norm_mul,spectralCharacter_norm,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r),abs_of_pos (gaussianCutoff_pos _ _)]
  exact mul_le_of_le_one_left (kernelScalar_pos r).le (gaussianCutoff_le_one _ _)

end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma gaussianCutoff_antitone_abs (n : ℕ) {r s : ℝ} (hs : 0 ≤ s) (hr : |r| ≤ s) :
    gaussianCutoff n s ≤ gaussianCutoff n r := by
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq : r^2 ≤ s^2 := by nlinarith [sq_abs r,abs_nonneg r]
  linarith

def kernelCutoffError (n : ℕ) (R : ℝ) : ℝ :=
  ∫ r, (1-gaussianCutoff n (|r|+R))*kernelScalar r

lemma integrable_kernelCutoffError (n : ℕ) (R : ℝ) :
    Integrable (fun r => (1-gaussianCutoff n (|r|+R))*kernelScalar r) := by
  have hc : Continuous (fun r => (1-gaussianCutoff n (|r|+R))*kernelScalar r) :=
    (continuous_const.sub ((continuous_gaussianCutoff n).comp
      (continuous_abs.add continuous_const))).mul continuous_kernelScalar
  apply integrable_kernelScalar.mono' hc.aestronglyMeasurable
  filter_upwards [] with r
  change ‖(1-gaussianCutoff n (|r|+R))*kernelScalar r‖ ≤ kernelScalar r
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (sub_nonneg.mpr (gaussianCutoff_le_one _ _)) (kernelScalar_pos r).le)]
  exact mul_le_of_le_one_left (kernelScalar_pos r).le (by linarith [gaussianCutoff_pos n (|r|+R)])

lemma kernelCutoffError_nonneg (n : ℕ) (R : ℝ) : 0 ≤ kernelCutoffError n R := by
  apply integral_nonneg
  intro r
  exact mul_nonneg (sub_nonneg.mpr (gaussianCutoff_le_one _ _)) (kernelScalar_pos r).le

lemma kernelCutoffError_tendsto (R : ℝ) :
    Tendsto (fun n => kernelCutoffError n R) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ => (0:ℝ)) kernelScalar
    (fun n => (integrable_kernelCutoffError n R).aestronglyMeasurable)
    integrable_kernelScalar
    (fun n => ae_of_all _ fun r => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
        (sub_nonneg.mpr (gaussianCutoff_le_one _ _)) (kernelScalar_pos r).le)]
      exact mul_le_of_le_one_left (kernelScalar_pos r).le
        (by linarith [gaussianCutoff_pos n (|r|+R)]))
    (ae_of_all _ fun r => by
      have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub (gaussianCutoff_tendsto (|r|+R))).mul_const (kernelScalar r)
      simpa only [sub_self,zero_mul] using hh)
  simpa only [kernelCutoffError,integral_zero] using ht

lemma norm_kernelMultiplier_sub_le (n : ℕ) (t u R : ℝ) (hR : 0 ≤ R) (hu : |u| ≤ R) :
    ‖kernelMultiplier n t u-kernelFourier t*spectralCharacter t u‖ ≤ kernelCutoffError n R := by
  have he : kernelMultiplier n t u-kernelFourier t*spectralCharacter t u =
      spectralCharacter t u * ∫ r, ((gaussianCutoff n (r+u):ℂ)-1)*
        spectralCharacter t r*(kernelScalar r:ℂ) := by
    rw [kernelMultiplier_shift]
    simp_rw [sub_mul,one_mul]
    rw [integral_sub (integrable_cutoff_fourierKernel n t u) (integrable_fourierKernel t)]
    unfold kernelFourier
    ring
  rw [he,norm_mul,spectralCharacter_norm,one_mul]
  apply norm_integral_le_of_norm_le (integrable_kernelCutoffError n R)
  filter_upwards [] with r
  have hg : gaussianCutoff n (|r|+R) ≤ gaussianCutoff n (r+u) :=
    gaussianCutoff_antitone_abs n (add_nonneg (abs_nonneg r) hR)
      ((abs_add_le r u).trans (add_le_add le_rfl hu))
  have hn : ‖(gaussianCutoff n (r+u):ℂ)-1‖ = 1-gaussianCutoff n (r+u) := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (gaussianCutoff_le_one _ _))]
    ring
  rw [norm_mul,norm_mul,hn,spectralCharacter_norm,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (kernelScalar_pos r)]
  exact mul_le_mul_of_nonneg_right (by linarith) (kernelScalar_pos r).le

lemma kernelMultiplier_mul_tendsto (t : ℝ) (q : BoundedContinuousFunction ℝ ℂ)
    (hq : HasCompactSupport (q:ℝ → ℂ)) :
    Tendsto (fun n => kernelMultiplier n t*q) atTop
      (𝓝 ((kernelFourier t • spectralCharacter t)*q)) := by
  obtain ⟨R,hR,hRq⟩ := hq.isCompact.isBounded.exists_pos_norm_le
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    ((kernelCutoffError_tendsto R).mul_const ‖q‖ |>.trans (by simp))
  rw [← sub_mul]
  apply BoundedContinuousFunction.norm_le
    (mul_nonneg (kernelCutoffError_nonneg n R) (norm_nonneg q)) |>.mpr
  intro u
  change ‖(kernelMultiplier n t u-kernelFourier t*spectralCharacter t u)*q u‖ ≤ _
  by_cases hu : q u = 0
  · rw [hu,mul_zero,norm_zero]
    exact mul_nonneg (kernelCutoffError_nonneg n R) (norm_nonneg q)
  · rw [norm_mul]
    exact mul_le_mul (norm_kernelMultiplier_sub_le n t u R hR.le (hRq u (subset_closure hu)))
      (BoundedContinuousFunction.norm_coe_le_norm q u) (norm_nonneg _)
      (kernelCutoffError_nonneg n R)

end BoundedRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.StrongLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong spectral limits and orbit limits. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma tendsto_calculus_of_compact (D : RealSpectralCalculus H)
    (f : ℕ → BoundedContinuousFunction ℝ ℂ) (g : BoundedContinuousFunction ℝ ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ n, ‖f n‖ ≤ C)
    (he : ∀ q : BoundedContinuousFunction ℝ ℂ, HasCompactSupport (q : ℝ → ℂ) →
      Tendsto (fun n => f n*q) atTop (𝓝 (g*q))) (h : H) :
    Tendsto (fun n => D.calculus (f n) h) atTop (𝓝 (D.calculus g h)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨v,⟨q,hq,k,rfl⟩,hv⟩ := D.nondegenerate.exists_dist_lt h
    (show 0 < eps / (3*(C + ‖g‖ + 1)) by positivity)
  have hv' : ‖h-D.calculus q k‖ < eps / (3*(C+‖g‖+1)) := by
    simpa only [dist_eq_norm] using hv
  have hqconv : Tendsto (fun n => D.calculus (f n) (D.calculus q k)) atTop
      (𝓝 (D.calculus g (D.calculus q k))) := by
    have hc : Continuous (fun p : BoundedContinuousFunction ℝ ℂ => D.calculusCLM p k) :=
      D.calculusCLM.continuous.clm_apply continuous_const
    have ht := (hc.tendsto (g*q)).comp (he q hq)
    simpa only [Function.comp_def,calculusCLM_apply,map_mul,mul_apply_eq_comp] using ht
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hqconv (eps/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ < eps/3 := by
    simpa only [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have heq : D.calculus (f n) h-D.calculus g h =
      (D.calculus (f n) (h-D.calculus q k)-D.calculus g (h-D.calculus q k))+
      (D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)) := by
    simp only [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖D.calculus (f n) (h-D.calculus q k)-D.calculus g (h-D.calculus q k)‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := norm_add_le _ _
    _ ≤ C*‖h-D.calculus q k‖+‖g‖*‖h-D.calculus q k‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add
        ((D.norm_calculus_apply_le _ _).trans (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)))
        (D.norm_calculus_apply_le _ _))
    _ ≤ (C+‖g‖+1)*‖h-D.calculus q k‖+
        ‖D.calculus (f n) (D.calculus q k)-D.calculus g (D.calculus q k)‖ := by
      nlinarith [norm_nonneg (h-D.calculus q k)]
    _ < (C+‖g‖+1)*(eps/(3*(C+‖g‖+1)))+eps/3 :=
      add_lt_add (mul_lt_mul_of_pos_left hv' (by positivity)) hmid
    _ < eps := by
      field_simp
      nlinarith [norm_nonneg g]

lemma kernelMultiplier_strong_tendsto (D : RealSpectralCalculus H) (t : ℝ) (h : H) :
    Tendsto (fun n => D.calculus (kernelMultiplier n t) h) atTop
      (𝓝 (kernelFourier t • D.unitary t h)) := by
  have ht := D.tendsto_calculus_of_compact (fun n => kernelMultiplier n t)
    (kernelFourier t • spectralCharacter t) kernelMass_pos.le
    (fun n => norm_kernelMultiplier_le n t) (kernelMultiplier_mul_tendsto t) h
  simpa only [map_smul,smul_apply,unitary] using ht

end RealSpectralCalculus
end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.ModularCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial Tomita conjugation and modular covariance. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def jConjugate (S : StandardModularData H) (a : H →L[ℂ] H) : H →L[ℂ] H where
  toFun h := S.J (a (S.J h))
  map_add' _ _ := by simp only [map_add]
  map_smul' z h := by
    simp only [map_smulₛₗ,starRingEnd_self_apply,RingHom.id_apply]
  cont := S.J.continuous.comp (a.continuous.comp S.J.continuous)

@[simp] lemma jConjugate_apply (S : StandardModularData H) (a : H →L[ℂ] H) (h : H) :
    S.jConjugate a h = S.J (a (S.J h)) := rfl

@[simp] lemma jConjugate_involutive (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.jConjugate (S.jConjugate a) = a := by
  ext h
  simp only [S.jConjugate_apply]
  rw [S.conjugation h,S.conjugation (a h)]

@[simp] lemma sigma_zero (S : StandardModularData H) (a : H →L[ℂ] H) : S.sigma 0 a = a := by
  simp only [sigma,neg_zero,S.D.unitary_zero,one_mul,mul_one]

end StandardModularData
end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma sigma_add_time (S : StandardModularData H) (s t : ℝ) (a : H →L[ℂ] H) :
    S.sigma (s+t) a = S.sigma s (S.sigma t a) := by
  simp only [sigma,S.D.unitary_add,neg_add_rev,mul_assoc]

end StandardModularData
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.ErgodicAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space and predual ergodic averaging for the modular action. -/

universe u uE uF uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

@[simp] lemma sigma_one (S : StandardModularData H) (t : ℝ) :
    S.sigma t 1 = 1 := by simp [sigma]

lemma sigma_add (S : StandardModularData H) (t : ℝ) (a b : H →L[ℂ] H) :
    S.sigma t (a + b) = S.sigma t a + S.sigma t b := by simp [sigma, mul_add, add_mul]

lemma sigma_smul (S : StandardModularData H) (t : ℝ) (c : ℂ) (a : H →L[ℂ] H) :
    S.sigma t (c • a) = c • S.sigma t a := by simp [sigma]

lemma norm_sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    ‖S.sigma t a‖ = ‖a‖ := by
  have hle (r : ℝ) (b : H →L[ℂ] H) : ‖S.sigma r b‖ ≤ ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simp only [sigma, mul_apply_eq_comp, S.D.norm_unitary_apply]
    simpa only [S.D.norm_unitary_apply] using b.le_opNorm (S.D.unitary (-r) v)
  apply le_antisymm (hle t a)
  simpa only [← S.sigma_add_time, neg_add_cancel, S.sigma_zero] using hle (-t) (S.sigma t a)

lemma continuous_sigma_apply (S : StandardModularData H) (a : H →L[ℂ] H) (h : H) :
    Continuous (fun t => S.sigma t a h) := by
  exact S.D.continuous_unitary_apply_varying
    (a.continuous.comp ((S.D.continuous_unitary_apply h).comp continuous_neg))

end StandardModularData

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology

noncomputable section
open Set Filter
open scoped Topology

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open scoped ComplexConjugate

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def sigmaLinear (S : StandardModularData H) (t : ℝ) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := S.sigma t
  map_add' := S.sigma_add t
  map_smul' := S.sigma_smul t

@[simp] lemma sigmaLinear_apply (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigmaLinear t a = S.sigma t a := rfl

end StandardModularData
end BoundedRecovery

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed free-ultrafilter mean of symmetric Lebesgue averages and orbit defects. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

def orbitDefect (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h : H) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => ‖T (D.unitary t h)‖ ^ 2)
    ((T.continuous.comp (D.continuous_unitary_apply h)).norm.pow 2) (‖T‖ ^ 2 * ‖h‖ ^ 2) (by
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := T.le_opNorm (D.unitary t h)
      rw [D.norm_unitary_apply] at hb
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2)

@[simp] lemma orbitDefect_apply (D : RealSpectralCalculus H) (T : H →L[ℂ] H) (h : H) (t : ℝ) :
    D.orbitDefect T h t = ‖T (D.unitary t h)‖ ^ 2 := rfl

end RealSpectralCalculus
end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourierLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar truncation and Fourier localization with a width-independent L1 bound. -/

universe u

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace RealSpectralCalculus

lemma norm_unitary_le_one (D : RealSpectralCalculus H) (t : ℝ) : ‖D.unitary t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simp [D.norm_unitary_apply]

def integratedUnitary (D : RealSpectralCalculus H) (k : ℝ → ℂ) (hk : Integrable k) : H →L[ℂ] H :=
  strongIntegral k hk D.unitary D.continuous_unitary_apply 1 D.norm_unitary_le_one

end RealSpectralCalculus

namespace StandardModularData

def fourierFilter (S : StandardModularData H) (k : ℝ → ℂ) (hk : Integrable k)
    (a : H →L[ℂ] H) : H →L[ℂ] H :=
  strongIntegral k hk (fun t => S.sigma t a) (S.continuous_sigma_apply a) ‖a‖
    (fun t => (S.norm_sigma t a).le)

end StandardModularData
end BoundedRecovery

noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace BoundedRecovery

def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def bumpSchwartz : SchwartzMap ℝ ℂ :=
  ((bump0.hasCompactSupport.comp_homeomorph
      (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity))).comp_left
        (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (bump0.contDiff.comp (by
      change ContDiff ℝ _ (fun u : ℝ => 2 * Real.pi * u)
      fun_prop)))

@[simp] lemma bumpSchwartz_apply (u : ℝ) :
    bumpSchwartz u = (bump0 (2 * Real.pi * u) : ℂ) := rfl

def baseKernel : ℝ → ℂ := (𝓕 bumpSchwartz : SchwartzMap ℝ ℂ)

lemma baseKernel_integrable : Integrable baseKernel := (𝓕 bumpSchwartz).integrable

def bandKernel (s rho : ℝ) (t : ℝ) : ℂ :=
  (rho : ℂ) * Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) * baseKernel (rho*t)

lemma bandKernel_integrable {s rho : ℝ} (hrho : 0 < rho) : Integrable (bandKernel s rho) := by
  have hi := (integrable_comp_mul_left_iff baseKernel hrho.ne').mpr baseKernel_integrable
  have hc : Continuous (fun t : ℝ => Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hi' := (hi.bdd_mul hc.aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall (fun t => by simp [Complex.norm_exp]))).const_mul (rho : ℂ)
  change Integrable (fun t => (rho : ℂ) * Complex.exp (((-s*t : ℝ) : ℂ) * Complex.I) * baseKernel (rho*t))
  simpa only [mul_assoc] using hi'

end BoundedRecovery

noncomputable section
open Set MeasureTheory
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardModularData

def bandFilter (S : StandardModularData H) (s rho : ℝ) (hrho : 0 < rho)
    (a : H →L[ℂ] H) : H →L[ℂ] H :=
  S.fourierFilter (bandKernel s rho) (bandKernel_integrable hrho) a

end StandardModularData
end BoundedRecovery

end
end
end
end

end OAI
end


