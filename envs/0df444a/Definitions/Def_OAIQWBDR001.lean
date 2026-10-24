-- Prove2me | Definitions.Def_OAIQWBDR001
-- name    : OAIQWBDR001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T20:34:27.096894+00:00
-- url     : https://prove2.me/theorems/540b5a91-6625-4a97-90e1-8a9a90cff970
-- title:
--   OpenAI bounded modular recovery split: definitions bundle OAIQWBDR001
-- statement:
--   A definitions bundle of the split of OpenAI's proof of the bounded recovery theorem for modular spectral averages (`OAI.BoundedRecovery.bounded_recovery`, the paper's Theorem 4.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/ModularRecovery` (OpenAI, *Bounded recovery for modular spectral averages*, OpenAI Math Release, September 23, 2026, result family 290, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   This bundle holds the averaging and randomization devices: the vector state (`state`), the translation-invariant mean on bounded continuous functions (`meanCLM`, `translateBCF`), the random phase sums and their expectations used in the fourth-moment estimate (`phase`, `phaseSum`, `phaseExpectation`, `phaseMean`), and the explicit moment constant $26 + 16e^{s+1}$ of the recovery step (`recoveryMomentBound`).
--
--   The definitions of the published statement (`StandardModularData`, `RealSpectralCalculus`, `fixedMean`, `RecoveryConclusion` and the rest) are not repeated: the bundle imports them from the published bundle `Def_BoundedRecovery`. It imports no other bundle of this split.
--
--   Modules: `FourthMoments`, `Mean`, `Model`, `PositiveKernels`, `Recovery`, `StrongIntegrals`, `TomitaResolvent`.
--
--   The theorems of the development that the definitions do not need are proved in the single solution of this split, which imports the bundle `OAIQWBDR002` (and through it the other two) and proves `OAI.BoundedRecovery.bounded_recovery`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Bounded recovery for modular spectral averages, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 290; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-recovery-for-modular-spectral-averages-September-23-2026/Bounded-recovery-for-modular-spectral-averages-September-23-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/ModularRecovery at commit adc7f12

import Mathlib
import Definitions.Def_BoundedRecovery

section
-- module Solutions.OAIQW_BoundedRecovery.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nondegenerate spectral calculus, the closed Tomita graph, and bounded recovery. -/

universe u

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardModularData

def state (S : StandardModularData H) (a : H →L[ℂ] H) : ℂ :=
  inner ℂ S.xi (a S.xi)

end StandardModularData

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

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

def realMultiplier (g : BoundedContinuousFunction ℝ ℝ) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun u => (g u : ℂ))
    (Complex.continuous_ofReal.comp g.continuous) ‖g‖ (by
      intro u
      simpa only [Complex.norm_real] using g.norm_coe_le_norm u)

@[simp] lemma realMultiplier_apply (g : BoundedContinuousFunction ℝ ℝ) (u : ℝ) :
    realMultiplier g u = (g u : ℂ) := rfl

def regularizedQuotient (f : BoundedContinuousFunction ℝ ℂ)
    (g : BoundedContinuousFunction ℝ ℝ) (k : ℝ) (hk : 0 < k) :
    BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => f u * ((g u / ((g u)^2 + k) : ℝ) : ℂ))
    (f.continuous.mul (Complex.continuous_ofReal.comp
      (g.continuous.div ((g.continuous.pow 2).add continuous_const)
        (fun u => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)))))
    (‖f‖ * (‖g‖ / k)) (by
      intro u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) hk)]
      apply mul_le_mul (f.norm_coe_le_norm u) _ (by positivity) (norm_nonneg _)
      apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos (sq_nonneg _) hk) hk).mpr
      calc
        |g u| * k ≤ ‖g‖ * k := mul_le_mul_of_nonneg_right
          (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm u) hk.le
        _ ≤ ‖g‖ * ((g u)^2 + k) := mul_le_mul_of_nonneg_left
          (by nlinarith [sq_nonneg (g u)]) (norm_nonneg _))

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def centeredHalfResolvent : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (u/2)+1)⁻¹ - 1/2)
    (by
      apply Continuous.sub _ continuous_const
      apply Continuous.inv₀
      · fun_prop
      · intro u
        exact ne_of_gt (add_pos (Real.exp_pos _) zero_lt_one))
    2 (by
      intro u
      rw [Real.norm_eq_abs, abs_le]
      have hp : 0 < (Real.exp (u/2)+1)⁻¹ := inv_pos.mpr (by positivity)
      have hle : (Real.exp (u/2)+1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by have := Real.exp_pos (u/2); linarith)
      constructor <;> linarith)

@[simp] lemma centeredHalfResolvent_apply (u : ℝ) :
    centeredHalfResolvent u = (Real.exp (u/2)+1)⁻¹ - 1/2 := rfl

@[simp] lemma centeredHalfResolvent_zero : centeredHalfResolvent 0 = 0 := by
  norm_num [centeredHalfResolvent_apply]

end BoundedRecovery

end
end
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

section Lyapunov
variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma nonneg_of_jordan_pairing (φ : A →ₗ[ℂ] ℂ)
    (hp : ∀ a : A, 0 ≤ (φ (star a * a)).re)
    (hf : ∀ a : A, (φ (star a * a)).re = 0 → a = 0)
    (x : A) (hx : IsSelfAdjoint x)
    (ht : ∀ y : A, 0 ≤ y → 0 ≤ (φ (x*y+y*x)).re) : 0 ≤ x := by
  have hn : IsSelfAdjoint x⁻ := (CFC.negPart_nonneg x).isSelfAdjoint
  have h1 : x * x⁻ = -(x⁻ * x⁻) := by
    calc
      x * x⁻ = (x⁺-x⁻) * x⁻ := congrArg (fun y : A => y*x⁻) (CFC.posPart_sub_negPart x hx).symm
      _ = _ := by simp [sub_mul]
  have h2 : x⁻ * x = -(x⁻ * x⁻) := by
    calc
      x⁻ * x = x⁻ * (x⁺-x⁻) := congrArg (fun y : A => x⁻*y) (CFC.posPart_sub_negPart x hx).symm
      _ = _ := by simp [mul_sub]
  have hh := ht x⁻ (CFC.negPart_nonneg x)
  rw [h1,h2] at hh
  simp only [map_add,map_neg,Complex.add_re,Complex.neg_re] at hh
  have hc := hp x⁻
  rw [hn.star_eq] at hc
  have he : (φ (star x⁻ * x⁻)).re = 0 := by
    rw [hn.star_eq]
    linarith
  exact (CFC.negPart_eq_zero_iff x hx).mp (hf x⁻ he)

end Lyapunov

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_factor_eq (x y : H →L[ℂ] H) (h : x ≤ y) :
    y = x+star (CFC.sqrt (y-x))*CFC.sqrt (y-x) := by
  rw [(CFC.sqrt_nonneg (y-x)).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr h)]
  abel

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

section MatrixNorm
variable {A : Type uA} {m : Type uM} {n : Type uN} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype m] [Fintype n]
open CStarMatrix WithCStarModule
lemma cstarMatrix_norm_le_sum (M : CStarMatrix m n A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum, Finset.sum_mul]
  apply pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v j
end MatrixNorm

end BoundedRecovery

end
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

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery

lemma integral_comp_simple {X : Type uX} {Y : Type uY} {E : Type uE} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] (q : SimpleFunc X Y) (f : Y → E) :
    ∫ x, f (q x) ∂μ = ∑ y ∈ q.range, μ.real (q ⁻¹' {y}) • f y := by
  classical
  have he : (fun x => f (q x)) = fun x => ∑ y ∈ q.range,
      (q ⁻¹' {y}).indicator (fun _ => f y) x := by
    funext x
    rw [Finset.sum_eq_single (q x)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · intro hn
      exact (hn (q.mem_range_self x)).elim
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_indicator (q.measurableSet_preimage _),setIntegral_const]
  · intro y _
    exact (integrable_const _).indicator (q.measurableSet_preimage _)

lemma integral_positive_kernel {X : Type uX} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (x₀ : X) (μ : Measure X) [IsFiniteMeasure μ]
    (K : X → X → ℂ) (hcont : Continuous (fun p : X × X => K p.1 p.2))
    (C : ℝ) (hbound : ∀ x y, ‖K x y‖ ≤ C)
    (hpos : ∀ (n : Type uX) [Fintype n] (x : n → X) (c : n → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * K (x i) (x j)).re) :
    0 ≤ (∫ x, ∫ y, K x y ∂μ ∂μ).re := by
  classical
  let q (n : ℕ) : SimpleFunc X X := SimpleFunc.approxOn id measurable_id univ x₀ (mem_univ _) n
  have hq (x : X) : Tendsto (fun n => q n x) atTop (𝓝 x) := by
    exact SimpleFunc.tendsto_approxOn measurable_id (mem_univ x₀) (by simp)
  let F (n : ℕ) (p : X × X) : ℂ := K (q n p.1) (q n p.2)
  have hF (n : ℕ) : AEStronglyMeasurable (F n) (μ.prod μ) :=
    (hcont.measurable.comp ((q n).measurable.comp measurable_fst |>.prodMk
      ((q n).measurable.comp measurable_snd))).aestronglyMeasurable
  have ht : Tendsto (fun n => ∫ p, F n p ∂μ.prod μ) atTop
      (𝓝 (∫ p : X × X, K p.1 p.2 ∂μ.prod μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C) hF
      (integrable_const C)
    · exact fun n => ae_of_all _ (fun p => hbound _ _)
    · exact ae_of_all _ (fun p => hcont.continuousAt.tendsto.comp ((hq p.1).prodMk_nhds (hq p.2)))
  have hfi (n : ℕ) : Integrable (F n) (μ.prod μ) :=
    (integrable_const C).mono' (hF n) (ae_of_all _ (fun _ => hbound _ _))
  have hki : Integrable (fun p : X × X => K p.1 p.2) (μ.prod μ) :=
    (integrable_const C).mono' hcont.aestronglyMeasurable (ae_of_all _ (fun _ => hbound _ _))
  rw [integral_prod _ hki] at ht
  apply ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp ht)
  apply Eventually.of_forall
  intro n
  change 0 ≤ (∫ p, F n p ∂μ.prod μ).re
  rw [integral_prod _ (hfi n)]
  change 0 ≤ (∫ x, ∫ y, K (q n x) (q n y) ∂μ ∂μ).re
  simp_rw [integral_comp_simple μ (q n)]
  rw [integral_comp_simple μ (q n) (fun x => ∑ y ∈ (q n).range, μ.real (q n ⁻¹' {y}) • K x y)]
  have hp := hpos (q n).range (fun i => (i:X))
    (fun i => (μ.real (q n ⁻¹' {(i:X)}):ℂ))
  simp only [Complex.conj_ofReal] at hp
  rw [Finset.sum_coe_sort (q n).range (fun i : X =>
    ∑ j : (q n).range, (μ.real (q n ⁻¹' {i}):ℂ) *
      (μ.real (q n ⁻¹' {(j:X)}):ℂ) * K i j)] at hp
  have hs (i : X) : (∑ j : (q n).range, (μ.real (q n ⁻¹' {i}):ℂ) *
      (μ.real (q n ⁻¹' {(j:X)}):ℂ) * K i j) =
      ∑ j ∈ (q n).range, (μ.real (q n ⁻¹' {i}):ℂ) *
        (μ.real (q n ⁻¹' {j}):ℂ) * K i j :=
    Finset.sum_coe_sort (q n).range (fun j : X =>
      (μ.real (q n ⁻¹' {i}):ℂ) * (μ.real (q n ⁻¹' {j}):ℂ) * K i j)
  simp_rw [hs] at hp
  convert hp using 1
  simp only [Finset.smul_sum,Complex.real_smul,mul_assoc]

end BoundedRecovery

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

lemma gaussian_double_sub_integral {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (v : ℝ≥0) (f : ℝ → E)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C) :
    (∫ x, ∫ y, f (x-y) ∂gaussianReal 0 v ∂gaussianReal 0 v) =
      ∫ r, f r ∂gaussianReal 0 (v+v) := by
  have he (x : ℝ) : (∫ y, f (x-y) ∂gaussianReal 0 v) =
      ∫ y, f (x+y) ∂gaussianReal 0 v := by
    have ht := integral_map (μ := gaussianReal 0 v) (φ := fun y : ℝ => -y)
      (f := fun y => f (x+y)) (by fun_prop) (by fun_prop)
    simpa only [gaussianReal_map_neg,neg_zero,sub_eq_add_neg] using ht.symm
  simp_rw [he]
  rw [← integral_conv]
  · rw [gaussianReal_conv_gaussianReal,zero_add]
  · exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hC)

lemma gaussian_positive_definite (v : ℝ≥0) (f : ℝ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hpos : ∀ (n : Type) [Fintype n] (r : n → ℝ) (c : n → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * f (r i-r j)).re) :
    0 ≤ (∫ r, f r ∂gaussianReal 0 (v+v)).re := by
  rw [← gaussian_double_sub_integral v f hf C hC]
  exact integral_positive_kernel 0 (gaussianReal 0 v) (fun x y => f (x-y))
    (hf.comp (continuous_fst.sub continuous_snd)) C (fun _ _ => hC _) hpos

end BoundedRecovery

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

namespace BoundedRecovery

lemma norm_symmetricAverage_le (f : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ t, ‖f t‖ ≤ C) (k : ℕ) : ‖symmetricAverage f k‖ ≤ C := by
  by_cases hk : k = 0
  · simp [symmetricAverage, hk, hC]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(k : ℝ)) (b := (k : ℝ)) (fun t _ => hf t)
  have hab : |(k : ℝ) - -(k : ℝ)| = 2 * (k : ℝ) := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [hab] at hb
  rw [symmetricAverage, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  calc
    _ ≤ (2 * (k : ℝ))⁻¹ * (C * (2 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by field_simp

lemma tendsto_symmetricAverage_mean (omega : Ultrafilter ℕ)
    (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (symmetricAverage f) (omega : Filter ℕ) (𝓝 (fixedMean omega f)) := by
  obtain ⟨v,hv,ht⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (symmetricAverage f) omega)
    (show (Ultrafilter.map (symmetricAverage f) omega : Filter ℝ) ≤
      𝓟 (Icc (-‖f‖) ‖f‖) from by
      rw [Filter.le_principal_iff]
      change ∀ᶠ k : ℕ in (omega : Filter ℕ), symmetricAverage f k ∈ Icc (-‖f‖) ‖f‖
      exact Filter.Eventually.of_forall (fun k =>
        abs_le.mp (norm_symmetricAverage_le f (norm_nonneg _) f.norm_coe_le_norm k)))
  have h : Tendsto (symmetricAverage f) (omega : Filter ℕ) (𝓝 v) := ht
  simpa only [fixedMean, h.limUnder_eq] using h

lemma norm_fixedMean_le (omega : Ultrafilter ℕ) (f : BoundedContinuousFunction ℝ ℝ) :
    ‖fixedMean omega f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_symmetricAverage_mean omega f).norm
    (Filter.Eventually.of_forall (norm_symmetricAverage_le f (norm_nonneg _) f.norm_coe_le_norm))

lemma symmetricAverage_add (f g : BoundedContinuousFunction ℝ ℝ) (k : ℕ) :
    symmetricAverage (f+g) k = symmetricAverage f k + symmetricAverage g k := by
  simp only [symmetricAverage, Pi.add_apply,
    intervalIntegral.integral_add (f.continuous.intervalIntegrable _ _)
      (g.continuous.intervalIntegrable _ _), mul_add]

lemma symmetricAverage_smul (c : ℝ) (f : BoundedContinuousFunction ℝ ℝ) (k : ℕ) :
    symmetricAverage (c • f) k = c * symmetricAverage f k := by
  simp only [symmetricAverage, Pi.smul_apply, smul_eq_mul,
    intervalIntegral.integral_const_mul]
  ring

lemma fixedMean_add (omega : Ultrafilter ℕ) (f g : BoundedContinuousFunction ℝ ℝ) :
    fixedMean omega (f+g) = fixedMean omega f + fixedMean omega g := by
  apply tendsto_nhds_unique (tendsto_symmetricAverage_mean omega (f+g))
  change Tendsto (fun k => symmetricAverage (f+g) k) _ _
  simp_rw [symmetricAverage_add]
  exact
    (tendsto_symmetricAverage_mean omega f).add (tendsto_symmetricAverage_mean omega g)

lemma fixedMean_smul (omega : Ultrafilter ℕ) (c : ℝ) (f : BoundedContinuousFunction ℝ ℝ) :
    fixedMean omega (c • f) = c * fixedMean omega f := by
  apply tendsto_nhds_unique (tendsto_symmetricAverage_mean omega (c • f))
  change Tendsto (fun k => symmetricAverage (c • f) k) _ _
  simp_rw [symmetricAverage_smul]
  exact (tendsto_symmetricAverage_mean omega f).const_mul c

def meanCLM (omega : Ultrafilter ℕ) : (BoundedContinuousFunction ℝ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => fixedMean omega f
      map_add' := fixedMean_add omega
      map_smul' := fixedMean_smul omega }
    1 (by intro f; simpa using norm_fixedMean_le omega f)

@[simp] lemma meanCLM_apply (omega : Ultrafilter ℕ) (f : BoundedContinuousFunction ℝ ℝ) :
    meanCLM omega f = fixedMean omega f := rfl

def translateBCF (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) :
    BoundedContinuousFunction ℝ ℝ := f.compContinuous ⟨fun t => t+r, by fun_prop⟩

@[simp] lemma translateBCF_apply (f : BoundedContinuousFunction ℝ ℝ) (r t : ℝ) :
    translateBCF f r t = f (t+r) := rfl

end BoundedRecovery

end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.FourthMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact noncommutative fourth-moment pairings and overlap subtraction. -/

universe u uA uB uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set Filter
open scoped Topology

noncomputable section

namespace BoundedRecovery

section AlgebraicPhases

variable {A : Type uA} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def phase (i : Fin 4) : ℂ := ![1, -1, Complex.I, -Complex.I] i

def phaseAverage (f : Fin 4 → A) : A := (1 / 4 : ℂ) • ∑ i, f i

end AlgebraicPhases

section PhaseExpectation
variable {A : Type uA} [AddCommMonoid A] [Module ℂ A]

def phaseExpectation : (n : ℕ) → ((Fin n → Fin 4) → A) → A
  | 0, f => f Fin.elim0
  | n + 1, f => phaseExpectation n (fun e =>
      (1 / 4 : ℂ) • ∑ i : Fin 4, f (Fin.cons i e))

end PhaseExpectation

section RingExpectation
variable {A : Type uA} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def phaseSum {n : ℕ} (a : Fin n → A) (e : Fin n → Fin 4) : A :=
  ∑ i, phase (e i) • a i

end RingExpectation

def phaseMean : (n : ℕ) → ((Fin n → Fin 4) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n + 1, f => phaseMean n (fun e => (1 / 4 : ℝ) * ∑ i : Fin 4, f (Fin.cons i e))

end BoundedRecovery

end
end

end OAI
end

section
-- module Solutions.OAIQW_BoundedRecovery.Recovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded recovery on exact factor-four spectral bands. -/

universe u uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Set

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def recoveryMomentBound (s : ℝ) : ℝ := 26 + 16 * Real.exp (s+1)

end BoundedRecovery

end
end

end OAI
end


