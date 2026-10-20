-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_FourierKernels
-- name    : OAI_Analysis_ModularRecovery_FourierKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:36:30.102608+00:00
-- url     : https://prove2.me/theorems/282dcd56-f5e6-40ad-b693-bbea7c4b8857
-- title:
--   Fourier transform of the modular kernel scalar
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Kernel mass.** $\int\kappa(r)\,dr>0$, where $\kappa(r)=1/(2\cosh(r/2))$.
--   2. **Kernel Fourier transform.** The function
--   $$
--   \hat\kappa(t)=\int e^{itr}\kappa(r)\,dr .
--   $$
--   3. **Cutoff error.** $\int\bigl(1-g_n(|r|+R)\bigr)\kappa(r)\,dr$, which tends to $0$ as $n\to\infty$.
--
--   These give uniform bounds for the Gaussian kernel multipliers, and convergence of the kernel averages to $\hat\kappa(t)$ times the modular unitary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/FourierKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/FourierKernels.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BoundedRecovery mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_OAI_Analysis_ModularRecovery_Model
import Definitions.Def_OAI_Analysis_ModularRecovery_SpectralCalculus
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaResolvent
import Definitions.Def_OAI_Analysis_ModularRecovery_PolarCutoff
import Definitions.Def_OAI_Analysis_ModularRecovery_TomitaFundamental
import Definitions.Def_OAI_Analysis_ModularRecovery_RealGraph
import Definitions.Def_OAI_Analysis_ModularRecovery_Commutant
import Definitions.Def_OAI_Analysis_ModularRecovery_PositiveKernels
import Definitions.Def_OAI_Analysis_ModularRecovery_KernelContinuity
import Definitions.Def_OAI_Analysis_ModularRecovery_StrongIntegrals
import Definitions.Def_OAI_Analysis_ModularRecovery_GaussianAverages

-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

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
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma kernelAverage_nonneg (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) : 0 ≤ S.kernelAverage n t b := by
  change 0 ≤ (S.kernelAverage n t b:H →L[ℂ] H)
  rw [ContinuousLinearMap.nonneg_iff_isPositive,ContinuousLinearMap.isPositive_def']
  refine ⟨?_,fun h => ?_⟩
  · show star (S.kernelAverage n t b:H →L[ℂ] H) = _
    rw [← StarMemClass.coe_star,S.kernelAverage_star,hb.isSelfAdjoint.star_eq]
  · obtain ⟨d,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    have hp := S.kernelAverage_gram_vector_nonneg n t (fun _ : Unit => d) (fun _ => h)
    change 0 ≤ (inner ℂ ((S.kernelAverage n t (star d*d):H →L[ℂ] H) h) h).re
    rw [← inner_conj_symm,Complex.conj_re]
    simpa only [Fintype.sum_unique] using hp

lemma kernelAverage_mono (S : StandardModularData H) (n : ℕ) (t : ℝ)
    {b c : S.M.commutant.toStarSubalgebra} (hbc : b ≤ c) :
    S.kernelAverage n t b ≤ S.kernelAverage n t c := by
  have he : S.kernelAverage n t (c-b)+S.kernelAverage n t b = S.kernelAverage n t c := by
    rw [← S.kernelAverage_add,sub_add_cancel]
  exact he ▸ le_add_of_nonneg_left (S.kernelAverage_nonneg n t _ (sub_nonneg.mpr hbc))

lemma kernelAverage_one (S : StandardModularData H) (n : ℕ) (t : ℝ) :
    S.kernelAverage n t 1 = (kernelMultiplier n t 0) • 1 := by
  apply Subtype.ext
  ext h
  rw [S.kernelAverage_apply]
  simp_rw [S.modularKernel_one']
  change (∫ r, gaussianFourierWeight n t r • ((kernelScalar r:ℂ) • h)) = _
  simp_rw [smul_smul]
  rw [integral_smul_const]
  congr 1
  simp only [kernelMultiplier_apply,sub_zero]

lemma norm_kernelAverage_one_le (S : StandardModularData H) (n : ℕ) (t : ℝ) :
    ‖S.kernelAverage n t 1‖ ≤ kernelMass := by
  rw [S.kernelAverage_one,norm_smul]
  apply (mul_le_mul_of_nonneg_right
    (BoundedContinuousFunction.norm_coe_le_norm (kernelMultiplier n t) 0) (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_right (norm_kernelMultiplier_le n t) (norm_nonneg _)).trans
  exact mul_le_of_le_one_right kernelMass_pos.le ContinuousLinearMap.norm_id_le

lemma norm_kernelAverage_of_nonneg (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) (hb : 0 ≤ b) :
    ‖S.kernelAverage n t b‖ ≤ kernelMass*‖b‖ := by
  have heq : algebraMap ℝ S.M.commutant.toStarSubalgebra ‖b‖ =
      (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    apply Subtype.ext
    ext h
    simp [Algebra.algebraMap_eq_smul_one]
  have hle : b ≤ (‖b‖:ℂ) • (1:S.M.commutant.toStarSubalgebra) := by
    rw [← heq]
    exact hb.isSelfAdjoint.le_algebraMap_norm_self
  apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg (S.kernelAverage_mono n t hle)
    (S.kernelAverage_nonneg n t b hb)).trans
  rw [S.kernelAverage_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  nlinarith [S.norm_kernelAverage_one_le n t,norm_nonneg b]

lemma kernelAverage_sum {ι : Type uι} (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (s : Finset ι) (b : ι → S.M.commutant.toStarSubalgebra) :
    S.kernelAverage n t (∑ i ∈ s, b i) = ∑ i ∈ s, S.kernelAverage n t (b i) := by
  classical
  have hz : S.kernelAverage n t 0 = 0 := by simpa using S.kernelAverage_smul n t 0 0
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih => simp only [Finset.sum_insert hi, S.kernelAverage_add, ih]

lemma norm_kernelAverage_le (S : StandardModularData H) (n : ℕ) (t : ℝ)
    (b : S.M.commutant.toStarSubalgebra) : ‖S.kernelAverage n t b‖ ≤ 4*kernelMass*‖b‖ := by
  obtain ⟨x,hx,hxn,he⟩ := CStarAlgebra.exists_sum_four_nonneg b
  nth_rw 1 [he]
  rw [S.kernelAverage_sum]
  calc
    ‖∑ i : Fin 4, S.kernelAverage n t (Complex.I ^ (i:ℕ) • x i)‖ ≤
        ∑ i : Fin 4, kernelMass*‖b‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [S.kernelAverage_smul,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
      exact (S.norm_kernelAverage_of_nonneg n t (x i) (hx i)).trans
        (mul_le_mul_of_nonneg_left (hxn i) kernelMass_pos.le)
    _ = 4*kernelMass*‖b‖ := by simp; ring

end StandardModularData
end BoundedRecovery

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


