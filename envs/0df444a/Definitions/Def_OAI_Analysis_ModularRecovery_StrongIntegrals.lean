-- Prove2me | Definitions.Def_OAI_Analysis_ModularRecovery_StrongIntegrals
-- name    : OAI_Analysis_ModularRecovery_StrongIntegrals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:31:12.430867+00:00
-- url     : https://prove2.me/theorems/eb34b3ee-b9cc-4ec7-ac94-a5687e32bf88
-- title:
--   Strong operator integrals and Gaussian cutoffs
-- statement:
--   These notions belong to a formal proof of a bounded recovery theorem in Tomita–Takesaki theory. Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\xi$, and let $\varphi(a)=\langle\xi,a\xi\rangle$. The modular data are encoded by a nondegenerate $*$-homomorphism $f\mapsto f(D)$ from bounded continuous functions on $\mathbb R$ to bounded operators, thought of as the functional calculus of $D=\log\Delta$. It comes with the unitary group $\Delta^{it}=e^{itD}$, the modular automorphisms $\sigma_t(a)=\Delta^{it}a\Delta^{-it}$, and an antiunitary involution $J$. The Tomita relation requires the closure of $\{(a\xi,a^*\xi):a\in M\}$ to be the graph of $J\Delta^{1/2}$. The theorem says that when $\varphi$ has trivial centralizer, a vector in a narrow spectral band of $D$ on which an operator $T$ is not small can be replaced by $v\xi$, with $v\in M$ uniformly bounded and $v\xi$ in a comparable band.
--
--   1. **Strong integral.** For an integrable scalar function $k$ and a strongly continuous, uniformly bounded family $F(t)$ of operators, the operator
--   $$
--   h\mapsto\int k(t)\,F(t)h\,dt,
--   $$
--   of norm at most $\|k\|_1\sup_t\|F(t)\|$.
--   2. **Gaussian cutoffs.** $g_n(r)=\exp\bigl(-r^2/(4(n+1))\bigr)$, with variance parameter $n+1$ and its normalization constant. These are positive definite functions increasing to $1$, so integrating a positive definite operator-valued kernel against them preserves positivity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ModularRecovery/StrongIntegrals.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ModularRecovery/StrongIntegrals.lean by skeleton subtraction
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

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ComplexConjugate NNReal
namespace BoundedRecovery

def gaussianCutoff (n : ℕ) (r : ℝ) : ℝ := Real.exp (-r^2/(4*((n:ℝ)+1)))

def gaussianVariance (n : ℕ) : ℝ≥0 := n+1

def gaussianNormalization (n : ℕ) : ℝ :=
  (gaussianPDFReal 0 (gaussianVariance n+gaussianVariance n) 0)⁻¹

lemma gaussianVariance_pos (n : ℕ) : 0 < gaussianVariance n := by
  unfold gaussianVariance
  positivity

lemma gaussianNormalization_pos (n : ℕ) : 0 < gaussianNormalization n := by
  apply inv_pos.mpr
  exact gaussianPDFReal_pos _ _ _ (ne_of_gt (add_pos (gaussianVariance_pos n) (gaussianVariance_pos n)))

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

lemma gaussianNormalization_pdf (n : ℕ) (r : ℝ) :
    gaussianNormalization n * gaussianPDFReal 0 (gaussianVariance n+gaussianVariance n) r =
      gaussianCutoff n r := by
  unfold gaussianNormalization gaussianPDFReal
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one]
  rw [inv_inv,mul_inv_cancel_left₀]
  · unfold gaussianCutoff
    congr 1
    simp only [gaussianVariance,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    congr 1
    ring
  · apply Real.sqrt_ne_zero'.mpr
    have hv : (0:ℝ) < (gaussianVariance n+gaussianVariance n:ℝ≥0) :=
      by exact_mod_cast add_pos (gaussianVariance_pos n) (gaussianVariance_pos n)
    positivity

lemma integral_gaussianCutoff_eq {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → E) :
    (∫ r, gaussianCutoff n r • f r) = gaussianNormalization n •
      ∫ r, f r ∂gaussianReal 0 (gaussianVariance n+gaussianVariance n) := by
  rw [integral_gaussianReal_eq_integral_smul
    (ne_of_gt (add_pos (gaussianVariance_pos n) (gaussianVariance_pos n))), ← integral_smul]
  simp_rw [smul_smul,gaussianNormalization_pdf]

lemma gaussianCutoff_positive_definite (n : ℕ) (f : ℝ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ r, ‖f r‖ ≤ C)
    (hpos : ∀ (ι : Type) [Fintype ι] (r : ι → ℝ) (c : ι → ℂ),
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * f (r i-r j)).re) :
    0 ≤ (∫ r, (gaussianCutoff n r:ℂ)*f r).re := by
  change 0 ≤ (∫ r, gaussianCutoff n r • f r).re
  rw [integral_gaussianCutoff_eq]
  rw [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (gaussianNormalization_pos n).le
    (gaussian_positive_definite (gaussianVariance n) f hf C hC hpos)

end BoundedRecovery

end
end
end
end

end OAI


