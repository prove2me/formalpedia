-- Prove2me | Definitions.Def_Mathlib_MeasureTheory_Function_L2KernelOperator
-- name    : Mathlib_MeasureTheory_Function_L2KernelOperator
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/16c27d41-2acb-5a7a-8039-fd10058bb5f8
-- title:
--   L² kernel integral operators: Schur bound and compactness
-- statement:
--   For measurable spaces $\alpha,\beta$ with measures $\mu,\nu$, `kernelIntegral ν K f x` is defined as $\int_\beta K(x,y)f(y)\,d\nu(y)$ for a kernel $K\colon\alpha\times\beta\to\mathbb{C}$ and $f\colon\beta\to\mathbb{C}$. The first group of results establishes the Cauchy–Schwarz (Schur-type) bound for $\sigma$-finite $\nu$: for a.e.-strongly measurable $K$ (for $\mu\times\nu$) and $f$, the $\mathbb{R}_{\ge0}^\infty$-valued integral $\int\|\mathrm{kernelIntegral}\|_e^2\,d\mu$ is at most $\bigl(\int\|K\|_e^2\,d(\mu\times\nu)\bigr)\bigl(\int\|f\|_e^2\,d\nu\bigr)$, equivalently $\mathrm{eLpNorm}$ at exponent $2$ is submultiplicative; consequently $K\in L^2(\mu\times\nu)$ and $f\in L^2(\nu)$ give $\mathrm{kernelIntegral}\in L^2(\mu)$, almost every slice $y\mapsto K(x,y)$ lies in $L^2(\nu)$, and almost every $y\mapsto K(x,y)f(y)$ is integrable.
--
--   For finite $\mu$ and $\nu$, `kernelIntegralLM` assigns to $K\in L^2(\mu\times\nu)$ the linear map $L^2(\nu)\to L^2(\mu)$, $f\mapsto T_Kf$, with $\|T_Kf\|\le\|K\|\,\|f\|$; `kernelIntegralₗ` packages $K\mapsto T_K$ as a continuous bilinear map of norm at most $1$, and `kernelIntegralCLM K` is $T_K$ as a continuous linear map, with $\|T_K\|\le\|K\|$. For $K=c\cdot\mathbf 1_{A\times B}$ one has $T_Kf=\bigl(c\int_B f\,d\nu\bigr)\mathbf 1_A$, a rank-one, hence compact, operator. The submodule `compactKernels μ ν` of those $K$ with $T_K$ compact is closed, being the preimage of the closed set of compact operators under $K\mapsto T_K$; since measurable rectangles form a set semiring generating the product $\sigma$-algebra, indicators of finite disjoint unions of rectangles lie in it, and approximation in measure of symmetric differences together with density of simple functions in $L^2$ yields `compactKernels μ ν = ⊤`. Thus $T_K$ is compact for every $K\in L^2(\mu\times\nu)$; in particular, if $T_K$ equals the identity of $L^2(\nu)$ for some $K\in L^2(\nu\times\nu)$, then $L^2(\nu)$ is finite-dimensional.
--
--   **Relation to Mathlib.** Mathlib supplies the $L^p$ spaces, `indicatorConstLp`, and the compact-operator API used here (`IsCompactOperator`, closedness of the set of compact operators, and finite-dimensionality from a compact identity); the kernel integral operator on $L^2$ and its compactness are developed in this module.
--
--   **Where it is used.** The construction provides the analytic input that integral operators with $L^2$ kernels on a finite measure space are compact, as needed for trace-formula style arguments on the automorphic side of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_MeasureTheory_Function_L2KernelOperator.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ENNReal NNReal symmDiff
open MeasureTheory Set

noncomputable section

namespace MeasureTheory

namespace L2

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

def kernelIntegral (ν : Measure β) (K : α × β → ℂ) (f : β → ℂ) (x : α) : ℂ :=
  ∫ y, K (x, y) * f y ∂ν

omit [MeasurableSpace α] in
lemma kernelIntegral_def (K : α × β → ℂ) (f : β → ℂ) (x : α) :
    kernelIntegral ν K f x = ∫ y, K (x, y) * f y ∂ν := rfl

section SchurBound

variable [SFinite ν]

theorem lintegral_enorm_kernelIntegral_sq_le {K : α × β → ℂ} {f : β → ℂ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : AEStronglyMeasurable f ν) :
    ∫⁻ x, ‖kernelIntegral ν K f x‖ₑ ^ (2 : ℝ) ∂μ ≤
      (∫⁻ z, ‖K z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by

  have hslice : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K (x, y)) ν :=
    hK.prodMk_left
  have key : ∀ᵐ x ∂μ, ‖kernelIntegral ν K f x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by
    filter_upwards [hslice] with x hx
    have h1 : ‖kernelIntegral ν K f x‖ₑ ≤ ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂ν := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      exact lintegral_congr fun y => by rw [enorm_mul]
    have h2 : ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂ν ≤
        (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
          (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
        hx.enorm hf.enorm
    calc ‖kernelIntegral ν K f x‖ₑ ^ (2 : ℝ)
        ≤ ((∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
            (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
      _ = (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          norm_num

  calc ∫⁻ x, ‖kernelIntegral ν K f x‖ₑ ^ (2 : ℝ) ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν ∂μ :=
        lintegral_mono_ae key
    _ = (∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν :=
        lintegral_mul_const'' _ (hK.enorm.pow_const _).lintegral_prod_right'
    _ = (∫⁻ z, ‖K z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by
        rw [lintegral_prod _ (hK.enorm.pow_const _)]

theorem eLpNorm_kernelIntegral_le {K : α × β → ℂ} {f : β → ℂ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : AEStronglyMeasurable f ν) :
    eLpNorm (kernelIntegral ν K f) 2 μ ≤ eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_kernelIntegral_sq_le hK hf) (by norm_num)

theorem _root_.MeasureTheory.MemLp.kernelIntegral {K : α × β → ℂ} {f : β → ℂ}
    (hK : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    MemLp (kernelIntegral ν K f) 2 μ := by
  refine ⟨?_, ?_⟩
  · exact (hK.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd)).integral_prod_right'
  · exact (eLpNorm_kernelIntegral_le hK.aestronglyMeasurable hf.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top hK.eLpNorm_lt_top hf.eLpNorm_lt_top)

theorem _root_.MeasureTheory.MemLp.ae_memLp_prodMk_left {K : α × β → ℂ}
    (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 ν := by
  have hmeas := hK.aestronglyMeasurable.prodMk_left
  have hfin : ∀ᵐ x ∂μ, ∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν < ∞ := by
    have h2 := hK.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h2
    have hfin' : ∫⁻ z, ‖K z‖ₑ ^ ((2 : ℝ≥0∞)).toReal ∂(μ.prod ν) ≠ ∞ := by
      intro hcon
      rw [hcon] at h2
      simp at h2
    rw [show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num] at hfin'
    rw [lintegral_prod _ (hK.aestronglyMeasurable.enorm.pow_const _)] at hfin'
    exact ae_lt_top' (hK.aestronglyMeasurable.enorm.pow_const _).lintegral_prod_right' hfin'
  filter_upwards [hmeas, hfin] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (by rw [show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num]; exact hx2.ne)

theorem ae_integrable_kernelIntegral {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    {f : β → ℂ} (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) ν := by
  filter_upwards [hK.ae_memLp_prodMk_left] with x hx
  exact hx.integrable_mul hf

end SchurBound

section Operator

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def kernelIntegralLM (K : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ((Lp.memLp K).kernelIntegral (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [ae_integrable_kernelIntegral (Lp.memLp K) (Lp.memLp f),
      ae_integrable_kernelIntegral (Lp.memLp K) (Lp.memLp g)] with x hxf hxg
    simp only [Pi.add_apply, kernelIntegral_def]
    rw [← integral_add hxf hxg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    refine .of_forall fun x => ?_
    simp only [Pi.smul_apply, kernelIntegral_def, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]; ring

omit [IsFiniteMeasure μ] in
@[simp]
lemma kernelIntegralLM_apply (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    kernelIntegralLM K f = ((Lp.memLp K).kernelIntegral (Lp.memLp f)).toLp _ := rfl

omit [IsFiniteMeasure μ] in
lemma kernelIntegralLM_coeFn (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    kernelIntegralLM K f =ᵐ[μ] kernelIntegral ν (K : α × β → ℂ) f :=
  MemLp.coeFn_toLp ((Lp.memLp K).kernelIntegral (Lp.memLp f))

omit [IsFiniteMeasure μ] in

theorem norm_kernelIntegralLM_apply_le (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    ‖kernelIntegralLM K f‖ ≤ ‖K‖ * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top K)
    (Lp.eLpNorm_ne_top f)) ?_
  rw [eLpNorm_congr_ae (kernelIntegralLM_coeFn K f)]
  exact eLpNorm_kernelIntegral_le (Lp.aestronglyMeasurable K) (Lp.aestronglyMeasurable f)

omit [IsFiniteMeasure μ] in

theorem kernelIntegralLM_add_apply (K K' : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    kernelIntegralLM (K + K') f = kernelIntegralLM K f + kernelIntegralLM K' f := by
  simp only [kernelIntegralLM_apply]
  rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
  filter_upwards [ae_integrable_kernelIntegral (Lp.memLp K) (Lp.memLp f),
    ae_integrable_kernelIntegral (Lp.memLp K') (Lp.memLp f),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add K K')] with x hxK hxK' hxadd
  simp only [Pi.add_apply, kernelIntegral_def]
  rw [← integral_add hxK hxK']
  refine integral_congr_ae ?_
  filter_upwards [hxadd] with y hy
  rw [hy, Pi.add_apply, add_mul]

omit [IsFiniteMeasure μ] in

theorem kernelIntegralLM_smul_apply (c : ℂ) (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    kernelIntegralLM (c • K) f = c • kernelIntegralLM K f := by
  simp only [kernelIntegralLM_apply]
  rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
  filter_upwards [Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c K)] with x hxsmul
  simp only [Pi.smul_apply, kernelIntegral_def, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hxsmul] with y hy
  rw [hy, Pi.smul_apply, smul_eq_mul]; ring

def kernelIntegralₗ : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous₂
    { toFun := kernelIntegralLM
      map_add' := fun K K' => LinearMap.ext fun f => kernelIntegralLM_add_apply K K' f
      map_smul' := fun c K => LinearMap.ext fun f => kernelIntegralLM_smul_apply c K f }
    1 (fun K f => by simpa using norm_kernelIntegralLM_apply_le K f)

abbrev kernelIntegralCLM (K : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  kernelIntegralₗ K

omit [IsFiniteMeasure μ] in
lemma kernelIntegralCLM_apply (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    kernelIntegralCLM K f = kernelIntegralLM K f := rfl

omit [IsFiniteMeasure μ] in
lemma kernelIntegralCLM_coeFn (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    kernelIntegralCLM K f =ᵐ[μ] fun x => ∫ y, (K : α × β → ℂ) (x, y) * f y ∂ν :=
  kernelIntegralLM_coeFn K f

omit [IsFiniteMeasure μ] in

theorem norm_kernelIntegralCLM_le (K : Lp ℂ 2 (μ.prod ν)) : ‖kernelIntegralCLM K‖ ≤ ‖K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K) fun f =>
    norm_kernelIntegralLM_apply_le K f

omit [IsFiniteMeasure μ] in

theorem norm_kernelIntegralₗ_le :
    ‖(kernelIntegralₗ : Lp ℂ 2 (μ.prod ν) →L[ℂ] _)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end Operator

section RankOne

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem kernelIntegralCLM_indicatorConst_prod {A : Set α} {B : Set β} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (c : ℂ) (f : Lp ℂ 2 ν) :
    kernelIntegralCLM (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c) f =
      (c * ∫ y in B, f y ∂ν) • indicatorConstLp 2 hA (measure_ne_top μ _) (1 : ℂ) := by
  refine Lp.ext ?_
  refine (kernelIntegralCLM_coeFn _ f).trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
  have hcoe := Measure.ae_ae_of_ae_prod
    (indicatorConstLp_coeFn (p := 2) (hs := hA.prod hB) (hμs := measure_ne_top (μ.prod ν) _) (c := c))
  filter_upwards [hcoe, indicatorConstLp_coeFn (p := 2) (hs := hA)
    (hμs := measure_ne_top μ _) (c := (1 : ℂ))] with x hx hAx
  have step1 : ∫ y, (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c : α × β → ℂ) (x, y)
      * f y ∂ν = ∫ y, (A ×ˢ B).indicator (fun _ => c) (x, y) * f y ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hx] with y hy
    rw [hy]
  rw [step1]
  have step2 : ∀ y, (A ×ˢ B).indicator (fun _ => c) (x, y) * f y =
      A.indicator (fun _ => c) x * B.indicator (fun y => f y) y := by
    intro y
    by_cases hxA : x ∈ A <;> by_cases hyB : y ∈ B <;>
      simp [Set.mem_prod, hxA, hyB]
  simp only [step2]
  rw [integral_const_mul, integral_indicator hB]
  rw [Pi.smul_apply, hAx]
  by_cases hxA : x ∈ A <;> simp [hxA, smul_eq_mul]

theorem isCompactOperator_kernelIntegralCLM_indicatorConst_prod {A : Set α} {B : Set β}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℂ) :
    IsCompactOperator (kernelIntegralCLM (μ := μ) (ν := ν)
      (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c)) := by
  have hfact : ⇑(kernelIntegralCLM (μ := μ) (ν := ν)
      (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c)) =
      ⇑(ContinuousLinearMap.toSpanSingleton ℂ
        (indicatorConstLp 2 hA (measure_ne_top μ _) (1 : ℂ))) ∘
      ⇑(c • (innerSL ℂ (indicatorConstLp 2 hB (measure_ne_top ν _) (1 : ℂ)))) := by
    funext f
    simp only [Function.comp_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [kernelIntegralCLM_indicatorConst_prod hA hB c f, inner_indicatorConstLp_one hB _ f]
  have : IsCompactOperator
      (⇑(c • (innerSL ℂ (indicatorConstLp 2 hB (measure_ne_top ν _) (1 : ℂ)))) :
        Lp ℂ 2 ν → ℂ) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have hcomp := this.clm_comp (ContinuousLinearMap.toSpanSingleton ℂ
    (indicatorConstLp 2 hA (measure_ne_top μ _) (1 : ℂ)))
  rw [show (⇑(kernelIntegralCLM (μ := μ) (ν := ν)
      (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c)) :
        Lp ℂ 2 ν → Lp ℂ 2 μ) = _ from hfact]
  exact hcomp

end RankOne

section Compactness

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

variable (μ ν) in

def compactKernels : Submodule ℂ (Lp ℂ 2 (μ.prod ν)) where
  carrier := {K | IsCompactOperator (kernelIntegralCLM K)}
  add_mem' {K K'} hK hK' := by
    have h : kernelIntegralCLM (K + K') = kernelIntegralCLM K + kernelIntegralCLM K' :=
      map_add _ _ _
    show IsCompactOperator (kernelIntegralCLM (K + K'))
    rw [h]
    exact hK.add hK'
  zero_mem' := by
    show IsCompactOperator (kernelIntegralCLM 0)
    have h : kernelIntegralCLM (0 : Lp ℂ 2 (μ.prod ν)) = 0 := map_zero _
    rw [h]
    exact isCompactOperator_zero
  smul_mem' c K hK := by
    have h : kernelIntegralCLM (c • K) = c • kernelIntegralCLM K := map_smul _ _ _
    show IsCompactOperator (kernelIntegralCLM (c • K))
    rw [h]
    exact hK.smul c

omit [IsFiniteMeasure μ] in
lemma mem_compactKernels {K : Lp ℂ 2 (μ.prod ν)} :
    K ∈ compactKernels μ ν ↔ IsCompactOperator (kernelIntegralCLM K) := Iff.rfl

omit [IsFiniteMeasure μ] in

theorem isClosed_compactKernels :
    IsClosed ((compactKernels μ ν : Set (Lp ℂ 2 (μ.prod ν)))) := by
  have : (compactKernels μ ν : Set (Lp ℂ 2 (μ.prod ν))) =
      ⇑(kernelIntegralₗ (μ := μ) (ν := ν)) ⁻¹' {T | IsCompactOperator T} := rfl
  rw [this]
  exact isClosed_setOf_isCompactOperator.preimage kernelIntegralₗ.continuous

theorem isSetSemiring_measurableRectangles :
    IsSetSemiring (Set.image2 (· ×ˢ ·) { s : Set α | MeasurableSet s }
      { t : Set β | MeasurableSet t }) := by
  classical
  constructor
  · exact ⟨∅, MeasurableSet.empty, ∅, MeasurableSet.empty, by simp⟩
  · rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨A', hA', B', hB', rfl⟩
    exact ⟨A ∩ A', hA.inter hA', B ∩ B', hB.inter hB', (Set.prod_inter_prod).symm⟩
  · rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨A', hA', B', hB', rfl⟩
    refine ⟨{(A \ A') ×ˢ B, (A ∩ A') ×ˢ (B \ B')}, ?_, ?_, ?_⟩
    · intro S hS
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hS
      rcases hS with rfl | rfl
      · exact ⟨A \ A', hA.diff hA', B, hB, rfl⟩
      · exact ⟨A ∩ A', hA.inter hA', B \ B', hB.diff hB', rfl⟩
    · intro S hS S' hS' hne
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hS hS'
      have hdisj : Disjoint ((A \ A') ×ˢ B) ((A ∩ A') ×ˢ (B \ B')) := by
        rw [Set.disjoint_left]
        rintro ⟨x, y⟩ hxy hxy'
        exact hxy.1.2 hxy'.1.2
      rcases hS with rfl | rfl <;> rcases hS' with rfl | rfl
      · exact absurd rfl hne
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hne
    · rw [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton]
      ext ⟨x, y⟩
      simp only [Set.mem_diff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
      tauto

theorem indicatorConst_prod_mem_compactKernels {A : Set α} {B : Set β} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (c : ℂ) :
    indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c ∈ compactKernels μ ν :=
  isCompactOperator_kernelIntegralCLM_indicatorConst_prod hA hB c

theorem indicatorConstLp_congr_set {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ}
    {p : ℝ≥0∞} {S S' : Set γ} (h : S = S') (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (hρS : ρ S ≠ ∞) (hρS' : ρ S' ≠ ∞) (c : ℂ) :
    indicatorConstLp p hS hρS c = indicatorConstLp p hS' hρS' c := by
  subst h; rfl

theorem indicatorConst_sup_mem_compactKernels (I : Finset (Set (α × β))) :
    ∀ (_ : ∀ R ∈ I, R ∈ Set.image2 (· ×ˢ ·) { s : Set α | MeasurableSet s }
        { t : Set β | MeasurableSet t })
      (_ : (↑I : Set (Set (α × β))).PairwiseDisjoint id)
      (hm : MeasurableSet (I.sup id)) (c : ℂ),
      indicatorConstLp 2 hm (measure_ne_top (μ.prod ν) _) c ∈ compactKernels μ ν := by
  classical
  induction I using Finset.cons_induction with
  | empty =>
    intro _ _ hm c
    rw [indicatorConstLp_congr_set (show (Finset.sup ∅ id : Set (α × β)) = ∅ by
      simp) hm MeasurableSet.empty (measure_ne_top _ _) (by simp) c]
    rw [indicatorConstLp_empty]
    exact (compactKernels μ ν).zero_mem
  | cons R I hRI ih =>
    intro hsub hdisj hm c
    have hRrect : R ∈ Set.image2 (· ×ˢ ·) { s : Set α | MeasurableSet s }
        { t : Set β | MeasurableSet t } := hsub R (Finset.mem_cons_self R I)
    obtain ⟨A, hA, B, hB, hR⟩ := hRrect
    have hRm : MeasurableSet R := hR ▸ hA.prod hB
    have hIm : MeasurableSet (I.sup id) := by
      refine Finset.sup_induction (by simp) (fun _ h _ h' => h.union h') ?_
      intro R' hR'
      obtain ⟨A', hA', B', hB', hR'eq⟩ := hsub R' (Finset.mem_cons_of_mem hR')
      exact hR'eq ▸ hA'.prod hB'
    have hdisjR : Disjoint R (I.sup id) := by
      refine Finset.disjoint_sup_right.mpr fun R' hR' => ?_
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_cons_self R I))
        (Finset.mem_coe.mpr (Finset.mem_cons_of_mem hR'))
        (fun h => hRI (h ▸ hR'))
    rw [indicatorConstLp_congr_set (show ((Finset.cons R I hRI).sup id : Set (α × β)) =
        R ∪ I.sup id by rw [Finset.sup_cons]; rfl) hm (hRm.union hIm)
      (measure_ne_top _ _) (measure_ne_top _ _) c]
    rw [indicatorConstLp_disjoint_union hRm hIm (measure_ne_top _ _) (measure_ne_top _ _)
      hdisjR c]
    refine (compactKernels μ ν).add_mem ?_ ?_
    · rw [indicatorConstLp_congr_set hR.symm hRm (hA.prod hB) (measure_ne_top _ _)
        (measure_ne_top _ _) c]
      exact indicatorConst_prod_mem_compactKernels hA hB c
    · exact ih (fun R' hR' => hsub R' (Finset.mem_cons_of_mem hR'))
        (hdisj.subset (Finset.coe_subset.mpr (Finset.subset_cons _))) hIm c

theorem indicatorConst_mem_compactKernels_of_mem_supClosure {S : Set (α × β)}
    (hS : S ∈ supClosure (Set.image2 (· ×ˢ ·) { s : Set α | MeasurableSet s }
      { t : Set β | MeasurableSet t })) (hSm : MeasurableSet S) (c : ℂ) :
    indicatorConstLp 2 hSm (measure_ne_top (μ.prod ν) _) c ∈ compactKernels μ ν := by
  classical
  obtain ⟨P, hP⟩ := isSetSemiring_measurableRectangles.mem_supClosure_iff.mp hS
  rw [indicatorConstLp_congr_set P.sup_parts.symm hSm
    (by rw [P.sup_parts]; exact hSm) (measure_ne_top _ _) (measure_ne_top _ _) c]
  exact indicatorConst_sup_mem_compactKernels P.parts (fun R hR => hP hR)
    P.supIndep.pairwiseDisjoint _ c

theorem indicatorConst_mem_compactKernels {S : Set (α × β)} (hS : MeasurableSet S) (c : ℂ) :
    indicatorConstLp 2 hS (measure_ne_top (μ.prod ν) _) c ∈ compactKernels μ ν := by
  classical

  have happrox : ∀ n : ℕ, ∃ T ∈ supClosure (Set.image2 (· ×ˢ ·)
      { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }),
      (μ.prod ν) (T ∆ S) < (n : ℝ≥0∞)⁻¹ := by
    intro n
    refine exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
      isSetSemiring_measurableRectangles ?_ generateFrom_prod.symm hS ?_
    · exact ⟨{Set.univ ×ˢ Set.univ}, Set.countable_singleton _,
        by rintro _ rfl; exact ⟨Set.univ, MeasurableSet.univ, Set.univ,
          MeasurableSet.univ, rfl⟩, by simp⟩
    · simp [ENNReal.inv_pos, ENNReal.natCast_ne_top]
  choose T hTmem hTlt using happrox
  have hTmeas : ∀ n, MeasurableSet (T n) := by
    intro n
    obtain ⟨P, hP⟩ :=
      isSetSemiring_measurableRectangles.mem_supClosure_iff.mp (hTmem n)
    rw [← P.sup_parts]
    refine Finset.sup_induction (by simp) (fun _ h _ h' => h.union h') ?_
    intro R hR
    obtain ⟨A, hA, B, hB, hReq⟩ := hP hR
    exact hReq ▸ hA.prod hB
  have htendsto : Filter.Tendsto (fun n => (μ.prod ν) (T n ∆ S)) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun n => zero_le') (fun n => (hTlt n).le)
  have hconv : Filter.Tendsto
      (fun n => indicatorConstLp 2 (hTmeas n) (measure_ne_top (μ.prod ν) _) c) Filter.atTop
      (nhds (indicatorConstLp 2 hS (measure_ne_top (μ.prod ν) _) c)) :=
    tendsto_indicatorConstLp_set (by norm_num) htendsto
  exact isClosed_compactKernels.mem_of_tendsto hconv
    (Filter.Eventually.of_forall fun n =>
      indicatorConst_mem_compactKernels_of_mem_supClosure (hTmem n) (hTmeas n) c)

variable (μ ν) in

theorem compactKernels_eq_top : compactKernels μ ν = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro K
  refine Lp.induction (by norm_num) (motive := fun K => K ∈ compactKernels μ ν) ?_ ?_ ?_ K
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact indicatorConst_mem_compactKernels hs c
  · intro f g hf hg _ hfmem hgmem
    exact (compactKernels μ ν).add_mem hfmem hgmem
  · exact isClosed_compactKernels

theorem isCompactOperator_kernelIntegralCLM (K : Lp ℂ 2 (μ.prod ν)) :
    IsCompactOperator (kernelIntegralCLM K) :=
  mem_compactKernels.mp (compactKernels_eq_top μ ν ▸ Submodule.mem_top)

theorem finiteDimensional_of_kernelIntegralCLM_eq_id {K : Lp ℂ 2 (ν.prod ν)}
    (h : kernelIntegralCLM K = ContinuousLinearMap.id ℂ (Lp ℂ 2 ν)) :
    FiniteDimensional ℂ (Lp ℂ 2 ν) := by
  have hcompact := isCompactOperator_kernelIntegralCLM K
  rw [h] at hcompact
  exact FiniteDimensional.of_isCompactOperator_id hcompact

end Compactness

section Gates

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

example {A : Set α} {B : Set β} (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℂ) :
    IsCompactOperator (kernelIntegralCLM (μ := μ) (ν := ν)
      (indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod ν) _) c)) :=
  isCompactOperator_kernelIntegralCLM _

end Gates

end L2

end MeasureTheory

/--
info: 'MeasureTheory.L2.lintegral_enorm_kernelIntegral_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.lintegral_enorm_kernelIntegral_sq_le

/--
info: 'MeasureTheory.L2.eLpNorm_kernelIntegral_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.eLpNorm_kernelIntegral_le

/--
info: 'MeasureTheory.MemLp.kernelIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.MemLp.kernelIntegral

/--
info: 'MeasureTheory.L2.norm_kernelIntegralCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.norm_kernelIntegralCLM_le

/--
info: 'MeasureTheory.L2.norm_kernelIntegralₗ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.norm_kernelIntegralₗ_le

/--
info: 'MeasureTheory.L2.kernelIntegralCLM_indicatorConst_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.kernelIntegralCLM_indicatorConst_prod

/--
info: 'MeasureTheory.L2.isCompactOperator_kernelIntegralCLM_indicatorConst_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.isCompactOperator_kernelIntegralCLM_indicatorConst_prod

/--
info: 'MeasureTheory.L2.compactKernels_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.compactKernels_eq_top

/--
info: 'MeasureTheory.L2.isCompactOperator_kernelIntegralCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.isCompactOperator_kernelIntegralCLM

/--
info: 'MeasureTheory.L2.finiteDimensional_of_kernelIntegralCLM_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.L2.finiteDimensional_of_kernelIntegralCLM_eq_id


