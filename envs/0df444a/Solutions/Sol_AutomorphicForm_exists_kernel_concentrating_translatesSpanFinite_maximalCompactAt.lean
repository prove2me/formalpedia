-- Prove2me | solution 1 for AutomorphicForm.exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fcf5da85-c298-5eb8-a0e4-11e88fb4a166

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory Filter Topology

namespace TraceKernel

noncomputable def wt (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (2 + M.trace.re) / 4

theorem continuous_wt : Continuous wt := by
  unfold wt
  exact (continuous_const.add (Complex.continuous_re.comp
    (continuous_id.matrix_trace))).div_const 4

theorem wt_one : wt 1 = 1 := by
  simp [wt]
  norm_num

def RowUnit (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ i : Fin 2, ‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2 = 1

theorem eq_one_of_norm_le_one_of_re_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1) (hre : z.re = 1) : z = 1 := by
  have hsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  rw [Complex.sq_norm, Complex.normSq_apply, hre] at hsq
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact Complex.ext (by simp [hre]) (by simp [him])

namespace RowUnit

variable {M : Matrix (Fin 2) (Fin 2) ℂ}

theorem norm_sq_le_one (h : RowUnit M) (i j : Fin 2) : ‖M i j‖ ^ 2 ≤ 1 := by
  have hi := h i
  have h0 := sq_nonneg ‖M i 0‖
  have h1 := sq_nonneg ‖M i 1‖
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · linarith
  · linarith

theorem norm_le_one (h : RowUnit M) (i j : Fin 2) : ‖M i j‖ ≤ 1 :=
  (sq_le_one_iff₀ (norm_nonneg _)).mp (h.norm_sq_le_one i j)

theorem re_le_one (h : RowUnit M) (i : Fin 2) : (M i i).re ≤ 1 :=
  (Complex.re_le_norm _).trans (h.norm_le_one i i)

theorem neg_one_le_re (h : RowUnit M) (i : Fin 2) : -1 ≤ (M i i).re := by
  have := (abs_le.mp (Complex.abs_re_le_norm (M i i))).1
  linarith [h.norm_le_one i i]

theorem wt_nonneg (h : RowUnit M) : 0 ≤ wt M := by
  have h0 := h.neg_one_le_re 0
  have h1 := h.neg_one_le_re 1
  simp only [wt, Matrix.trace_fin_two, Complex.add_re]
  linarith

theorem wt_le_one (h : RowUnit M) : wt M ≤ 1 := by
  have h0 := h.re_le_one 0
  have h1 := h.re_le_one 1
  simp only [wt, Matrix.trace_fin_two, Complex.add_re]
  linarith

theorem eq_one_of_wt_eq_one (h : RowUnit M) (h1 : wt M = 1) : M = 1 := by
  have hsum : (M 0 0).re + (M 1 1).re = 2 := by
    simp only [wt, Matrix.trace_fin_two, Complex.add_re] at h1
    linarith
  have h00 : M 0 0 = 1 :=
    eq_one_of_norm_le_one_of_re_eq_one (h.norm_le_one 0 0) (by linarith [h.re_le_one 0, h.re_le_one 1])
  have h11 : M 1 1 = 1 :=
    eq_one_of_norm_le_one_of_re_eq_one (h.norm_le_one 1 1) (by linarith [h.re_le_one 0, h.re_le_one 1])
  have h01 : M 0 1 = 0 := by
    have h' := h 0
    rw [h00, norm_one, one_pow] at h'
    have h'' : ‖M 0 1‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h'')
  have h10 : M 1 0 = 0 := by
    have h' := h 1
    rw [h11, norm_one, one_pow] at h'
    have h'' : ‖M 1 0‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h'')
  rw [Matrix.eta_fin_two M, Matrix.one_fin_two, h00, h01, h10, h11]

end RowUnit

section Places

variable {ι : Type*} [Fintype ι]

noncomputable def pwt (M : ι → Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∏ w, wt (M w)

theorem continuous_pwt : Continuous (pwt : (ι → Matrix (Fin 2) (Fin 2) ℂ) → ℝ) :=
  continuous_finsetProd _ fun w _ => continuous_wt.comp (continuous_apply w)

theorem pwt_one : pwt (1 : ι → Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  simp [pwt, wt_one]

variable {M : ι → Matrix (Fin 2) (Fin 2) ℂ}

theorem pwt_nonneg (h : ∀ w, RowUnit (M w)) : 0 ≤ pwt M :=
  Finset.prod_nonneg fun w _ => (h w).wt_nonneg

theorem pwt_le_one (h : ∀ w, RowUnit (M w)) : pwt M ≤ 1 :=
  Finset.prod_le_one (fun w _ => (h w).wt_nonneg) fun w _ => (h w).wt_le_one

theorem eq_one_of_pwt_eq_one (h : ∀ w, RowUnit (M w)) (h1 : pwt M = 1) : M = 1 := by
  classical
  funext w
  apply (h w).eq_one_of_wt_eq_one
  by_contra hne
  have hlt : wt (M w) < 1 := lt_of_le_of_ne (h w).wt_le_one hne
  have hlt' : pwt M < 1 := by
    unfold pwt
    rw [← Finset.mul_prod_erase Finset.univ (fun w => wt (M w)) (Finset.mem_univ w)]
    calc wt (M w) * ∏ x ∈ Finset.univ.erase w, wt (M x) ≤ wt (M w) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (h w).wt_nonneg
          exact Finset.prod_le_one (fun x _ => (h x).wt_nonneg) fun x _ => (h x).wt_le_one
      _ < 1 := by rw [mul_one]; exact hlt
  linarith

end Places

section Concentration

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {φ : X → ℝ}

omit [CompactSpace X] [μ.IsOpenPosMeasure] in
theorem integrable_pow (hφ : Continuous φ) (h0 : ∀ x, 0 ≤ φ x) (hle : ∀ x, φ x ≤ 1) (n : ℕ) :
    Integrable (fun x => φ x ^ n) μ := by
  refine (integrable_const (1 : ℝ)).mono' ((hφ.pow n).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) n)]
  exact pow_le_one₀ (h0 x) (hle x)

omit [CompactSpace X] in
theorem integral_pow_pos (hφ : Continuous φ) (h0 : ∀ x, 0 ≤ φ x) (hle : ∀ x, φ x ≤ 1)
    {x₀ : X} (hx₀ : φ x₀ = 1) (n : ℕ) : 0 < ∫ x, φ x ^ n ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => pow_nonneg (h0 x) n)
    (integrable_pow μ hφ h0 hle n)]
  exact (hφ.pow n).isOpen_support.measure_pos μ ⟨x₀, by simp [hx₀]⟩

theorem tendsto_setIntegral_pow_div (hφ : Continuous φ) (h0 : ∀ x, 0 ≤ φ x) (hle : ∀ x, φ x ≤ 1)
    {x₀ : X} (hx₀ : φ x₀ = 1) (hlt : ∀ x, x ≠ x₀ → φ x < 1)
    {U : Set X} (hU : U ∈ 𝓝 x₀) :
    Tendsto (fun n => (∫ x in Uᶜ, φ x ^ n ∂μ) / ∫ x, φ x ^ n ∂μ) atTop (𝓝 0) := by
  set C := (interior U)ᶜ with hC
  have hCc : IsClosed C := isOpen_interior.isClosed_compl
  have hCk : IsCompact C := hCc.isCompact
  have hx₀C : x₀ ∉ C := fun h => h (mem_interior_iff_mem_nhds.mpr hU)
  have hUC : Uᶜ ⊆ C := Set.compl_subset_compl.mpr interior_subset
  have hZ : ∀ n, 0 < ∫ x, φ x ^ n ∂μ := integral_pow_pos μ hφ h0 hle hx₀
  have hnum_nonneg : ∀ n, 0 ≤ ∫ x in Uᶜ, φ x ^ n ∂μ := fun n =>
    integral_nonneg fun x => pow_nonneg (h0 x) n
  have hnum_le : ∀ n, ∫ x in Uᶜ, φ x ^ n ∂μ ≤ ∫ x in C, φ x ^ n ∂μ := fun n =>
    setIntegral_mono_set (integrable_pow μ hφ h0 hle n).integrableOn
      (Eventually.of_forall fun x => pow_nonneg (h0 x) n) hUC.eventuallyLE
  by_cases hCe : C = ∅
  · have hz : ∀ n, (∫ x in Uᶜ, φ x ^ n ∂μ) = 0 := fun n => by
      have hUe : Uᶜ = ∅ := Set.subset_eq_empty hUC hCe
      rw [hUe, Measure.restrict_empty, integral_zero_measure]
    simp only [hz, zero_div]
    exact tendsto_const_nhds
  obtain ⟨x₁, hx₁C, hmax⟩ :=
    hCk.exists_isMaxOn (Set.nonempty_iff_ne_empty.mpr hCe) hφ.continuousOn
  set q := φ x₁ with hq
  have hq1 : q < 1 := hlt x₁ (fun h => hx₀C (h ▸ hx₁C))
  have hq0 : 0 ≤ q := h0 x₁
  set r := (q + 1) / 2 with hr
  have hqr : q < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := by rw [hr]; linarith
  set V := φ ⁻¹' Set.Ioi r with hV
  have hVo : IsOpen V := isOpen_Ioi.preimage hφ
  have hx₀V : x₀ ∈ V := by show r < φ x₀; rw [hx₀]; exact hr1
  have hμV : 0 < μ.real V :=
    ENNReal.toReal_pos (hVo.measure_pos μ ⟨x₀, hx₀V⟩).ne' (measure_ne_top μ V)
  have hden : ∀ n, r ^ n * μ.real V ≤ ∫ x, φ x ^ n ∂μ := fun n => by
    calc r ^ n * μ.real V = ∫ x in V, r ^ n ∂μ := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in V, φ x ^ n ∂μ :=
          setIntegral_mono_on (integrable_const _).integrableOn
            (integrable_pow μ hφ h0 hle n).integrableOn hVo.measurableSet
            (fun x hx => pow_le_pow_left₀ hr0.le (le_of_lt hx) n)
      _ ≤ ∫ x, φ x ^ n ∂μ :=
          setIntegral_le_integral (integrable_pow μ hφ h0 hle n)
            (Eventually.of_forall fun x => pow_nonneg (h0 x) n)
  have hnumC : ∀ n, ∫ x in C, φ x ^ n ∂μ ≤ q ^ n * μ.real C := fun n => by
    have key := norm_setIntegral_le_of_norm_le_const (measure_lt_top μ C)
      (f := fun x => φ x ^ n) (C := q ^ n) (fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) n)]
        exact pow_le_pow_left₀ (h0 x) (hmax hx) n)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using key)
  have hV0 : μ.real V ≠ 0 := hμV.ne'
  have hr0' : r ≠ 0 := hr0.ne'
  have hbound : ∀ n, (∫ x in Uᶜ, φ x ^ n ∂μ) / ∫ x, φ x ^ n ∂μ ≤
      (μ.real C / μ.real V) * (q / r) ^ n := fun n => by
    rw [div_le_iff₀ (hZ n)]
    calc ∫ x in Uᶜ, φ x ^ n ∂μ ≤ q ^ n * μ.real C := (hnum_le n).trans (hnumC n)
      _ = (μ.real C / μ.real V) * (q / r) ^ n * (r ^ n * μ.real V) := by
          rw [div_pow]; field_simp
      _ ≤ (μ.real C / μ.real V) * (q / r) ^ n * ∫ x, φ x ^ n ∂μ :=
          mul_le_mul_of_nonneg_left (hden n) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => div_nonneg (hnum_nonneg n) (hZ n).le) hbound
  have hlim : Tendsto (fun n => (μ.real C / μ.real V) * (q / r) ^ n) atTop
      (𝓝 ((μ.real C / μ.real V) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hq0 hr0.le)
      ((div_lt_one hr0).mpr hqr)).const_mul _
  simpa using hlim

end Concentration

section Span

variable {C : Type*} {ι : Type*} [Fintype ι]

noncomputable def affMap (ρ : C → ι → Matrix (Fin 2) (Fin 2) ℂ) :
    (ℝ × (ι → Matrix (Fin 2) (Fin 2) ℂ)) →ₗ[ℝ] (C → ℝ) where
  toFun p := fun k => p.1 + ∑ w, ((p.2 w * ρ k w).trace).re
  map_add' p q := by
    ext k
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.add_mul, Matrix.trace_add,
      Complex.add_re, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    ext k
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, mul_add,
      Finset.mul_sum]

noncomputable def affSpace (ρ : C → ι → Matrix (Fin 2) (Fin 2) ℂ) : Submodule ℝ (C → ℝ) :=
  LinearMap.range (affMap ρ)

theorem affSpace_fg (ρ : C → ι → Matrix (Fin 2) (Fin 2) ℂ) : (affSpace ρ).FG :=
  Module.Finite.iff_fg.mp (inferInstance : Module.Finite ℝ (LinearMap.range (affMap ρ)))

theorem wt_mul_mem_affSpace (ρ : C → ι → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) (w : ι) :
    (fun k => wt (B * ρ k w)) ∈ affSpace ρ := by
  classical
  refine ⟨((1 / 2 : ℝ), Pi.single w ((1 / 4 : ℝ) • B)), ?_⟩
  ext k
  simp only [affMap, LinearMap.coe_mk, AddHom.coe_mk, wt]
  rw [Finset.sum_eq_single w (fun w' _ hw' => by simp [hw']) (fun h => (h (Finset.mem_univ w)).elim)]
  simp only [Pi.single_eq_same, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul,
    Complex.re_ofReal_mul]
  ring

omit [Fintype ι] in
theorem prod_mem_pow {A : Type*} [CommSemiring A] [Algebra ℝ A] (P : Submodule ℝ A)
    {s : Finset ι} (f : ι → A) (h : ∀ i ∈ s, f i ∈ P) : ∏ i ∈ s, f i ∈ P ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem translate_pwt_pow_div_mem [Monoid C] (ρ : C →* (ι → Matrix (Fin 2) (Fin 2) ℂ)) (n : ℕ)
    (Z : ℝ) (a : C) :
    (fun k => pwt (ρ (a * k)) ^ n / Z) ∈ ((affSpace ρ) ^ (Finset.univ : Finset ι).card) ^ n := by
  have h1 : (fun k => pwt (ρ (a * k))) ∈ (affSpace ρ) ^ (Finset.univ : Finset ι).card := by
    have heq : (fun k => pwt (ρ (a * k))) = ∏ w, (fun k => wt (ρ a w * ρ k w)) := by
      ext k
      simp [pwt, map_mul, Finset.prod_apply, Pi.mul_apply]
    rw [heq]
    exact prod_mem_pow _ _ (fun w _ => wt_mul_mem_affSpace ρ (ρ a w) w)
  have h2 : (fun k => pwt (ρ (a * k))) ^ n ∈ ((affSpace ρ) ^ (Finset.univ : Finset ι).card) ^ n :=
    Submodule.pow_mem_pow _ h1 n
  have heq2 : (fun k => pwt (ρ (a * k)) ^ n / Z) = Z⁻¹ • (fun k => pwt (ρ (a * k))) ^ n := by
    ext k
    simp [Pi.pow_apply, div_eq_inv_mul]
  rw [heq2]
  exact Submodule.smul_mem _ _ h2

theorem exists_finset_translate_mem_span [Monoid C] (ρ : C →* (ι → Matrix (Fin 2) (Fin 2) ℂ))
    (n : ℕ) (Z : ℝ) :
    ∃ s : Finset (C → ℝ), ∀ a : C,
      (fun k => pwt (ρ (a * k)) ^ n / Z) ∈ Submodule.span ℝ (s : Set (C → ℝ)) := by
  obtain ⟨s, hs⟩ := ((affSpace_fg (ρ : C → ι → Matrix (Fin 2) (Fin 2) ℂ)).pow
    (Finset.univ : Finset ι).card).pow n
  exact ⟨s, fun a => hs ▸ translate_pwt_pow_div_mem ρ n Z a⟩

end Span

theorem exists_kernel {C : Type*} [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [OpensMeasurableSpace C] {ι : Type*} [Fintype ι]
    (ρ : C →* (ι → Matrix (Fin 2) (Fin 2) ℂ)) (hρc : Continuous ρ)
    (hρ1 : ∀ k, ρ k = 1 → k = 1) (hrow : ∀ k w, RowUnit (ρ k w))
    (μ : Measure C) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] :
    ∃ κ : ℕ → C → ℝ,
      (∀ n, Continuous (κ n)) ∧ (∀ n k, 0 ≤ κ n k) ∧ (∀ n, ∫ k, κ n k ∂μ = 1) ∧
      (∀ U ∈ nhds (1 : C), Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂μ) Filter.atTop (nhds 0)) ∧
      (∀ n, ∃ s : Finset (C → ℝ), ∀ a : C,
        (fun k => κ n (a * k)) ∈ Submodule.span ℝ (s : Set (C → ℝ))) := by
  set φ : C → ℝ := fun k => pwt (ρ k) with hφdef
  have hφc : Continuous φ := continuous_pwt.comp hρc
  have h0 : ∀ k, 0 ≤ φ k := fun k => pwt_nonneg (hrow k)
  have hle : ∀ k, φ k ≤ 1 := fun k => pwt_le_one (hrow k)
  have hφ1 : φ 1 = 1 := by simp [hφdef, map_one, pwt_one]
  have hlt : ∀ k, k ≠ 1 → φ k < 1 := fun k hk =>
    lt_of_le_of_ne (hle k) fun h => hk (hρ1 k (eq_one_of_pwt_eq_one (hrow k) h))
  set Z : ℕ → ℝ := fun n => ∫ k, φ k ^ n ∂μ with hZdef
  have hZ : ∀ n, 0 < Z n := integral_pow_pos μ hφc h0 hle hφ1
  refine ⟨fun n k => φ k ^ n / Z n, fun n => (hφc.pow n).div_const _,
    fun n k => div_nonneg (pow_nonneg (h0 k) n) (hZ n).le, fun n => ?_, fun U hU => ?_, fun n => ?_⟩
  · rw [integral_div]
    exact div_self (hZ n).ne'
  · simp_rw [integral_div]
    exact tendsto_setIntegral_pow_div μ hφc h0 hle hφ1 hlt hU
  · exact exists_finset_translate_mem_span ρ n (Z n)

end TraceKernel

namespace K1Glue

open NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

noncomputable def rho : ↥(maximalCompactAt K ∅) →* (InfinitePlace K → Matrix (Fin 2) (Fin 2) ℂ) where
  toFun k w := ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) w.Completion)).map (extensionEmbedding w)
  map_one' := by
    funext w
    simp only [OneMemClass.coe_one, map_one, Units.val_one, Pi.one_apply]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  map_mul' a b := by
    funext w
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul, Pi.mul_apply]
    exact Matrix.map_mul

theorem rho_apply (k : ↥(maximalCompactAt K ∅)) (w : InfinitePlace K) :
    rho K k w = ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) w.Completion)).map (extensionEmbedding w) := rfl

theorem continuous_rho : Continuous (rho K) := by
  refine continuous_pi fun w => ?_
  change Continuous fun k : ↥(maximalCompactAt K ∅) =>
    ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) w.Completion)).map (extensionEmbedding w)
  have h1 : Continuous fun k : ↥(maximalCompactAt K ∅) =>
      ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K))) :
        Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp ((continuous_archComponent K w).comp
      ((continuous_glArch (𝓞 K) K).comp continuous_subtype_val))
  exact h1.matrix_map (isometry_extensionEmbedding w).continuous

theorem rowUnit_rho (k : ↥(maximalCompactAt K ∅)) (w : InfinitePlace K) (i : Fin 2) :
    ‖rho K k w i 0‖ ^ 2 + ‖rho K k w i 1‖ ^ 2 = 1 := by
  have hk : (k : AdelicGL2 (𝓞 K) K) ∈ adelicMaximalCompact K := (mem_maximalCompactAt_iff.1 k.2).1
  have hiso := isRowIsometry_archComponent hk w
  have hnorm : ∀ x : w.Completion, ‖extensionEmbedding w x‖ = ‖x‖ :=
    (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
  simp only [rho_apply, Matrix.map_apply, hnorm]
  have h0 := hiso.2 1 0
  have h1 := hiso.2 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, one_pow,
    zero_pow two_ne_zero] at h0 h1
  fin_cases i
  · exact h0
  · exact h1

omit [NumberField K] in
theorem glInf_ext {a b : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ v : InfinitePlace K, archComponent K v a = archComponent K v b) : a = b := by
  apply Units.ext
  ext i j
  funext v
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.Completion) =>
    (m : Matrix (Fin 2) (Fin 2) (v.Completion))) (h v)) i) j
  rwa [archComponent_apply, archComponent_apply] at this

theorem glFin_ext {a b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (h : ∀ v, finComponent (𝓞 K) K v a = finComponent (𝓞 K) K v b) : a = b := by
  apply Units.ext
  ext i j v : 2
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.adicCompletion K) =>
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) (h v)) i) j
  rwa [finComponent_apply, finComponent_apply] at this

theorem glFin_eq_one (k : ↥(maximalCompactAt K ∅)) :
    glFin (𝓞 K) K (k : AdelicGL2 (𝓞 K) K) = 1 :=
  glFin_ext K fun v => by
    rw [map_one]; exact (mem_maximalCompactAt_iff.1 k.2).2 v (Finset.notMem_empty v)

theorem gl_ext {x y : AdelicGL2 (𝓞 K) K}
    (h₁ : glArch (𝓞 K) K x = glArch (𝓞 K) K y) (h₂ : glFin (𝓞 K) K x = glFin (𝓞 K) K y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem eq_one_of_rho_eq_one (k : ↥(maximalCompactAt K ∅)) (h : rho K k = 1) : k = 1 := by
  have harch : ∀ w, archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) = 1 := by
    intro w
    have hw := congrFun h w
    rw [rho_apply, Pi.one_apply] at hw
    apply Units.ext
    rw [Units.val_one]
    have hw' : ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) w.Completion)).map (extensionEmbedding w) =
        (1 : Matrix (Fin 2) (Fin 2) w.Completion).map (extensionEmbedding w) := by
      rw [hw, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (extensionEmbedding w).injective hw'
  have hA : glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K) = glArch (𝓞 K) K 1 :=
    glInf_ext K fun w => by rw [harch w, map_one, map_one]
  have hF : glFin (𝓞 K) K (k : AdelicGL2 (𝓞 K) K) = glFin (𝓞 K) K 1 := by
    rw [glFin_eq_one K k, map_one]
  exact Subtype.ext (gl_ext K hA hF)

end K1Glue

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ κ : ℕ → ↥(maximalCompactAt K ∅) → ℝ,
      (∀ n, Continuous (κ n)) ∧ (∀ n k, 0 ≤ κ n k) ∧ (∀ n, ∫ k, κ n k ∂(maximalCompactAtHaar K ∅) = 1) ∧
      (∀ U ∈ nhds (1 : ↥(maximalCompactAt K ∅)),
        Filter.Tendsto (fun n => ∫ k in Uᶜ, κ n k ∂(maximalCompactAtHaar K ∅)) Filter.atTop (nhds 0)) ∧
      (∀ n, ∃ s : Finset (↥(maximalCompactAt K ∅) → ℝ), ∀ a : ↥(maximalCompactAt K ∅),
        (fun k => κ n (a * k)) ∈ Submodule.span ℝ (s : Set (↥(maximalCompactAt K ∅) → ℝ))) := by
  exact TraceKernel.exists_kernel (K1Glue.rho K) (K1Glue.continuous_rho K)
    (K1Glue.eq_one_of_rho_eq_one K) (fun k w => K1Glue.rowUnit_rho K k w) (maximalCompactAtHaar K ∅)

end S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt
end P2MW
export P2MW.S_AutomorphicForm_exists_kernel_concentrating_translatesSpanFinite_maximalCompactAt (solution)
