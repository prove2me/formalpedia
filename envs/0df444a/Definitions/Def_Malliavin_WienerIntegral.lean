-- Prove2me | Definitions.Def_Malliavin_WienerIntegral
-- name    : Malliavin_WienerIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:49:13.985034+00:00
-- url     : https://prove2.me/theorems/ff5c329c-0e64-59cb-86e9-572f99e0cbb0
-- title:
--   Wiener Integral
-- statement:
--   Definitions and structural lemmas for Wiener Integral, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
namespace Malliavin
section Density
theorem nonnegativeLebesgueMeasure_Ioc_ne_top (a b : ℝ≥0) :
    nonnegativeLebesgueMeasure (Set.Ioc a b) ≠ ∞ := by
  rw [nonnegativeLebesgueMeasure_Ioc]
  exact ENNReal.ofReal_ne_top
theorem nonnegativeLebesgueMeasure_Iic_ne_top (T : ℝ≥0) :
    nonnegativeLebesgueMeasure (Set.Iic T) ≠ ∞ := by
  have hsub : Set.Iic T ⊆ Set.Icc 0 T := fun x hx ↦ ⟨zero_le, hx⟩
  exact ((measure_mono hsub).trans_lt isCompact_Icc.measure_lt_top).ne
theorem integrableOn_Ioc_of_memLp {g : ℝ≥0 → ℝ} (hg : MemLp g 2 nonnegativeLebesgueMeasure)
    (a b : ℝ≥0) : IntegrableOn g (Set.Ioc a b) nonnegativeLebesgueMeasure := by
  have : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) :=
    isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b)
  exact (hg.restrict _).integrable one_le_two
theorem setIntegral_Ioc_eq_zero {g : ℝ≥0 → ℝ} (hg : MemLp g 2 nonnegativeLebesgueMeasure)
    (h : ∀ t, ∫ s in Set.Ioc 0 t, g s ∂nonnegativeLebesgueMeasure = 0) (a b : ℝ≥0) :
    ∫ s in Set.Ioc a b, g s ∂nonnegativeLebesgueMeasure = 0 := by
  rcases le_or_gt b a with hab | hab
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    simp only [Measure.restrict_empty, integral_zero_measure]
  · have hunion : Set.Ioc 0 a ∪ Set.Ioc a b = Set.Ioc 0 b :=
      Set.Ioc_union_Ioc_eq_Ioc zero_le hab.le
    have hdisj : Disjoint (Set.Ioc 0 a) (Set.Ioc a b) :=
      Set.Ioc_disjoint_Ioc.mpr ((min_le_left a b).trans (le_max_right 0 a))
    have := setIntegral_union hdisj measurableSet_Ioc (integrableOn_Ioc_of_memLp hg 0 a)
      (integrableOn_Ioc_of_memLp hg a b)
    rw [hunion, h, h] at this
    linarith
theorem ae_eq_zero_of_forall_setIntegral_Ioc {g : ℝ≥0 → ℝ}
    (hg : MemLp g 2 nonnegativeLebesgueMeasure)
    (h : ∀ t, ∫ s in Set.Ioc 0 t, g s ∂nonnegativeLebesgueMeasure = 0) :
    g =ᵐ[nonnegativeLebesgueMeasure] 0 := by
  have hIoc := setIntegral_Ioc_eq_zero hg h
  have hT : ∀ T : ℕ, ∀ᵐ s ∂nonnegativeLebesgueMeasure, s ∈ Set.Iic (T : ℝ≥0) → g s = 0 := by
    intro T
    set μT := nonnegativeLebesgueMeasure.restrict (Set.Iic (T : ℝ≥0)) with hμT
    have : IsFiniteMeasure μT :=
      isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Iic_ne_top _)
    have hgT : Integrable g μT := (hg.restrict _).integrable one_le_two
    set gp : ℝ≥0 → ℝ := fun s ↦ max (g s) 0 with hgp_def
    set gm : ℝ≥0 → ℝ := fun s ↦ max (-g s) 0 with hgm_def
    have hgp : Integrable gp μT := hgT.pos_part
    have hgm : Integrable gm μT := hgT.neg_part
    have hgp_nn : ∀ s, 0 ≤ gp s := fun s ↦ le_max_right _ _
    have hgm_nn : ∀ s, 0 ≤ gm s := fun s ↦ le_max_right _ _
    have hsub : ∀ s, gp s - gm s = g s := fun s ↦ max_zero_sub_eq_self (g s)
    -- the integrals of `g` against `μT` over intervals and over the whole space vanish
    have hS : ∀ a b : ℝ≥0, ∫ s in Set.Ioc a b, g s ∂μT = 0 := by
      intro a b
      rw [hμT, Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Iic]
      exact hIoc _ _
    have huniv : ∫ s, g s ∂μT = 0 := by
      have hIic : Set.Iic (T : ℝ≥0) = Set.Icc (0 : ℝ≥0) T := by
        ext x
        simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
      rw [hμT, hIic, ← setIntegral_congr_set Ioc_ae_eq_Icc]
      exact hIoc _ _
    -- hence the finite measures `gp μT` and `gm μT` agree on intervals and on the whole space
    have hμ : μT.withDensity (fun s ↦ ENNReal.ofReal (gp s)) =
        μT.withDensity (fun s ↦ ENNReal.ofReal (gm s)) := by
      have : IsFiniteMeasure (μT.withDensity (fun s ↦ ENNReal.ofReal (gp s))) :=
        isFiniteMeasure_withDensity_ofReal hgp.hasFiniteIntegral
      apply Measure.ext_of_Ioc_finite
      · rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
          Measure.restrict_univ,
          ← ofReal_integral_eq_lintegral_ofReal hgp (Filter.Eventually.of_forall hgp_nn),
          ← ofReal_integral_eq_lintegral_ofReal hgm (Filter.Eventually.of_forall hgm_nn)]
        congr 1
        have := integral_sub hgp hgm
        simp only [hsub] at this
        linarith
      · intro a b _
        rw [withDensity_apply _ measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc,
          ← ofReal_integral_eq_lintegral_ofReal hgp.integrableOn
            (Filter.Eventually.of_forall hgp_nn),
          ← ofReal_integral_eq_lintegral_ofReal hgm.integrableOn
            (Filter.Eventually.of_forall hgm_nn)]
        congr 1
        have := integral_sub (hgp.integrableOn (s := Set.Ioc a b))
          (hgm.integrableOn (s := Set.Ioc a b))
        simp only [hsub] at this
        linarith [hS a b]
    rw [withDensity_eq_iff_of_sigmaFinite hgp.aemeasurable.ennreal_ofReal
      hgm.aemeasurable.ennreal_ofReal, hμT, Filter.EventuallyEq,
      ae_restrict_iff' measurableSet_Iic] at hμ
    filter_upwards [hμ] with s hs hsT
    have h1 := hs hsT
    rw [ENNReal.ofReal_eq_ofReal_iff (hgp_nn s) (hgm_nn s)] at h1
    have h2 := hsub s
    linarith
  rw [← ae_all_iff] at hT
  filter_upwards [hT] with s hs
  exact hs ⌈s⌉₊ (Nat.le_ceil s)
noncomputable def intervalIndicator (t : ℝ≥0) : Lp ℝ 2 nonnegativeLebesgueMeasure :=
  indicatorConstLp 2 measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t) (1 : ℝ)
theorem dense_span_intervalIndicator :
    Dense (Submodule.span ℝ (Set.range intervalIndicator) :
      Set (Lp ℝ 2 nonnegativeLebesgueMeasure)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have key : ∀ t, ∫ s in Set.Ioc 0 t, g s ∂nonnegativeLebesgueMeasure = 0 := fun t ↦ by
    rw [← L2.inner_indicatorConstLp_one measurableSet_Ioc
      (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)]
    exact hg _ (Submodule.subset_span ⟨t, rfl⟩)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_eq_zero_of_forall_setIntegral_Ioc (Lp.memLp g) key)
theorem inner_intervalIndicator (s t : ℝ≥0) :
    ⟪intervalIndicator s, intervalIndicator t⟫_ℝ = (min s t : ℝ) := by
  unfold intervalIndicator
  rw [L2.inner_indicatorConstLp_one, setIntegral_indicatorConstLp measurableSet_Ioc]
  have hinter : Set.Ioc 0 t ∩ Set.Ioc 0 s = Set.Ioc 0 (min s t) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, le_min_iff]
    tauto
  rw [hinter, measureReal_def, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (by
      simp only [NNReal.coe_min, NNReal.coe_zero, sub_zero, le_inf_iff,
        NNReal.zero_le_coe, and_self])]
  simp only [NNReal.coe_min, NNReal.coe_zero, sub_zero]
end Density
section WienerIntegral
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
noncomputable def brownianLp (hB : IsPreBrownianReal B P) (t : ℝ≥0) : Lp ℝ 2 P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.toLp (B t)
theorem coeFn_brownianLp (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (brownianLp hB t : Ω → ℝ) =ᵐ[P] B t :=
  MemLp.coeFn_toLp _
theorem inner_brownianLp (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ⟪brownianLp hB s, brownianLp hB t⟫_ℝ = (min s t : ℝ) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hcov := hB.covariance_eval s t
  rw [covariance_eq_sub hs ht, hB.integral_eval, hB.integral_eval, mul_zero, sub_zero,
    NNReal.coe_min] at hcov
  rw [L2.inner_def, ← hcov]
  apply integral_congr_ae
  filter_upwards [coeFn_brownianLp hB s, coeFn_brownianLp hB t] with ω hωs hωt
  rw [hωs, hωt]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm, Pi.mul_apply]
noncomputable def stepToLp : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 nonnegativeLebesgueMeasure :=
  Finsupp.linearCombination ℝ intervalIndicator
noncomputable def stepToRandom (hB : IsPreBrownianReal B P) : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (brownianLp hB)
theorem inner_stepToRandom (hB : IsPreBrownianReal B P) (v w : ℝ≥0 →₀ ℝ) :
    ⟪stepToRandom hB v, stepToRandom hB w⟫_ℝ = ⟪stepToLp v, stepToLp w⟫_ℝ := by
  unfold stepToRandom stepToLp
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_brownianLp, inner_intervalIndicator]
theorem norm_stepToRandom (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    ‖stepToRandom hB v‖ = ‖stepToLp v‖ := by
  have h := inner_stepToRandom hB v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
theorem denseRange_stepToLp : DenseRange stepToLp := by
  change Dense (Set.range stepToLp)
  rw [← LinearMap.coe_range, stepToLp, Finsupp.range_linearCombination]
  exact dense_span_intervalIndicator
noncomputable def wienerIntegral (hB : IsPreBrownianReal B P) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] Lp ℝ 2 P :=
  (stepToRandom hB).extendOfNorm stepToLp
theorem wienerIntegral_stepToLp (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    wienerIntegral hB (stepToLp v) = stepToRandom hB v :=
  LinearMap.extendOfNorm_eq denseRange_stepToLp
    ⟨1, fun v ↦ by rw [norm_stepToRandom, one_mul]⟩ v
theorem inner_wienerIntegral (hB : IsPreBrownianReal B P)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪wienerIntegral hB f, wienerIntegral hB g⟫_ℝ = ⟪f, g⟫_ℝ := by
  refine denseRange_stepToLp.induction_on₂
    (p := fun f g ↦ ⟪wienerIntegral hB f, wienerIntegral hB g⟫_ℝ = ⟪f, g⟫_ℝ) ?_ ?_ f g
  · exact isClosed_eq (((wienerIntegral hB).continuous.comp continuous_fst).inner
      ((wienerIntegral hB).continuous.comp continuous_snd))
      (continuous_fst.inner continuous_snd)
  · intro v w
    simp only [wienerIntegral_stepToLp, inner_stepToRandom]
theorem norm_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖wienerIntegral hB f‖ = ‖f‖ := by
  have h := inner_wienerIntegral hB f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
noncomputable def wienerIntegralₗᵢ (hB : IsPreBrownianReal B P) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] Lp ℝ 2 P :=
  ⟨(wienerIntegral hB).toLinearMap, norm_wienerIntegral hB⟩
section BrownianLink
def orderedBox {n : ℕ} (u v : Fin n → ℝ≥0) : Set (Fin n → ℝ≥0) :=
  Set.univ.pi fun i ↦ Set.Ioc (u i) (v i)
theorem measurableSet_orderedBox {n : ℕ} (u v : Fin n → ℝ≥0) :
    MeasurableSet (orderedBox u v) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc
theorem iteratedKernelMeasure_orderedBox_ne_top {n : ℕ} (u v : Fin n → ℝ≥0) :
    iteratedKernelMeasure n (orderedBox u v) ≠ ∞ := by
  rw [orderedBox, iteratedKernelMeasure, Measure.pi_pi]
  exact ENNReal.prod_ne_top fun i _ ↦ nonnegativeLebesgueMeasure_Ioc_ne_top _ _
noncomputable def boxKernel {n : ℕ} (u v : Fin n → ℝ≥0) : IteratedKernel n :=
  indicatorConstLp 2 (measurableSet_orderedBox u v) (iteratedKernelMeasure_orderedBox_ne_top u v)
    (1 : ℝ)
structure IteratedIntegralFamily.IsBrownian (J : IteratedIntegralFamily P) (B : ℝ≥0 → Ω → ℝ) :
    Prop where
  box : ∀ (n : ℕ) (u v : Fin n → ℝ≥0), (∀ i, u i ≤ v i) → (∀ i j, i < j → v i ≤ u j) →
    (fun ω ↦ J.integral n (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v
theorem measurePreserving_funUnique_symm_nnreal :
    MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ≥0).symm nonnegativeLebesgueMeasure
      (iteratedKernelMeasure 1) :=
  (measurePreserving_funUnique nonnegativeLebesgueMeasure (Fin 1)).symm _
noncomputable def kernelToLine : IteratedKernel 1 →ₗᵢ[ℝ] Lp ℝ 2 nonnegativeLebesgueMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ _ measurePreserving_funUnique_symm_nnreal
noncomputable def wienerIntegralKernel (hB : IsPreBrownianReal B P) :
    IteratedKernel 1 →L[ℝ] RandomL2 P :=
  (wienerIntegral hB).comp kernelToLine.toContinuousLinearMap
end BrownianLink
section SecondChaos
theorem holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 :=
  ⟨by rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
theorem memLp_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (B t) p P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp hp
theorem memLp_two_incr_mul_incr (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    MemLp (fun ω ↦ (B b ω - B a ω) * (B d ω - B c ω)) 2 P :=
  have := holderTriple_four_four_two
  MemLp.mul' ((memLp_eval hB d (p := 4) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB c (p := 4) ENNReal.ofNat_ne_top))
    ((memLp_eval hB b (p := 4) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB a (p := 4) ENNReal.ofNat_ne_top))
noncomputable def incrementProductLp (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    RandomL2 P :=
  (memLp_two_incr_mul_incr hB a b c d).toLp _
end SecondChaos
section Gaussian
open CameronMartin
def stepSum (B : ℝ≥0 → Ω → ℝ) (v : ℝ≥0 →₀ ℝ) : Ω → ℝ :=
  fun ω ↦ v.sum fun t c ↦ c * B t ω
end Gaussian
section FirstChaos
noncomputable def firstChaos (hB : IsPreBrownianReal B P) : Submodule ℝ (RandomL2 P) :=
  (Submodule.span ℝ (Set.range (brownianLp hB))).topologicalClosure
end FirstChaos
section UnitIncrements
noncomputable def unitIncrementLp (hB : IsPreBrownianReal B P) (k : ℕ) : RandomL2 P :=
  brownianLp hB (k + 1) - brownianLp hB k
end UnitIncrements
end WienerIntegral
end Malliavin


