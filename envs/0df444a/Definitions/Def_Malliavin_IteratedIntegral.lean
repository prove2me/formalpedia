-- Prove2me | Definitions.Def_Malliavin_IteratedIntegral
-- name    : Malliavin_IteratedIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:46:35.802797+00:00
-- url     : https://prove2.me/theorems/c98ac16f-c8d3-5c21-b553-95f48b0f9393
-- title:
--   Iterated Integral
-- statement:
--   Definitions and structural lemmas for Iterated Integral, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Theorems.Thm_Malliavin_measurableSet_simplex
import Theorems.Thm_Malliavin_mem_simplex
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
namespace Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
structure IsWienerCov (W : ℝ≥0 → Ω → ℝ) : Prop where
  integrable_W : ∀ t, Integrable (W t)
  integrable_prod : ∀ s t, Integrable fun x => W s x * W t x
  mean_zero : ∀ t, ∫ x, W t x = 0
  covariance : ∀ s t, ∫ x, W s x * W t x = min s t
section Step
variable {W : ℝ≥0 → Ω → ℝ}
structure Partition (n : ℕ) where
  /-- The partition times `t 0 < t 1 < ⋯ < t n`. -/
  t : Fin (n + 1) → ℝ≥0
  /-- The partition starts at time `0`. -/
  start : t 0 = 0
  /-- The partition times are strictly increasing. -/
  mono : StrictMono t
omit [MeasureSpace Ω] in
/-- Stochastic integral of the step function taking the value `a i` on the
time interval `[P.t i, P.t (i+1)]`. -/
def stepIntegral (W : ℝ≥0 → Ω → ℝ) {n : ℕ} (P : Partition n) (a : Fin n → ℝ) : Ω → ℝ :=
  fun x => ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
omit [MeasureSpace Ω] in
@[simp] lemma stepIntegral_add {n : ℕ} (P : Partition n) (a b : Fin n → ℝ) :
    stepIntegral W P (a + b) = stepIntegral W P a + stepIntegral W P b := by
  funext x
  change ∑ i : Fin n, (a i + b i) * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
        + ∑ i : Fin n, b i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
  have hterm : ∀ i : Fin n, (a i + b i) * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
        + b i * (W (P.t i.succ) x - W (P.t i.castSucc) x) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
omit [MeasureSpace Ω] in
@[simp] lemma stepIntegral_smul {n : ℕ} (P : Partition n) (c : ℝ) (a : Fin n → ℝ) :
    stepIntegral W P (c • a) = c • stepIntegral W P a := by
  funext x
  change ∑ i : Fin n, c * a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = c * ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
  calc ∑ i : Fin n, c * a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)
      = ∑ i : Fin n, c * (a i * (W (P.t i.succ) x - W (P.t i.castSucc) x)) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = c * ∑ i : Fin n, a i * (W (P.t i.succ) x - W (P.t i.castSucc) x) :=
        (Finset.mul_sum _ _ _).symm
end Step
def chainIntegral {n : ℕ} (W : ℝ≥0 → Ω → ℝ) (u v : Fin n → ℝ≥0) : Ω → ℝ :=
  fun x => ∏ i, (W (v i) x - W (u i) x)
section ContinuousTower
open ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace lp
variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P : Measure Ω'}
  {B : ℝ≥0 → Ω' → ℝ}
lemma measurableEmbedding_nnrealCoe_iterated :
    MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding
noncomputable def nonnegativeLebesgueMeasure : Measure ℝ≥0 :=
  Measure.comap ((↑) : ℝ≥0 → ℝ) (volume : Measure ℝ)
theorem nonnegativeLebesgueMeasure_Ioc (a b : ℝ≥0) :
    nonnegativeLebesgueMeasure (Set.Ioc a b) = ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
  have himage : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc a b = Set.Ioc (a : ℝ) b := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
      exact ⟨by exact_mod_cast hay, by exact_mod_cast hyb⟩
    · rintro ⟨hax, hxb⟩
      have hx0 : 0 ≤ x := le_trans a.coe_nonneg hax.le
      exact ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hax, by exact_mod_cast hxb⟩, rfl⟩
  rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.comap_apply,
    himage, Real.volume_Ioc]
instance nonnegativeLebesgueMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts nonnegativeLebesgueMeasure :=
  IsFiniteMeasureOnCompacts.comap' (volume : Measure ℝ) NNReal.continuous_coe
    measurableEmbedding_nnrealCoe_iterated
instance nonnegativeLebesgueMeasure_sigmaFinite :
    SigmaFinite nonnegativeLebesgueMeasure := inferInstance
instance nonnegativeLebesgueMeasure_nullSingletonClass :
    NullSingletonClass nonnegativeLebesgueMeasure where
  measure_singleton x := by
    rw [nonnegativeLebesgueMeasure, measurableEmbedding_nnrealCoe_iterated.comap_apply,
      Set.image_singleton, Real.volume_singleton]
noncomputable abbrev iteratedKernelMeasure (n : ℕ) : Measure (Fin n → ℝ≥0) :=
  Measure.pi fun _ : Fin n => nonnegativeLebesgueMeasure
noncomputable abbrev IteratedKernel (n : ℕ) := Lp ℝ 2 (iteratedKernelMeasure n)
abbrev RandomL2 (P : Measure Ω') := Lp ℝ 2 P
abbrev processMeasurableSpace (B : ℝ≥0 → Ω' → ℝ) : MeasurableSpace Ω' :=
  ⨆ t : ℝ≥0, MeasurableSpace.comap (B t) (borel ℝ)
def IsWienerGenerated (B : ℝ≥0 → Ω' → ℝ) : Prop :=
  processMeasurableSpace B = ‹MeasurableSpace Ω'›
theorem processMeasurableSpace_le_of_measurable
    (hmeas : ∀ t, Measurable (B t)) :
    processMeasurableSpace B ≤ mΩ' :=
  iSup_le fun t ↦ (hmeas t).comap_le
noncomputable abbrev processTrimMeasure
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t)) :
    @Measure Ω' (processMeasurableSpace B) :=
  P.trim (processMeasurableSpace_le_of_measurable hmeas)
theorem measurePreserving_id_processTrim
    (hmeas : ∀ t, Measurable (B t)) :
    @MeasurePreserving Ω' Ω' mΩ' (processMeasurableSpace B) id P
      (processTrimMeasure P B hmeas) := by
  let hm : processMeasurableSpace B ≤ mΩ' :=
    processMeasurableSpace_le_of_measurable hmeas
  have hid : @Measurable Ω' Ω' mΩ' (processMeasurableSpace B) id :=
    @measurable_id'' Ω' (processMeasurableSpace B) mΩ' hm
  exact @MeasurePreserving.mk Ω' Ω' mΩ' (processMeasurableSpace B)
    id P (processTrimMeasure P B hmeas) hid (trim_eq_map hm).symm
noncomputable def processLpEmbedding
    (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) (hmeas : ∀ t, Measurable (B t)) :
    (@Lp Ω' ℝ (processMeasurableSpace B) inferInstance 2
      (processTrimMeasure P B hmeas)) →ₗᵢ[ℝ] RandomL2 P := by
  exact @Lp.compMeasurePreservingₗᵢ Ω' ℝ mΩ' 2 P _ Ω'
    (processMeasurableSpace B) (processTrimMeasure P B hmeas) ℝ _ _ _ _ id
    (measurePreserving_id_processTrim hmeas)
structure IteratedIntegralFamily (P : Measure Ω') where
  /-- The order-`n` operator `Jₙ`. -/
  integral : (n : ℕ) → IteratedKernel n →L[ℝ] RandomL2 P
  /-- Polarized simplex isometry. -/
  sameOrder : ∀ (n : ℕ) (f g : IteratedKernel n),
    inner ℝ (integral n f) (integral n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n
  /-- Positive-order operators have centered output. -/
  centered : ∀ (n : ℕ), 0 < n → ∀ f : IteratedKernel n,
    ∫ ω, integral n f ω ∂P = 0
  /-- The zeroth-order integral is the constant represented by its kernel. -/
  zeroOrder : ∀ f : IteratedKernel 0,
    (fun ω => integral 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0
  /-- Outputs of different orders are orthogonal. -/
  differentOrder : ∀ {m n : ℕ}, m ≠ n → ∀ (f : IteratedKernel m) (g : IteratedKernel n),
    inner ℝ (integral m f) (integral n g) = 0
  /-- Restriction to the simplex is contractive, hence so is `Jₙ`. -/
  norm_integral_le : ∀ (n : ℕ) (f : IteratedKernel n), ‖integral n f‖ ≤ ‖f‖
namespace IteratedIntegralConstruction
section HilbertBasisCountability
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]
omit [CompleteSpace E] in
lemma countable_hilbertBasis_index {ι : Type*} (b : HilbertBasis ι ℝ E) :
    Countable ι := by
  let s : Set E := Set.range b
  have hs_orth : Orthonormal ℝ ((↑) : s → E) := b.orthonormal.toSubtypeRange
  have hs_discrete : DiscreteTopology s := by
    apply DiscreteTopology.of_forall_le_dist (r := 1) zero_lt_one
    intro x y hxy
    have hinner : inner ℝ (x : E) (y : E) = 0 := hs_orth.inner_eq_zero hxy
    have hsq : ‖(x : E) - (y : E)‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℝ)]
      norm_num [hs_orth.norm_eq_one, hinner]
    have hnorm : 1 ≤ ‖(x : E) - (y : E)‖ := by
      nlinarith [norm_nonneg ((x : E) - (y : E))]
    simpa only [Subtype.dist_eq, dist_eq_norm] using hnorm
  let _ : DiscreteTopology s := hs_discrete
  let _ : Countable s := countable_of_Lindelof_of_discrete
  exact (Equiv.ofInjective b b.orthonormal.linearIndependent.injective).injective.countable
end HilbertBasisCountability
end IteratedIntegralConstruction
namespace IteratedIntegralConstruction
noncomputable abbrev SimplexKernel (n : ℕ) :=
  Lp ℝ 2 ((iteratedKernelMeasure n).restrict (simplex ℝ≥0 n))
lemma restrictedSimplexMeasure_le (n : ℕ) :
    (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n) ≤
      (1 : ℝ≥0∞) • iteratedKernelMeasure n := by
  simpa only [one_smul] using
    (Measure.restrict_le_self :
      (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n) ≤ iteratedKernelMeasure n)
noncomputable def restrictToSimplex (n : ℕ) :
    IteratedKernel n →L[ℝ] SimplexKernel n := by
  exact Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (c := 1)
    (by norm_num) (restrictedSimplexMeasure_le n)
lemma restrictToSimplex_ae (n : ℕ) (f : IteratedKernel n) :
    restrictToSimplex n f =ᵐ[(iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)] f := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞)) (c := 1)
    (by norm_num) (restrictedSimplexMeasure_le n) f
lemma inner_restrictToSimplex (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (restrictToSimplex n f) (restrictToSimplex n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [restrictToSimplex_ae n f, restrictToSimplex_ae n g] with t hft hgt
  rw [hft, hgt]
lemma norm_restrictToSimplex_le (n : ℕ) (f : IteratedKernel n) :
    ‖restrictToSimplex n f‖ ≤ ‖f‖ := by
  have hop : ‖restrictToSimplex n‖ ≤ 1 := by
    simpa only [restrictToSimplex, ENNReal.toReal_one, Real.one_rpow] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le
        (E := ℝ) (p := (2 : ℝ≥0∞)) (c := 1)
        (by norm_num) (restrictedSimplexMeasure_le n))
  calc
    ‖restrictToSimplex n f‖ ≤ ‖restrictToSimplex n‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm (restrictToSimplex n) f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg f)
    _ = ‖f‖ := one_mul _
lemma memLp_zeroExtension (n : ℕ) (g : SimplexKernel n) :
    MemLp ((simplex ℝ≥0 n).indicator (fun t ↦ g t)) (2 : ℝ≥0∞)
      (iteratedKernelMeasure n) := by
  rw [memLp_indicator_iff_restrict (measurableSet_simplex n)]
  exact Lp.memLp g
noncomputable def zeroExtendSimplex (n : ℕ) (g : SimplexKernel n) :
    IteratedKernel n :=
  (memLp_zeroExtension n g).toLp ((simplex ℝ≥0 n).indicator (fun t ↦ g t))
noncomputable def symmetrizeRestrict (n : ℕ) :
    IteratedKernel n →L[ℝ] SimplexKernel n := by
  exact (restrictToSimplex n).comp
    (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2)
noncomputable def symmetrizedRightInverse (n : ℕ) :
    SimplexKernel n → IteratedKernel n := by
  exact fun g ↦ (n.factorial : ℝ) •
    symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (zeroExtendSimplex n g)
lemma iteratedKernelMeasure_zero :
    iteratedKernelMeasure 0 = Measure.dirac (0 : Fin 0 → ℝ≥0) := by
  simpa only [iteratedKernelMeasure] using
    (Measure.pi_of_empty (fun _ : Fin 0 ↦ nonnegativeLebesgueMeasure)
      (0 : Fin 0 → ℝ≥0))
lemma simplex_zero : simplex ℝ≥0 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  change StrictMono t
  intro i
  exact Fin.elim0 i
instance iteratedKernelMeasure_zero_isProbability :
    IsProbabilityMeasure (iteratedKernelMeasure 0) := by
  rw [iteratedKernelMeasure_zero]
  infer_instance
theorem integral_iteratedKernelMeasure_zero (φ : (Fin 0 → ℝ≥0) → ℝ) :
    ∫ t, φ t ∂iteratedKernelMeasure 0 = φ 0 := by
  rw [iteratedKernelMeasure_zero]
  exact integral_dirac _ _
theorem setIntegral_simplex_zero (φ : (Fin 0 → ℝ≥0) → ℝ) :
    ∫ t in simplex ℝ≥0 0, φ t ∂iteratedKernelMeasure 0 = φ 0 := by
  rw [simplex_zero, Measure.restrict_univ]
  exact integral_iteratedKernelMeasure_zero φ
noncomputable def zeroKernelOne : IteratedKernel 0 :=
  Lp.const 2 (iteratedKernelMeasure 0) (1 : ℝ)
noncomputable def zeroKernelIntegral : IteratedKernel 0 →L[ℝ] ℝ :=
  innerSL ℝ zeroKernelOne
theorem zeroKernelIntegral_apply (f : IteratedKernel 0) :
    zeroKernelIntegral f = ∫ t, f t ∂iteratedKernelMeasure 0 := by
  rw [zeroKernelIntegral, innerSL_apply_apply, zeroKernelOne, ← indicatorConstLp_univ,
    L2.inner_indicatorConstLp_one MeasurableSet.univ
      (measure_ne_top (iteratedKernelMeasure 0) Set.univ), Measure.restrict_univ]
noncomputable def probabilityConstL (hB : IsPreBrownianReal B P) :
    ℝ →L[ℝ] RandomL2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact Lp.constL 2 P ℝ
theorem probabilityConstL_coe (hB : IsPreBrownianReal B P) (c : ℝ) :
    (fun ω ↦ probabilityConstL hB c ω) =ᵐ[P] fun _ ↦ c := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := P) c
  filter_upwards [h] with ω hω
  exact hω
noncomputable def zeroIntegralCLM (hB : IsPreBrownianReal B P) :
    IteratedKernel 0 →L[ℝ] RandomL2 P :=
  (probabilityConstL hB).comp zeroKernelIntegral
theorem zeroIntegralCLM_coe (hB : IsPreBrownianReal B P) (f : IteratedKernel 0) :
    (fun ω ↦ zeroIntegralCLM hB f ω) =ᵐ[P]
      fun _ ↦ ∫ t, f t ∂iteratedKernelMeasure 0 := by
  simpa only [zeroIntegralCLM, ContinuousLinearMap.comp_apply, zeroKernelIntegral_apply] using
    probabilityConstL_coe hB (zeroKernelIntegral f)
theorem zeroIntegralCLM_sameOrder (hB : IsPreBrownianReal B P)
    (f g : IteratedKernel 0) :
    inner ℝ (zeroIntegralCLM hB f) (zeroIntegralCLM hB g) =
      ∫ t in simplex ℝ≥0 0, inner ℝ (f t) (g t) ∂iteratedKernelMeasure 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [zeroIntegralCLM_coe hB f, zeroIntegralCLM_coe hB g]
      with ω hf hg
    rw [hf, hg])]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_iteratedKernelMeasure_zero (fun t ↦ f t),
    integral_iteratedKernelMeasure_zero (fun t ↦ g t),
    setIntegral_simplex_zero (fun t ↦ inner ℝ (f t) (g t))]
theorem zeroIntegralCLM_inner_centered (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) (X : RandomL2 P) (hX : ∫ ω, X ω ∂P = 0) :
    inner ℝ (zeroIntegralCLM hB f) X = 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [L2.inner_def]
  calc
    ∫ ω, inner ℝ (zeroIntegralCLM hB f ω) (X ω) ∂P =
        ∫ ω, (∫ t, f t ∂iteratedKernelMeasure 0) * X ω ∂P := by
          apply integral_congr_ae
          filter_upwards [zeroIntegralCLM_coe hB f] with ω hω
          rw [hω]
          exact Real.inner_apply _ _
    _ = (∫ t, f t ∂iteratedKernelMeasure 0) * ∫ ω, X ω ∂P :=
      integral_const_mul _ _
    _ = 0 := by rw [hX, mul_zero]
theorem zeroIntegralCLM_norm_le (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) : ‖zeroIntegralCLM hB f‖ ≤ ‖f‖ := by
  have hsq : ‖zeroIntegralCLM hB f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← @real_inner_self_eq_norm_sq _ _ _ (zeroIntegralCLM hB f),
      ← @real_inner_self_eq_norm_sq _ _ _ f,
      zeroIntegralCLM_sameOrder hB f f, L2.inner_def, simplex_zero,
      Measure.restrict_univ]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq).le
end IteratedIntegralConstruction
namespace IteratedIntegralConstruction
def unitIncrement (B : ℝ≥0 → Ω' → ℝ) (k : ℕ) : Ω' → ℝ :=
  fun ω => B (k + 1) ω - B k ω
theorem unitIncrement_memLp (hB : IsPreBrownianReal B P) (k : ℕ) :
    MemLp (unitIncrement B k) 2 P :=
  hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
theorem integral_unitIncrement (hB : IsPreBrownianReal B P) (k : ℕ) :
    ∫ ω, unitIncrement B k ω ∂P = 0 := by
  change ∫ ω, B (k + 1) ω - B k ω ∂P = 0
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
    hB.integral_eval, hB.integral_eval, sub_zero]
theorem integral_unitIncrement_sq (hB : IsPreBrownianReal B P) (k : ℕ) :
    ∫ ω, unitIncrement B k ω * unitIncrement B k ω ∂P = 1 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm := unitIncrement_memLp hB k
  have hc := covariance_eq_sub hm hm
  rw [integral_unitIncrement hB, mul_zero, sub_zero] at hc
  calc
    ∫ ω, unitIncrement B k ω * unitIncrement B k ω ∂P =
        ∫ ω, (unitIncrement B k * unitIncrement B k) ω ∂P := rfl
    _ = cov[unitIncrement B k, unitIncrement B k; P] := hc.symm
    _ = Var[unitIncrement B k; P] := covariance_self hm.aemeasurable
    _ = Var[id; gaussianReal 0 (nndist ((k + 1 : ℝ≥0) : ℝ) ((k : ℝ≥0) : ℝ))] :=
      (hB.hasLaw_sub (k + 1) k).variance_eq
    _ = 1 := by
      rw [variance_id_gaussianReal]
      norm_num [nndist]
      rfl
theorem iIndepFun_unitIncrement (hB : IsPreBrownianReal B P) :
    iIndepFun (unitIncrement B) P := by
  unfold unitIncrement
  have h := hB.hasIndepIncrements.nat
    (t := fun k : ℕ => (k : ℝ≥0)) (fun _ _ hab => Nat.cast_le.mpr hab)
  simpa only [Nat.cast_add, Nat.cast_one] using h
theorem integral_unitIncrement_mul_of_ne (hB : IsPreBrownianReal B P)
    {k l : ℕ} (hkl : k ≠ l) :
    ∫ ω, unitIncrement B k ω * unitIncrement B l ω ∂P = 0 := by
  have hi := (iIndepFun_unitIncrement hB).indepFun hkl
  rw [hi.integral_fun_mul_eq_mul_integral
    (unitIncrement_memLp hB k).aestronglyMeasurable
    (unitIncrement_memLp hB l).aestronglyMeasurable,
    integral_unitIncrement hB, zero_mul]
noncomputable def unitIncrementL2 (hB : IsPreBrownianReal B P) (k : ℕ) :
    RandomL2 P :=
  (unitIncrement_memLp hB k).toLp (unitIncrement B k)
theorem unitIncrementL2_orthonormal (hB : IsPreBrownianReal B P) :
    Orthonormal ℝ (unitIncrementL2 hB) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [L2.inner_def]
  simp only [Real.inner_apply]
  change ∫ a, unitIncrementL2 hB k a * unitIncrementL2 hB l a ∂P = _
  have hk := MemLp.coeFn_toLp (unitIncrement_memLp hB k)
  have hl := MemLp.coeFn_toLp (unitIncrement_memLp hB l)
  have hcoe : (fun a => unitIncrementL2 hB k a * unitIncrementL2 hB l a) =ᵐ[P]
      fun a => unitIncrement B k a * unitIncrement B l a := by
    filter_upwards [hk, hl] with a hka hla
    exact congrArg₂ (· * ·) hka hla
  rw [integral_congr_ae hcoe]
  by_cases hkl : k = l
  · subst l
    rw [if_pos rfl]
    exact integral_unitIncrement_sq hB k
  · rw [if_neg hkl]
    exact integral_unitIncrement_mul_of_ne hB hkl
local instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
noncomputable abbrev PositiveKernelSum :=
  lp (fun n : ℕ ↦ SimplexKernel (n + 1)) 2
def orderedBoxLeft {n : ℕ} (i : Fin (n + 1)) : ℝ≥0 :=
  2 * (i.1 : ℝ≥0)
def orderedUnitBox (n : ℕ) : Set (Fin (n + 1) → ℝ≥0) :=
  Set.univ.pi fun i ↦ Set.Ioc (orderedBoxLeft i) (orderedBoxLeft i + 1)
theorem measurableSet_orderedUnitBox (n : ℕ) :
    MeasurableSet (orderedUnitBox n) :=
  MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ioc
theorem orderedUnitBox_subset_simplex (n : ℕ) :
    orderedUnitBox n ⊆ simplex ℝ≥0 (n + 1) := by
  intro t ht
  rw [mem_simplex]
  intro i j hij
  have hit := (Set.mem_pi.mp ht) i (Set.mem_univ i)
  have hjt := (Set.mem_pi.mp ht) j (Set.mem_univ j)
  have hij' : i.1 + 1 ≤ j.1 := by omega
  have hij'' : (i.1 : ℝ≥0) + 1 ≤ (j.1 : ℝ≥0) := by exact_mod_cast hij'
  have hsep : orderedBoxLeft i + 1 < orderedBoxLeft j := by
    dsimp only [orderedBoxLeft]
    calc
      2 * (i.1 : ℝ≥0) + 1 < 2 * (i.1 : ℝ≥0) + 2 := by norm_num
      _ = 2 * ((i.1 : ℝ≥0) + 1) := by ring
      _ ≤ 2 * (j.1 : ℝ≥0) := by gcongr
  exact lt_of_le_of_lt hit.2 (hsep.trans hjt.1)
theorem measure_orderedUnitBox (n : ℕ) :
    iteratedKernelMeasure (n + 1) (orderedUnitBox n) = 1 := by
  change (Measure.pi fun _ : Fin (n + 1) ↦ nonnegativeLebesgueMeasure)
      (Set.univ.pi fun i ↦ Set.Ioc (orderedBoxLeft i) (orderedBoxLeft i + 1)) = 1
  rw [Measure.pi_pi]
  simp only [orderedBoxLeft, nonnegativeLebesgueMeasure_Ioc, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_one, add_sub_cancel_left, ENNReal.ofReal_one,
    Finset.prod_const_one]
theorem restrict_measure_orderedUnitBox (n : ℕ) :
    ((iteratedKernelMeasure (n + 1)).restrict (simplex ℝ≥0 (n + 1)))
        (orderedUnitBox n) = 1 := by
  rw [Measure.restrict_apply (measurableSet_orderedUnitBox n),
    Set.inter_eq_left.mpr (orderedUnitBox_subset_simplex n)]
  exact measure_orderedUnitBox n
noncomputable def simplexUnitBoxIndicator (n : ℕ) : SimplexKernel (n + 1) :=
  indicatorConstLp 2 (measurableSet_orderedUnitBox n)
    (by rw [restrict_measure_orderedUnitBox n]; norm_num) (1 : ℝ)
theorem norm_simplexUnitBoxIndicator (n : ℕ) : ‖simplexUnitBoxIndicator n‖ = 1 := by
  rw [simplexUnitBoxIndicator, norm_indicatorConstLp (by norm_num) (by norm_num),
    measureReal_def, restrict_measure_orderedUnitBox]
  norm_num
noncomputable def simplexBasisSet (n : ℕ) : Set (SimplexKernel (n + 1)) :=
  Classical.choose (exists_hilbertBasis ℝ (SimplexKernel (n + 1)))
noncomputable abbrev simplexBasisIndex (n : ℕ) : Type :=
  simplexBasisSet n
noncomputable def simplexBasis (n : ℕ) :
    HilbertBasis (simplexBasisIndex n) ℝ (SimplexKernel (n + 1)) :=
  Classical.choose (show ∃ b : HilbertBasis (simplexBasisIndex n) ℝ
      (SimplexKernel (n + 1)), ⇑b = Subtype.val from
    Classical.choose_spec (exists_hilbertBasis ℝ (SimplexKernel (n + 1))))
noncomputable local instance simplexBasisIndex_countable (n : ℕ) :
    Countable (simplexBasisIndex n) := by
  exact countable_hilbertBasis_index (simplexBasis n)
theorem simplexBasisIndex_nonempty (n : ℕ) : Nonempty (simplexBasisIndex n) := by
  by_contra h
  have hz : (simplexBasis n).repr (simplexUnitBoxIndicator n) = 0 := by
    ext i
    exact (h ⟨i⟩).elim
  have hu : simplexUnitBoxIndicator n = 0 :=
    (simplexBasis n).repr.injective (by simpa only [map_zero] using hz)
  have hnorm := norm_simplexUnitBoxIndicator n
  rw [hu, norm_zero] at hnorm
  norm_num at hnorm
noncomputable def globalBasisIndexPoint (n : ℕ) :
    Σ k : ℕ, simplexBasisIndex k :=
  ⟨n, Classical.choice (simplexBasisIndex_nonempty n)⟩
theorem globalBasisIndexPoint_injective :
    Function.Injective globalBasisIndexPoint := by
  intro i j hij
  exact congrArg Sigma.fst hij
noncomputable local instance globalBasisIndex_infinite :
    Infinite (Σ n : ℕ, simplexBasisIndex n) :=
  Infinite.of_injective globalBasisIndexPoint globalBasisIndexPoint_injective
noncomputable def globalBasisVector
    (a : Σ n : ℕ, simplexBasisIndex n) : PositiveKernelSum :=
  lp.single 2 a.1 (simplexBasis a.1 a.2)
theorem globalBasisVector_orthonormal : Orthonormal ℝ globalBasisVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨n, i⟩ ⟨m, j⟩
  change inner ℝ
      (lp.single 2 n (simplexBasis n i) : PositiveKernelSum)
      (lp.single 2 m (simplexBasis m j) : PositiveKernelSum) = _
  rw [lp.inner_single_left]
  by_cases hnm : n = m
  · subst m
    rw [lp.single_apply_self (E := fun k : ℕ ↦ SimplexKernel (k + 1))]
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using
      (orthonormal_iff_ite.mp (simplexBasis n).orthonormal i j)
  · rw [lp.single_apply_ne (E := fun k : ℕ ↦ SimplexKernel (k + 1)) 2 m
      (simplexBasis m j) hnm]
    simp only [inner_zero_right, Sigma.mk.injEq, hnm, false_and, ↓reduceIte]
theorem globalBasisVector_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range globalBasisVector))ᗮ = ⊥ := by
  classical
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [lp.eq_zero_iff_coeFn_eq_zero]
  funext n
  apply (simplexBasis n).repr.injective
  ext i
  rw [(simplexBasis n).repr_apply_apply]
  have hinner := (Submodule.mem_orthogonal' _ _).mp hx
    (globalBasisVector ⟨n, i⟩)
    (Submodule.subset_span ⟨⟨n, i⟩, rfl⟩)
  change inner ℝ x (lp.single 2 n (simplexBasis n i)) = 0 at hinner
  rw [lp.inner_single_right] at hinner
  simpa only [real_inner_comm, Pi.zero_apply, map_zero, ZeroMemClass.coe_zero,
    PreLp.zero_apply] using hinner
noncomputable def positiveKernelHilbertBasis :
    HilbertBasis (Σ n : ℕ, simplexBasisIndex n) ℝ PositiveKernelSum :=
  HilbertBasis.mkOfOrthogonalEqBot globalBasisVector_orthonormal
    globalBasisVector_orthogonal_eq_bot
noncomputable def l2CongrLeft {ι κ : Type*} (e : ι ≃ κ) :
    ℓ²(ι, ℝ) ≃ₗᵢ[ℝ] ℓ²(κ, ℝ) where
  toFun f := ⟨fun j ↦ f (e.symm j), by
    change Memℓp (fun j : κ ↦ f (e.symm j)) (2 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
    exact e.symm.summable_iff.mpr
      ((memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp f))⟩
  invFun g := ⟨fun i ↦ g (e i), by
    change Memℓp (fun i : ι ↦ g (e i)) (2 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)]
    exact e.summable_iff.mpr
      ((memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp g))⟩
  left_inv f := by ext i; simp only [Equiv.symm_apply_apply]
  right_inv g := by ext j; simp only [Equiv.apply_symm_apply]
  map_add' f g := by ext j; rfl
  map_smul' c f := by ext j; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num),
      lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num)]
    congr 1
    simpa only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs,
      ENNReal.toReal_ofNat, Real.rpow_ofNat, sq_abs] using
      (e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal))
noncomputable def probabilityOne (hB : IsPreBrownianReal B P) : RandomL2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ)
@[simp] theorem norm_probabilityOne (hB : IsPreBrownianReal B P) :
    ‖probabilityOne hB‖ = 1 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [probabilityOne, norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def]
  rw [measure_univ]
  norm_num
noncomputable abbrev CenteredRandomL2 (hB : IsPreBrownianReal B P) :=
  (ℝ ∙ probabilityOne hB)ᗮ
noncomputable def centeredUnitIncrement (hB : IsPreBrownianReal B P) (k : ℕ) :
    CenteredRandomL2 hB := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨unitIncrementL2 hB k, ?_⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  change inner ℝ
    (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ))
    (unitIncrementL2 hB k) = 0
  rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
  unfold unitIncrementL2
  rw [integral_congr_ae (MemLp.coeFn_toLp (unitIncrement_memLp hB k))]
  exact integral_unitIncrement hB k
theorem centeredUnitIncrement_orthonormal (hB : IsPreBrownianReal B P) :
    Orthonormal ℝ (centeredUnitIncrement hB) := by
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ (unitIncrementL2 hB i) (unitIncrementL2 hB j) = _
  exact orthonormal_iff_ite.mp (unitIncrementL2_orthonormal hB) i j
theorem nonempty_positiveKernelSum_equiv_centered
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (CenteredRandomL2 hB)] :
    Nonempty (PositiveKernelSum ≃ₗᵢ[ℝ] CenteredRandomL2 hB) := by
  have hw := centeredUnitIncrement_orthonormal hB
  have hw_range : Orthonormal ℝ ((↑) : Set.range (centeredUnitIncrement hB) →
      CenteredRandomL2 hB) := hw.toSubtypeRange
  obtain ⟨sF, bF, hw_sub, _hbF⟩ := hw_range.exists_hilbertBasis_extension
  let _ : Countable sF := countable_hilbertBasis_index bF
  have hsF_inf : sF.Infinite :=
    (Set.infinite_range_of_injective hw.linearIndependent.injective).mono hw_sub
  let _ : Infinite sF := Set.infinite_coe_iff.mpr hsF_inf
  let e : (Σ n : ℕ, simplexBasisIndex n) ≃ sF := nonempty_equiv_of_countable.some
  exact ⟨positiveKernelHilbertBasis.repr.trans ((l2CongrLeft e).trans bF.repr.symm)⟩
noncomputable def positiveKernelEmbeddingCentered
    (hB : IsPreBrownianReal B P) : PositiveKernelSum →ₗᵢ[ℝ] CenteredRandomL2 hB := by
  let hex := exists_injective_nat (Σ n : ℕ, simplexBasisIndex n)
  let e := Classical.choose hex
  have he : Function.Injective e := Classical.choose_spec hex
  exact (((centeredUnitIncrement_orthonormal hB).comp e he).orthogonalFamily.linearIsometry).comp
    positiveKernelHilbertBasis.repr.toLinearIsometry
def processMeasurableL2Exhausts (P : Measure Ω') (B : ℝ≥0 → Ω' → ℝ) : Prop :=
  ∃ hmeas : ∀ t, Measurable (B t), Function.Surjective (processLpEmbedding P B hmeas)
noncomputable def positiveIteratedTowerLI (hB : IsPreBrownianReal B P) :
    PositiveKernelSum →ₗᵢ[ℝ] CenteredRandomL2 hB := by
  classical
  exact if h : Nonempty (SecondCountableTopology (CenteredRandomL2 hB)) ∧
      processMeasurableL2Exhausts P B then
      let _ : SecondCountableTopology (CenteredRandomL2 hB) := Classical.choice h.1
      (Classical.choice (nonempty_positiveKernelSum_equiv_centered hB)).toLinearIsometry
    else
      positiveKernelEmbeddingCentered hB
noncomputable def singleKernelLI (n : ℕ) :
    SimplexKernel (n + 1) →ₗᵢ[ℝ] PositiveKernelSum where
  toLinearMap := lp.lsingle (𝕜 := ℝ)
    (E := fun k : ℕ ↦ SimplexKernel (k + 1)) (2 : ℝ≥0∞) n
  norm_map' f := lp.norm_single (E := fun k : ℕ ↦ SimplexKernel (k + 1))
    (p := (2 : ℝ≥0∞)) (by norm_num) n f
noncomputable def simplexIntegralLI (hB : IsPreBrownianReal B P) (n : ℕ) :
    SimplexKernel (n + 1) →ₗᵢ[ℝ] RandomL2 P :=
  (CenteredRandomL2 hB).subtypeₗᵢ.comp
    ((positiveIteratedTowerLI hB).comp (singleKernelLI n))
@[simp] theorem simplexIntegralLI_apply (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : SimplexKernel (n + 1)) :
    simplexIntegralLI hB n f =
      ((positiveIteratedTowerLI hB (lp.single 2 n f) : CenteredRandomL2 hB) :
        RandomL2 P) :=
  rfl
noncomputable def positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel (n + 1) →L[ℝ] RandomL2 P :=
  (simplexIntegralLI hB n).toContinuousLinearMap.comp (restrictToSimplex (n + 1))
theorem inner_positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f g : IteratedKernel (n + 1)) :
    inner ℝ (positiveIntegralCLM hB n f) (positiveIntegralCLM hB n g) =
      ∫ t in simplex ℝ≥0 (n + 1), inner ℝ (f t) (g t)
        ∂iteratedKernelMeasure (n + 1) := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change inner ℝ (simplexIntegralLI hB n (restrictToSimplex (n + 1) f))
    (simplexIntegralLI hB n (restrictToSimplex (n + 1) g)) = _
  rw [LinearIsometry.inner_map_map]
  exact inner_restrictToSimplex (n + 1) f g
theorem integral_positiveIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel (n + 1)) :
    ∫ ω, positiveIntegralCLM hB n f ω ∂P = 0 := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmem : simplexIntegralLI hB n (restrictToSimplex (n + 1) f) ∈
      (ℝ ∙ probabilityOne hB)ᗮ := by
    simpa only [simplexIntegralLI_apply] using
      (positiveIteratedTowerLI hB
        (lp.single 2 n (restrictToSimplex (n + 1) f))).property
  have hi := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  change inner ℝ
    (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P Set.univ) (1 : ℝ))
    (simplexIntegralLI hB n (restrictToSimplex (n + 1) f)) = 0 at hi
  rwa [L2.inner_indicatorConstLp_one, setIntegral_univ] at hi
theorem inner_positiveIntegralCLM_ne (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel (m + 1)) (g : IteratedKernel (n + 1)) :
    inner ℝ (positiveIntegralCLM hB m f) (positiveIntegralCLM hB n g) = 0 := by
  change inner ℝ
    ((CenteredRandomL2 hB).subtypeₗᵢ
      (positiveIteratedTowerLI hB
        (lp.single 2 m (restrictToSimplex (m + 1) f))))
    ((CenteredRandomL2 hB).subtypeₗᵢ
      (positiveIteratedTowerLI hB
        (lp.single 2 n (restrictToSimplex (n + 1) g)))) = 0
  rw [LinearIsometry.inner_map_map, LinearIsometry.inner_map_map]
  change inner ℝ
    (lp.single 2 m (restrictToSimplex (m + 1) f) : PositiveKernelSum)
    (lp.single 2 n (restrictToSimplex (n + 1) g) : PositiveKernelSum) = 0
  rw [lp.inner_single_left,
    lp.single_apply_ne (E := fun k : ℕ ↦ SimplexKernel (k + 1)) 2 n
      (restrictToSimplex (n + 1) g) hmn]
  exact inner_zero_right _
theorem norm_positiveIntegralCLM_le (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel (n + 1)) : ‖positiveIntegralCLM hB n f‖ ≤ ‖f‖ := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply]
  change ‖simplexIntegralLI hB n (restrictToSimplex (n + 1) f)‖ ≤ ‖f‖
  rw [LinearIsometry.norm_map]
  exact norm_restrictToSimplex_le (n + 1) f
noncomputable def integralCLM (hB : IsPreBrownianReal B P) :
    (n : ℕ) → IteratedKernel n →L[ℝ] RandomL2 P
  | 0 => zeroIntegralCLM hB
  | n + 1 => positiveIntegralCLM hB n
theorem integralCLM_sameOrder (hB : IsPreBrownianReal B P)
    (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (integralCLM hB n f) (integralCLM hB n g) =
      ∫ t in simplex ℝ≥0 n, inner ℝ (f t) (g t) ∂iteratedKernelMeasure n := by
  cases n with
  | zero => exact zeroIntegralCLM_sameOrder hB f g
  | succ n => exact inner_positiveIntegralCLM hB n f g
theorem integralCLM_centered (hB : IsPreBrownianReal B P)
    (n : ℕ) (hn : 0 < n) (f : IteratedKernel n) :
    ∫ ω, integralCLM hB n f ω ∂P = 0 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n => exact integral_positiveIntegralCLM hB n f
theorem integralCLM_zeroOrder (hB : IsPreBrownianReal B P)
    (f : IteratedKernel 0) :
    (fun ω => integralCLM hB 0 f ω) =ᵐ[P]
      fun _ => ∫ t, f t ∂iteratedKernelMeasure 0 :=
  zeroIntegralCLM_coe hB f
theorem integralCLM_differentOrder (hB : IsPreBrownianReal B P)
    {m n : ℕ} (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (integralCLM hB m f) (integralCLM hB n g) = 0 := by
  cases m with
  | zero =>
      cases n with
      | zero => exact False.elim (hmn rfl)
      | succ n =>
          exact zeroIntegralCLM_inner_centered hB f (positiveIntegralCLM hB n g)
            (integral_positiveIntegralCLM hB n g)
  | succ m =>
      cases n with
      | zero =>
          rw [real_inner_comm]
          exact zeroIntegralCLM_inner_centered hB g (positiveIntegralCLM hB m f)
            (integral_positiveIntegralCLM hB m f)
      | succ n =>
          have hmn' : m ≠ n := fun h => hmn (congrArg Nat.succ h)
          exact inner_positiveIntegralCLM_ne hB hmn' f g
theorem integralCLM_norm_le (hB : IsPreBrownianReal B P)
    (n : ℕ) (f : IteratedKernel n) : ‖integralCLM hB n f‖ ≤ ‖f‖ := by
  cases n with
  | zero => exact zeroIntegralCLM_norm_le hB f
  | succ n => exact norm_positiveIntegralCLM_le hB n f
noncomputable def family (hB : IsPreBrownianReal B P) : IteratedIntegralFamily P where
  integral := integralCLM hB
  sameOrder := integralCLM_sameOrder hB
  centered := integralCLM_centered hB
  zeroOrder := integralCLM_zeroOrder hB
  differentOrder := integralCLM_differentOrder hB
  norm_integral_le := integralCLM_norm_le hB
end IteratedIntegralConstruction
noncomputable def iteratedIntegralFamily
    (hB : IsPreBrownianReal B P) : IteratedIntegralFamily P :=
  IteratedIntegralConstruction.family hB
noncomputable def iteratedIntegralCLM (hB : IsPreBrownianReal B P) (n : ℕ) :
    IteratedKernel n →L[ℝ] RandomL2 P :=
  (iteratedIntegralFamily hB).integral n
end ContinuousTower
end Malliavin


