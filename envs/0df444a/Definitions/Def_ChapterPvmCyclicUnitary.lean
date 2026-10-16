-- Prove2me | Definitions.Def_ChapterPvmCyclicUnitary
-- name    : ChapterPvmCyclicUnitary
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T00:53:26.028984+00:00
-- url     : https://prove2.me/theorems/a44c212d-126e-4d50-af51-430dae8a791c
-- title:
--   The Lean 4 theorem `lp2_norm_sq_eq_integral` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPvmCyclicUnitary.lean`): generated def bundle for ChapterPvmCyclicUnitary. See BookProof/ChapterPvmCyclicUnitary.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPvmCyclicUnitary.lean

import Theorems.Thm_BookProof_ChapterOrthogonalSums_norm_sum_sq_of_orthogonal

import Theorems.Thm_BookProof_ChapterMackeyQuasiInvariant_proj_coeFn


import Theorems.Thm_BookProof_ChapterPvmMeasure_pvmMeasure_eq_zero_iff


import Theorems.Thm_BookProof_ChapterPvmMeasure_Pvm_add_of_disjoint

import Definitions.Def_ChapterPvmMeasure
import Definitions.Def_ChapterMackeyQuasiInvariant
import Mathlib


/-!
# The spectral theorem for a cyclic projection-valued measure

Second step towards the converse of Mackey's imprimitivity theorem over a *continuous*
base.  Let `P` be a projection-valued measure on a measurable space `X` acting on a complex
Hilbert space `H`, and let `ψ` be a **cyclic** vector for `P`.  Write
`μ = pvmMeasure P ψ : E ↦ ‖P(E) ψ‖²`, a finite measure on `X`.

**Theorem** (`pvm_cyclic_unitary`).  There is a unitary `W : L²(X, μ) ≃ H` with
`W (1_E) = P(E) ψ` for every measurable `E`, and `W` carries multiplication by the
indicator of `E` to `P(E)`:
`W (P_E f) = P(E) (W f)`, where `P_E` is the multiplication projection of
`BookProof.ChapterMackeyQuasiInvariant`.

In other words: a projection-valued measure with a cyclic vector *is* the multiplication
projection-valued measure of `L²` of a finite measure.  This is the measure-theoretic
replacement of the discrete decomposition used in
`BookProof.ChapterMackeyGeneralBase`.

The construction is the classical one: the map `1_E ↦ P(E) ψ` is defined on simple
functions by `MeasureTheory.SimpleFunc.setToSimpleFunc`, it is isometric because the
projections of disjoint sets are orthogonal and `‖P(E) ψ‖² = μ(E)`, and it is extended to
`L²` by density and surjectivity follows from cyclicity.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmCyclicUnitary

open BookProof.ChapterPvmMeasure BookProof.ChapterMackeyQuasiInvariant

attribute [local instance] Lp.simpleFunc.module Lp.simpleFunc.normedSpace

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The `L²`-norm as an integral -/

/-- The square of the `L²`-norm is the integral of the square of the modulus. -/
theorem lp2_norm_sq_eq_integral (μ : Measure X) (F : Lp ℂ 2 μ) :
    ‖F‖ ^ 2 = ∫ x, ‖(F : X → ℂ) x‖ ^ 2 ∂μ := by
  have hint : Integrable (fun x => (inner ℂ ((F : X → ℂ) x) ((F : X → ℂ) x) : ℂ)) μ :=
    L2.integrable_inner F F
  have h1 : ‖F‖ ^ 2 = RCLike.re (inner ℂ F F : ℂ) := by
    have := @inner_self_eq_norm_sq ℂ (Lp ℂ 2 μ) _ _ _ F
    simpa using this.symm
  have h2 := integral_re hint
  rw [h1, L2.inner_def, ← h2]
  refine integral_congr_ae ?_
  filter_upwards with x
  have := @inner_self_eq_norm_sq ℂ ℂ _ _ _ ((F : X → ℂ) x)
  simpa using this

/-! ## Multiplication by an indicator is a bounded operator on `L²` -/

theorem integrable_norm_sq (μ : Measure X) (f : Lp ℂ 2 μ) :
    Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) μ := by
  have h := (L2.integrable_inner (𝕜 := ℂ) f f).re
  refine h.congr ?_
  filter_upwards with x
  have := @inner_self_eq_norm_sq ℂ ℂ _ _ _ ((f : X → ℂ) x)
  simpa using this

theorem proj_add (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f g : Lp ℂ 2 μ) :
    proj μ hE (f + g) = proj μ hE f + proj μ hE g := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hE (f + g), proj_coeFn μ hE f, proj_coeFn μ hE g,
    Lp.coeFn_add f g, Lp.coeFn_add (proj μ hE f) (proj μ hE g)] with x e1 e2 e3 e4 e5
  simp only [Pi.add_apply] at e4 e5
  rw [e1, e5, e2, e3]
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx, e4]
  · simp only [Set.indicator_of_notMem hx, add_zero]

theorem proj_smul (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (c : ℂ) (f : Lp ℂ 2 μ) :
    proj μ hE (c • f) = c • proj μ hE f := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hE (c • f), proj_coeFn μ hE f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (proj μ hE f)] with x e1 e2 e3 e4
  simp only [Pi.smul_apply] at e3 e4
  rw [e1, e4, e2]
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx, e3]
  · simp only [Set.indicator_of_notMem hx, smul_zero]

theorem norm_proj_le (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp ℂ 2 μ) :
    ‖proj μ hE f‖ ≤ ‖f‖ := by
  have hsq : ‖proj μ hE f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [lp2_norm_sq_eq_integral μ (proj μ hE f), lp2_norm_sq_eq_integral μ f]
    refine integral_mono_ae (integrable_norm_sq μ (proj μ hE f)) (integrable_norm_sq μ f) ?_
    filter_upwards [proj_coeFn μ hE f] with x e1
    rw [e1]
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have h1 : (0:ℝ) ≤ ‖proj μ hE f‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖f‖ := norm_nonneg _
  nlinarith [hsq]

/-- Multiplication by the indicator of `E`, as a continuous linear map on `L²`. -/
noncomputable def projL (μ : Measure X) {E : Set X} (hE : MeasurableSet E) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => proj μ hE f
      map_add' := proj_add μ hE
      map_smul' := fun c f => proj_smul μ hE c f } 1
    (fun f => by simpa using norm_proj_le μ hE f)

@[simp] theorem projL_apply (μ : Measure X) {E : Set X} (hE : MeasurableSet E)
    (f : Lp ℂ 2 μ) : projL μ hE f = proj μ hE f := rfl

/-! ## The projection-valued measure as an additive set function -/

variable (P : Pvm X H) (ψ : H)

/-- The projection-valued measure read as a set function with values in `ℂ →L[ℝ] H`. -/
noncomputable def pvmT (s : Set X) : ℂ →L[ℝ] H :=
  (((ContinuousLinearMap.id ℂ ℂ).smulRight (P.p s ψ))).restrictScalars ℝ

@[simp] theorem pvmT_apply (s : Set X) (c : ℂ) : pvmT P ψ s c = c • P.p s ψ := rfl

theorem pvmT_empty : pvmT P ψ ∅ = 0 := by
  ext c
  simp [P.p_empty]

theorem pvmT_smul (c : ℂ) (s : Set X) (x : ℂ) : pvmT P ψ s (c • x) = c • pvmT P ψ s x := by
  simp [smul_smul]

theorem pvmT_zero_of_measure_zero (s : Set X) (hs : MeasurableSet s)
    (h0 : pvmMeasure P ψ s = 0) : pvmT P ψ s = 0 := by
  ext c
  simp [(pvmMeasure_eq_zero_iff P ψ hs).mp h0]

theorem pvmT_finMeasAdditive : FinMeasAdditive (pvmMeasure P ψ) (pvmT P ψ) := by
  intro s t hs ht _ _ hd
  ext c
  simp [P.add_of_disjoint hs ht hd, smul_add]

theorem norm_pvm_sq {E : Set X} (hE : MeasurableSet E) :
    ‖P.p E ψ‖ ^ 2 = (pvmMeasure P ψ E).toReal := by
  rw [pvmMeasure_apply P ψ hE, ENNReal.toReal_ofReal (by positivity)]

/-! ## The map on simple functions -/

/-- The norm of `∑ c · P(f⁻¹{c}) ψ`, by orthogonality. -/
theorem norm_setToSimpleFunc_sq (f : SimpleFunc X ℂ) :
    ‖SimpleFunc.setToSimpleFunc (pvmT P ψ) f‖ ^ 2
      = ∑ c ∈ f.range, ‖c‖ ^ 2 * (pvmMeasure P ψ (f ⁻¹' {c})).toReal := by
  classical
  have horth : ∀ x y : ℂ, x ≠ y →
      ⟪pvmT P ψ (f ⁻¹' {x}) x, pvmT P ψ (f ⁻¹' {y}) y⟫_ℂ = 0 := by
    intro x y hxy
    rw [pvmT_apply, pvmT_apply, inner_smul_left, inner_smul_right]
    have hd : Disjoint (f ⁻¹' {x}) (f ⁻¹' {y}) := by
      rw [Set.disjoint_left]
      intro a hax hay
      simp only [Set.mem_preimage] at hax hay
      exact hxy (hax ▸ hay ▸ rfl)
    rw [P.inner_eq_zero (f.measurableSet_fiber x) (f.measurableSet_fiber y) hd]
    simp
  rw [SimpleFunc.setToSimpleFunc,
    BookProof.ChapterOrthogonalSums.norm_sum_sq_of_orthogonal f.range horth]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pvmT_apply, norm_smul, mul_pow, norm_pvm_sq P ψ (f.measurableSet_fiber c)]

/-- The same sum is the integral of `‖f‖²`. -/
theorem sum_sq_eq_integral (f : SimpleFunc X ℂ) :
    ∑ c ∈ f.range, ‖c‖ ^ 2 * (pvmMeasure P ψ (f ⁻¹' {c})).toReal
      = ∫ x, ‖f x‖ ^ 2 ∂(pvmMeasure P ψ) := by
  classical
  set μ := pvmMeasure P ψ
  have hmap : (SimpleFunc.map (fun c : ℂ => ‖c‖ ^ 2) f).integral μ
      = ∑ c ∈ f.range, μ.real (f ⁻¹' {c}) • ‖c‖ ^ 2 :=
    SimpleFunc.map_integral f _ (SimpleFunc.integrable_of_isFiniteMeasure f) (by simp)
  have hint : (SimpleFunc.map (fun c : ℂ => ‖c‖ ^ 2) f).integral μ
      = ∫ x, ‖f x‖ ^ 2 ∂μ :=
    SimpleFunc.integral_eq_integral _
      (SimpleFunc.integrable_of_isFiniteMeasure (SimpleFunc.map (fun c : ℂ => ‖c‖ ^ 2) f))
  rw [← hint, hmap]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul, measureReal_def]
  ring

/-- The value of the intertwiner on an `L²` simple function. -/
noncomputable def swSimple (F : Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) : H :=
  SimpleFunc.setToSimpleFunc (pvmT P ψ) (Lp.simpleFunc.toSimpleFunc F)

theorem swSimple_add (F G : Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) :
    swSimple P ψ (F + G) = swSimple P ψ F + swSimple P ψ G := by
  have hae : ⇑(Lp.simpleFunc.toSimpleFunc (F + G)) =ᵐ[pvmMeasure P ψ]
      ⇑(Lp.simpleFunc.toSimpleFunc F + Lp.simpleFunc.toSimpleFunc G) := by
    simpa using Lp.simpleFunc.add_toSimpleFunc F G
  have hcongr := SimpleFunc.setToSimpleFunc_congr (μ := pvmMeasure P ψ) (pvmT P ψ)
    (pvmT_zero_of_measure_zero P ψ) (pvmT_finMeasAdditive P ψ)
    (SimpleFunc.integrable_of_isFiniteMeasure (Lp.simpleFunc.toSimpleFunc (F + G))) hae
  rw [swSimple, hcongr, SimpleFunc.setToSimpleFunc_add (pvmT P ψ) (pvmT_finMeasAdditive P ψ)
    (SimpleFunc.integrable_of_isFiniteMeasure _) (SimpleFunc.integrable_of_isFiniteMeasure _)]
  rfl

theorem swSimple_smul (c : ℂ) (F : Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) :
    swSimple P ψ (c • F) = c • swSimple P ψ F := by
  have hae : ⇑(Lp.simpleFunc.toSimpleFunc (c • F)) =ᵐ[pvmMeasure P ψ]
      ⇑(c • Lp.simpleFunc.toSimpleFunc F) := by
    simpa using Lp.simpleFunc.smul_toSimpleFunc c F
  have hcongr := SimpleFunc.setToSimpleFunc_congr (μ := pvmMeasure P ψ) (pvmT P ψ)
    (pvmT_zero_of_measure_zero P ψ) (pvmT_finMeasAdditive P ψ)
    (SimpleFunc.integrable_of_isFiniteMeasure (Lp.simpleFunc.toSimpleFunc (c • F))) hae
  rw [swSimple, hcongr, SimpleFunc.setToSimpleFunc_smul (pvmT P ψ) (pvmT_finMeasAdditive P ψ)
    (pvmT_smul P ψ) c (SimpleFunc.integrable_of_isFiniteMeasure _)]
  rfl

theorem swSimple_norm (F : Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) :
    ‖swSimple P ψ F‖ = ‖(F : Lp ℂ 2 (pvmMeasure P ψ))‖ := by
  have h1 : ‖swSimple P ψ F‖ ^ 2
      = ∫ x, ‖(Lp.simpleFunc.toSimpleFunc F) x‖ ^ 2 ∂(pvmMeasure P ψ) := by
    rw [swSimple, norm_setToSimpleFunc_sq P ψ (Lp.simpleFunc.toSimpleFunc F),
      sum_sq_eq_integral P ψ (Lp.simpleFunc.toSimpleFunc F)]
  have h2 : ∫ x, ‖(Lp.simpleFunc.toSimpleFunc F) x‖ ^ 2 ∂(pvmMeasure P ψ)
      = ∫ x, ‖((F : Lp ℂ 2 (pvmMeasure P ψ)) : X → ℂ) x‖ ^ 2 ∂(pvmMeasure P ψ) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun F] with x hx
    rw [hx]
  have h3 : ‖swSimple P ψ F‖ ^ 2 = ‖(F : Lp ℂ 2 (pvmMeasure P ψ))‖ ^ 2 := by
    rw [h1, h2, ← lp2_norm_sq_eq_integral (pvmMeasure P ψ) (F : Lp ℂ 2 (pvmMeasure P ψ))]
  have hnn1 : (0:ℝ) ≤ ‖swSimple P ψ F‖ := norm_nonneg _
  have hnn2 : (0:ℝ) ≤ ‖(F : Lp ℂ 2 (pvmMeasure P ψ))‖ := norm_nonneg _
  calc ‖swSimple P ψ F‖ = Real.sqrt (‖swSimple P ψ F‖ ^ 2) := (Real.sqrt_sq hnn1).symm
    _ = Real.sqrt (‖(F : Lp ℂ 2 (pvmMeasure P ψ))‖ ^ 2) := by rw [h3]
    _ = ‖(F : Lp ℂ 2 (pvmMeasure P ψ))‖ := Real.sqrt_sq hnn2

/-- The intertwiner on simple functions, as a `ℂ`-linear map. -/
noncomputable def swLin :
    (Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) →ₗ[ℂ] H where
  toFun := swSimple P ψ
  map_add' := swSimple_add P ψ
  map_smul' := swSimple_smul P ψ

@[simp] theorem swLin_apply (F : Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) :
    swLin P ψ F = swSimple P ψ F := rfl

/-- The value of the intertwiner on the indicator of a measurable set. -/
theorem swSimple_indicatorConst {E : Set X} (hE : MeasurableSet E) :
    swSimple P ψ (Lp.simpleFunc.indicatorConst 2 hE
        (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ)) = P.p E ψ := by
  have hcongr := SimpleFunc.setToSimpleFunc_congr (μ := pvmMeasure P ψ) (pvmT P ψ)
    (pvmT_zero_of_measure_zero P ψ) (pvmT_finMeasAdditive P ψ)
    (SimpleFunc.integrable_of_isFiniteMeasure
      (Lp.simpleFunc.toSimpleFunc (Lp.simpleFunc.indicatorConst 2 hE
        (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ))))
    (Lp.simpleFunc.toSimpleFunc_indicatorConst hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ))
  rw [swSimple, hcongr,
    SimpleFunc.setToSimpleFunc_indicator (pvmT P ψ) (pvmT_empty P ψ) hE (1 : ℂ)]
  simp

/-! ## The unitary -/

variable [CompleteSpace H]

theorem denseRange_coeToLp :
    DenseRange ((Lp.simpleFunc.coeToLp X ℂ ℂ :
      (Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) →L[ℂ] Lp ℂ 2 (pvmMeasure P ψ)).toLinearMap) :=
  Lp.simpleFunc.denseRange (by simp)

/-- The intertwiner `W : L²(X, μ) → H`, the continuous extension of `1_E ↦ P(E) ψ`. -/
noncomputable def swCLM : Lp ℂ 2 (pvmMeasure P ψ) →L[ℂ] H :=
  (swLin P ψ).extendOfNorm
    (Lp.simpleFunc.coeToLp X ℂ ℂ :
      (Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) →L[ℂ] Lp ℂ 2 (pvmMeasure P ψ)).toLinearMap

theorem swCLM_simple (F : Lp.simpleFunc ℂ 2 (pvmMeasure P ψ)) :
    swCLM P ψ (F : Lp ℂ 2 (pvmMeasure P ψ)) = swSimple P ψ F :=
  LinearMap.extendOfNorm_eq (denseRange_coeToLp P ψ)
    ⟨1, fun F => by rw [one_mul]; exact le_of_eq (swSimple_norm P ψ F)⟩ F

theorem swCLM_norm (v : Lp ℂ 2 (pvmMeasure P ψ)) : ‖swCLM P ψ v‖ = ‖v‖ := by
  refine (denseRange_coeToLp P ψ).induction (P := fun v => ‖swCLM P ψ v‖ = ‖v‖) ?_ ?_ v
  · rintro _ ⟨F, rfl⟩
    show ‖swCLM P ψ (F : Lp ℂ 2 (pvmMeasure P ψ))‖ = ‖(F : Lp ℂ 2 (pvmMeasure P ψ))‖
    rw [swCLM_simple P ψ F]
    exact swSimple_norm P ψ F
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem swCLM_indicator {E : Set X} (hE : MeasurableSet E) :
    swCLM P ψ (indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ))
      = P.p E ψ := by
  have h := swCLM_simple P ψ (Lp.simpleFunc.indicatorConst 2 hE
    (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ))
  rw [Lp.simpleFunc.coe_indicatorConst] at h
  rw [h, swSimple_indicatorConst P ψ hE]

/-- The intertwiner as a linear isometry. -/
noncomputable def swIsom : Lp ℂ 2 (pvmMeasure P ψ) →ₗᵢ[ℂ] H :=
  ⟨(swCLM P ψ).toLinearMap, swCLM_norm P ψ⟩

theorem swIsom_surjective (hcyc : IsCyclic P ψ) : Function.Surjective (swIsom P ψ) := by
  have hrange_closed : IsClosed (Set.range (swIsom P ψ)) :=
    (swIsom P ψ).isometry.isClosedEmbedding.isClosed_range
  have hle : (Submodule.span ℂ (pvmOrbit P ψ))
      ≤ LinearMap.range (swCLM P ψ).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨E, hE, rfl⟩
    exact ⟨indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ),
      swCLM_indicator P ψ hE⟩
  have hsub : ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H)
      ⊆ Set.range (swIsom P ψ) := fun v hv => hle hv
  intro v
  have hv : v ∈ closure ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H) := by
    rw [hcyc.closure_eq]; trivial
  have : v ∈ Set.range (swIsom P ψ) := (closure_minimal hsub hrange_closed) hv
  exact this

/-- The unitary `W : L²(X, μ) ≃ H`. -/
noncomputable def swEquiv (hcyc : IsCyclic P ψ) : Lp ℂ 2 (pvmMeasure P ψ) ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (swIsom P ψ) (swIsom_surjective P ψ hcyc)

@[simp] theorem swEquiv_apply (hcyc : IsCyclic P ψ) (v : Lp ℂ 2 (pvmMeasure P ψ)) :
    swEquiv P ψ hcyc v = swCLM P ψ v := rfl

/-! ## The intertwining of the projections -/

omit [CompleteSpace H] in
theorem proj_indicatorConstLp {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    proj (pvmMeasure P ψ) hE
        (indicatorConstLp 2 hF (measure_ne_top (pvmMeasure P ψ) F) (1 : ℂ))
      = indicatorConstLp 2 (hE.inter hF) (measure_ne_top (pvmMeasure P ψ) (E ∩ F)) (1 : ℂ) := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn (pvmMeasure P ψ) hE
      (indicatorConstLp 2 hF (measure_ne_top (pvmMeasure P ψ) F) (1 : ℂ)),
    indicatorConstLp_coeFn (μ := pvmMeasure P ψ) (p := 2) (s := F)
      (hs := hF) (hμs := measure_ne_top (pvmMeasure P ψ) F) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (μ := pvmMeasure P ψ) (p := 2) (s := E ∩ F)
      (hs := hE.inter hF) (hμs := measure_ne_top (pvmMeasure P ψ) (E ∩ F)) (c := (1 : ℂ))]
    with x e1 e2 e3
  rw [e1, e3]
  by_cases hx : x ∈ E <;> by_cases hy : x ∈ F <;>
    simp [Set.indicator_apply, e2, hx, hy]

theorem swCLM_proj {E : Set X} (hE : MeasurableSet E) (f : Lp ℂ 2 (pvmMeasure P ψ)) :
    swCLM P ψ (proj (pvmMeasure P ψ) hE f) = P.p E (swCLM P ψ f) := by
  refine Lp.induction (p := 2) (by simp)
    (fun f => swCLM P ψ (proj (pvmMeasure P ψ) hE f) = P.p E (swCLM P ψ f)) ?_ ?_ ?_ f
  · intro c F hF hμF
    rw [Lp.simpleFunc.coe_indicatorConst]
    have hcsmul : indicatorConstLp 2 hF hμF.ne c
        = c • indicatorConstLp 2 hF (measure_ne_top (pvmMeasure P ψ) F) (1 : ℂ) := by
      refine Lp.ext ?_
      filter_upwards [indicatorConstLp_coeFn (μ := pvmMeasure P ψ) (p := 2) (s := F)
          (hs := hF) (hμs := hμF.ne) (c := c),
        Lp.coeFn_smul c (indicatorConstLp 2 hF (measure_ne_top (pvmMeasure P ψ) F) (1 : ℂ)),
        indicatorConstLp_coeFn (μ := pvmMeasure P ψ) (p := 2) (s := F)
          (hs := hF) (hμs := measure_ne_top (pvmMeasure P ψ) F) (c := (1 : ℂ))] with x e1 e2 e3
      simp only [Pi.smul_apply] at e2
      rw [e1, e2, e3]
      by_cases hx : x ∈ F <;> simp [hx]
    rw [hcsmul, proj_smul, map_smul, map_smul, proj_indicatorConstLp P ψ hE hF,
      swCLM_indicator P ψ (hE.inter hF), swCLM_indicator P ψ hF, map_smul, P.inter hE hF]
  · intro g h hg hh _ hPg hPh
    rw [proj_add, map_add, map_add, hPg, hPh, map_add]
  · exact isClosed_eq
      ((swCLM P ψ).continuous.comp (projL (pvmMeasure P ψ) hE).continuous)
      ((P.p E).continuous.comp (swCLM P ψ).continuous)

/-! ## The headline -/

/-- **The spectral theorem for a cyclic projection-valued measure.**  For a cyclic vector
`ψ` of a projection-valued measure `P` on `X`, the Hilbert space is unitarily `L²(X, μ)`
with `μ = ‖P(·)ψ‖²`, by a unitary sending the indicator of `E` to `P(E) ψ` and intertwining
multiplication by indicators with the projections of `P`. -/
theorem pvm_cyclic_unitary (P : Pvm X H) (ψ : H) (hcyc : IsCyclic P ψ) :
    ∃ W : Lp ℂ 2 (pvmMeasure P ψ) ≃ₗᵢ[ℂ] H,
      (∀ (E : Set X) (hE : MeasurableSet E),
          W (indicatorConstLp 2 hE (measure_ne_top (pvmMeasure P ψ) E) (1 : ℂ)) = P.p E ψ) ∧
      (∀ (E : Set X) (hE : MeasurableSet E) (f : Lp ℂ 2 (pvmMeasure P ψ)),
          W (proj (pvmMeasure P ψ) hE f) = P.p E (W f)) :=
  ⟨swEquiv P ψ hcyc, fun _ hE => swCLM_indicator P ψ hE,
    fun _ hE f => swCLM_proj P ψ hE f⟩

end BookProof.ChapterPvmCyclicUnitary


