-- Prove2me | Definitions.Def_Malliavin_TimewiseCondExp
-- name    : Malliavin_TimewiseCondExp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:38:18.380188+00:00
-- url     : https://prove2.me/theorems/e2642109-ae20-4650-bed6-a934b5e188d8
-- title:
--   Timewise Cond Exp
-- statement:
--   Definitions and structural lemmas for Timewise Cond Exp, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimewiseCondExp.lean

import Definitions.Def_Malliavin_NaturalItoDuality
import Mathlib.Probability.Kernel.Condexp
import Theorems.Thm_Malliavin_integral_predictableProjection_Ioc
import Theorems.Thm_Malliavin_integral_set_eq_zero_of_rectangles
import Theorems.Thm_Malliavin_memLp_timeSection_ae

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
noncomputable def timewiseCondExpKernelRepresentative
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) :
    ℝ≥0 × W → ℝ :=
  fun z ↦ ∫ w', U (z.1, w') ∂condExpKernel P (𝓕 z.1) z.2
omit [CompleteSpace W] [BorelSpace W] in
lemma setIntegral_timewiseCondExp_Ioc
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (V : PredictableProcessL2 𝓕 P)
    (hV : ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      (fun w ↦ (V : ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
        P[(fun w ↦ U (t, w)) | 𝓕 t])
    (a b : ℝ≥0) {A : Set W} (hA : MeasurableSet[𝓕 a] A) :
    ∫ t in Set.Ioc a b, ∫ w in A,
        (V : ℝ≥0 × W → ℝ) (t, w) ∂P ∂nonnegativeLebesgueMeasure =
      ∫ t in Set.Ioc a b, ∫ w in A,
        U (t, w) ∂P ∂nonnegativeLebesgueMeasure := by
  have hsec := memLp_timeSection_ae U
  apply integral_congr_ae
  filter_upwards [ae_restrict_le hV, ae_restrict_le hsec,
    ae_restrict_mem measurableSet_Ioc] with t hVt hUt ht
  have hUint : Integrable (fun w ↦ U (t, w)) P :=
    hUt.integrable one_le_two
  calc
    ∫ w in A, (V : ℝ≥0 × W → ℝ) (t, w) ∂P =
        ∫ w in A, P[(fun w ↦ U (t, w)) | 𝓕 t] w ∂P :=
      integral_congr_ae (ae_restrict_le hVt)
    _ = ∫ w in A, U (t, w) ∂P :=
      setIntegral_condExp (𝓕.le t) hUint (𝓕.mono ht.1.le A hA)
omit [CompleteSpace W] [BorelSpace W] in
/-- A predictable product-`L²` version of the fixed-time conditional expectations is
necessarily the product-space predictable projection. -/
theorem predictableProjection_eq_of_ae_timewiseCondExp
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (V : PredictableProcessL2 𝓕 P)
    (hV : ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      (fun w ↦ (V : ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
        P[(fun w ↦ U (t, w)) | 𝓕 t]) :
    predictableProjection 𝓕 U = V := by
  let Q := predictableProjection 𝓕 U
  let g : PredictableProcessL2 𝓕 P := Q - V
  have hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0 := by
    intro R hR
    rcases hR with ⟨F₀, _hF₀, rfl⟩ | ⟨a, b, A, _hab, hA, rfl⟩
    · apply setIntegral_measure_zero
      rw [Measure.prod_prod, measure_singleton, zero_mul]
    · have hμrect : (nonnegativeLebesgueMeasure.prod P)
          (Set.Ioc a b ×ˢ A) ≠ ∞ := by
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top
          (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (measure_ne_top P A)
      have hQint : IntegrableOn
          (Q : ℝ≥0 × W → ℝ) (Set.Ioc a b ×ˢ A)
          (nonnegativeLebesgueMeasure.prod P) :=
        integrableOn_Lp_of_measure_ne_top (Q : TimeProcessL2 P)
          one_le_two hμrect
      have hVint : IntegrableOn
          (V : ℝ≥0 × W → ℝ) (Set.Ioc a b ×ˢ A)
          (nonnegativeLebesgueMeasure.prod P) :=
        integrableOn_Lp_of_measure_ne_top (V : TimeProcessL2 P)
          one_le_two hμrect
      have hcoe : (g : ℝ≥0 × W → ℝ) =ᵐ[
          nonnegativeLebesgueMeasure.prod P]
          fun z ↦ (Q : ℝ≥0 × W → ℝ) z -
            (V : ℝ≥0 × W → ℝ) z := by
        have hgLp : (g : TimeProcessL2 P) =
            (Q : TimeProcessL2 P) - (V : TimeProcessL2 P) := rfl
        rw [hgLp]
        exact Lp.coeFn_sub (Q : TimeProcessL2 P) (V : TimeProcessL2 P)
      calc
        ∫ z in Set.Ioc a b ×ˢ A, (g : ℝ≥0 × W → ℝ) z
            ∂nonnegativeLebesgueMeasure.prod P =
            ∫ z in Set.Ioc a b ×ˢ A,
              ((Q : ℝ≥0 × W → ℝ) z -
                (V : ℝ≥0 × W → ℝ) z)
              ∂nonnegativeLebesgueMeasure.prod P :=
          integral_congr_ae (ae_restrict_le hcoe)
        _ = (∫ z in Set.Ioc a b ×ˢ A,
              (Q : ℝ≥0 × W → ℝ) z
              ∂nonnegativeLebesgueMeasure.prod P) -
            ∫ z in Set.Ioc a b ×ˢ A,
              (V : ℝ≥0 × W → ℝ) z
              ∂nonnegativeLebesgueMeasure.prod P :=
          integral_sub' hQint hVint
        _ = 0 := by
          rw [setIntegral_prod _ hQint, setIntegral_prod _ hVint,
            integral_predictableProjection_Ioc 𝓕 U a b hA,
            setIntegral_timewiseCondExp_Ioc 𝓕 U V hV a b hA,
            sub_self]
  have hg0 : (g : ℝ≥0 × W → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P] 0 := by
    apply lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
      (predictable_le_prod 𝓕) g (by norm_num) (by norm_num)
    · intro s _hs hμs
      exact integrableOn_Lp_of_measure_ne_top
        (g : TimeProcessL2 P) one_le_two hμs.ne
    · intro s hs hμs
      exact integral_set_eq_zero_of_rectangles 𝓕 g hrect s hs hμs
  have hg : g = 0 := by
    apply Subtype.ext
    apply Lp.ext
    exact hg0.trans (Lp.coeFn_zero ℝ 2
      (nonnegativeLebesgueMeasure.prod P)).symm
  exact sub_eq_zero.mp hg
theorem predictableProjection_eq_of_ae_timewiseCondExpKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (V : PredictableProcessL2 𝓕 P)
    (hV : ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      (fun w ↦ (V : ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
        fun w ↦ ∫ w', U (t, w') ∂condExpKernel P (𝓕 t) w) :
    predictableProjection 𝓕 U = V := by
  apply predictableProjection_eq_of_ae_timewiseCondExp 𝓕 U V
  filter_upwards [hV, memLp_timeSection_ae U] with t hVt hUt
  have hUint : Integrable (fun w ↦ U (t, w)) P :=
    hUt.integrable one_le_two
  exact hVt.trans
    (condExp_ae_eq_integral_condExpKernel (𝓕.le t) hUint).symm
section NaturalClarkOcone
variable {B : ℝ≥0 → W → ℝ}
theorem bestNaturalItoIntegrand_eq_predictableProjection_of_ae_timewiseCondExpKernel
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (F : D12 P)
    (hTimewise : ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      (fun w ↦
        (bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) :
          ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
        fun w ↦ ∫ w',
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F) : ℝ≥0 × W → ℝ) (t, w')
          ∂condExpKernel P (𝓅 t) w) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F)) :=
  (predictableProjection_eq_of_ae_timewiseCondExpKernel 𝓅
    (Malliavin.timeDerivative hB coordinate coordinate_apply generated
      (mderivD12 P F))
    (bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1)) hTimewise).symm
noncomputable def ClarkOconeFamily.ofNaturalItoTimewiseCondExpKernel
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (hTimewise : ∀ F : D12 P,
      ∀ᵐ t ∂nonnegativeLebesgueMeasure,
        (fun w ↦
          (bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) :
            ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
          fun w ↦ ∫ w',
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              (mderivD12 P F) : ℝ≥0 × W → ℝ) (t, w')
            ∂condExpKernel P (𝓅 t) w) :
    ClarkOconeFamily B P 𝓅 :=
  ClarkOconeFamily.ofNaturalItoBestIntegrand hB coordinate coordinate_apply
    generated hsm hnat hMRT fun F ↦
      bestNaturalItoIntegrand_eq_predictableProjection_of_ae_timewiseCondExpKernel
        hB coordinate coordinate_apply generated hsm hnat F (hTimewise F)
end NaturalClarkOcone
end Malliavin


