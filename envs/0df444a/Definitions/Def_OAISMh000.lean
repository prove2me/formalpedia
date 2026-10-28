-- Prove2me | Definitions.Def_OAISMh000
-- name    : OAISMh000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:38:54.989987+00:00
-- url     : https://prove2.me/theorems/d3124ad3-59f0-4a1d-8214-573e183cfca8
-- title:
--   Definitions bundle OAISMh000 of the split of OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler`, carved from OpenAI's openai/math development (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 380 declarations of OpenAI's Lean: 287 definitions, 3 inductive types or structures, 4 instances and 86 theorems. The definitions and types are `OAI.CompactIntegral.tube`, `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.HasRawFDerivAt`, `OAI.Mahler.Horizontal`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.RealComplexTwoJet`, `OAI.Mahler.WedgePowerSlots`, `OAI.Mahler.actualRealComplexJet`, `OAI.Mahler.alphaPath`, `OAI.Mahler.ambientFinEquiv`, `OAI.Mahler.basisContinuousWedge`, `OAI.Mahler.basisContinuousWedgePower`, `OAI.Mahler.basisVolumeContinuous`, `OAI.Mahler.betaLinear`, `OAI.Mahler.boundaryFinEquiv`, `OAI.Mahler.boundaryForm`, `OAI.Mahler.boundaryFormFin`, `OAI.Mahler.boundaryJet`, `OAI.Mahler.boundaryResidualFin`, `OAI.Mahler.boundarySingleResidualFin`, `OAI.Mahler.bundleFiniteForm`, `OAI.Mahler.circleTangent`, `OAI.Mahler.complexCoord`, `OAI.Mahler.complexHessian`, `OAI.Mahler.complexStructure`, `OAI.Mahler.complexifyDerivative`, `OAI.Mahler.complexifySecondDerivative`, `OAI.Mahler.continuousCovectorVolume`, `OAI.Mahler.continuousReindex`, `OAI.Mahler.continuousSourceBoundaryForm`, `OAI.Mahler.continuousWedge`, `OAI.Mahler.continuousWedgeCLM`, `OAI.Mahler.continuousWedgeFin`, `OAI.Mahler.continuousWedgePower`, `OAI.Mahler.coordinateCast`, `OAI.Mahler.coordinateDirection`, `OAI.Mahler.coordinateMap`, `OAI.Mahler.coordinatePair`, `OAI.Mahler.covectorVolume`, `OAI.Mahler.dbar` and 250 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Mahler, in whole or in part: `Mahler_ActualFiniteStrips`, `Mahler_ActualVerticalPrimitive`, `Mahler_AngularFibers`, `Mahler_AngularGeometry`, `Mahler_BasisContinuousWedge`, `Mahler_BoundaryJet`, `Mahler_ChartExtension`, `Mahler_ChartStokes`, `Mahler_ClosedWedgePowers`, `Mahler_CompactIntegral`, `Mahler_ComplexCoordinates`, `Mahler_ComplexStripMap`, `Mahler_ComplexVolume`, `Mahler_ConformalInverse`, `Mahler_ConformalSeries`, `Mahler_ContinuousWedge`, `Mahler_ConvexGeometry`, `Mahler_ConvexSequence`, `Mahler_CoordinateAnnulus`, `Mahler_CoordinateBall`, `Mahler_CoordinateEuclidean`, `Mahler_CovectorVolume`, `Mahler_DCForms`, `Mahler_DilationTransport`, `Mahler_ErrorBound`, `Mahler_EuclideanRegularLevels`, `Mahler_EuclideanSpecialMap`, `Mahler_ExactFormCoordinates`, `Mahler_ExteriorAlternatization`, `Mahler_ExteriorCoordinates`, `Mahler_ExteriorFlux`, `Mahler_ExteriorLeibnizTwo`, `Mahler_ExteriorPower`, `Mahler_FiberHeight`, `Mahler_FiberPrimitive`, `Mahler_FiniteStripReduction`, `Mahler_FiniteStrips`, `Mahler_FormStokes`, `Mahler_GlobalVerticalGeometry`, `Mahler_HalfspaceStokes`, `Mahler_HemisphereArea`, `Mahler_HemisphereChart`, `Mahler_HemisphereJacobian`, `Mahler_HemisphereMeasure`, `Mahler_Hessian`, `Mahler_HolomorphicLogC2`, `Mahler_HomogeneousDeformation`, `Mahler_HomogeneousDensityVariation`, `Mahler_HomogeneousFlux`, `Mahler_HomogeneousPrimitiveRegularity`, `Mahler_HomogeneousSphereIntegral`, `Mahler_HomogeneousTransgression`, `Mahler_HomogeneousVariationCoefficient`, `Mahler_HorizontalForms`, `Mahler_InverseRadialRegularity`, `Mahler_Jacobian`, `Mahler_LevelFace`, `Mahler_LogDilation`, `Mahler_LogJet`, `Mahler_LogNormSquare`, `Mahler_LogScalarJet`, `Mahler_MassLimit`, `Mahler_MassTarget`, `Mahler_MatrixExteriorPower`, `Mahler_MatrixHessian`, `Mahler_NormExteriorPower`, `Mahler_NormSquareForm`, `Mahler_NormSquareJet`, `Mahler_OpenExteriorNormalization`, `Mahler_OrientedChartIntegral`, `Mahler_OrientedSphereDensity`, `Mahler_PairTransgression`, `Mahler_PlanarDensity`, `Mahler_PlanarEstimates`, `Mahler_PlanarIntegralRegularity`, `Mahler_Positivity`, `Mahler_PowerTransgression`, `Mahler_PrimitiveBound`, `Mahler_PrimitiveRegularity`, `Mahler_PunctureCutoff`, `Mahler_RadialBridge`, `Mahler_RadialPrimitiveDeriv`, `Mahler_RawAlternationDerivative`, `Mahler_RawClosedPower`, `Mahler_RawClosedProduct`, `Mahler_RawCoefficientDerivative`, `Mahler_RawExteriorPower`, `Mahler_RawReindexedDerivative`, `Mahler_RealLogBridge`, `Mahler_ReferencePole`, `Mahler_ReferencePoleFrame`, `Mahler_RegularBoundaryAtlas`, `Mahler_RegularChartStokes`, `Mahler_RegularLevelCharts`, `Mahler_RegularMassReduction`, `Mahler_RegularPartition`, `Mahler_RegularSublevel`, `Mahler_RescaledHolomorphic`, `Mahler_RescaledMassMap`, `Mahler_ShellRegularity`, `Mahler_SourceCoordinateForms`, `Mahler_SourceFluxCoordinates`, `Mahler_SourceFluxRegularity`, `Mahler_SourceFullExterior`, `Mahler_SourceHomogeneous`, `Mahler_SourceLevelFlux`, `Mahler_SourceLogC2`, `Mahler_SourceRawCoefficient`, `Mahler_SourceRawJets`, `Mahler_SourceRawOrientation`, `Mahler_SourceSphereLimit`, `Mahler_SourceTopCoordinates`, `Mahler_SpecialJacobian`, `Mahler_SpecialLeadingTerm`, `Mahler_SpecialMassBridge`, `Mahler_SpecialMassHypotheses`, `Mahler_SphereAreaTransport`, `Mahler_SphereCoordinateIntegral`, `Mahler_SphereDensityBridge`, `Mahler_SphereFlux`, `Mahler_SphereFluxIntegral`, `Mahler_SphereFluxLimit`, `Mahler_SphereForms`, `Mahler_SphereNormalization`, `Mahler_SphereOrientation`, `Mahler_SphereTransport`, `Mahler_StripDifferential`, `Mahler_StripMassExhaustion`, `Mahler_StripRankGeometry`, `Mahler_StripRegularValues`, `Mahler_StripVolume`, `Mahler_UniformError`, `Mahler_VerticalRadius`, `Mahler_VerticalSpeed`, `Mahler_WedgeAlgebra`, `Mahler_WedgeCalculus`, `Mahler_WedgeDecomposition`, `Mahler_WedgeOne`, `Mahler_WedgeTwoDifferentialAlgebra`.
--
--   **Imports.** It imports the published bundle `Def_MahlerConjecture`.
--
--   **Imported by** (directly, in this split): the statements `OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression`, `OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression`, `OAI.Mahler.MassHypotheses.homogeneousSphereFlux_value`, `OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints`, `OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit`, `OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit`, `OAI.Mahler.source_punctured_scaled_extDeriv`, `OAI.Mahler.source_regular_massBelow_of_flux_limit`, `OAI.SymmetricMahler.stripMap_volume_le_product` and `OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass`; the proofs of `OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression`, `OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression`, `OAI.Mahler.MassHypotheses.homogeneousSphereFlux_value`, `OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints`, `OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit`, `OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit`, `OAI.Mahler.source_punctured_scaled_extDeriv`, `OAI.Mahler.source_regular_massBelow_of_flux_limit`, `OAI.SymmetricMahler.stripMap_volume_le_product`, `OAI.SymmetricMahler.symmetric_mahler` and `OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass`.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Mahler at commit adc7f12

import Mathlib
import Definitions.Def_MahlerConjecture

section
-- module Solutions.OAIS_Mahler.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiniteStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional algebra for the finite-strip construction.
The image estimate and algebraic injectivity step do not require
the analytic mass inequality. -/

namespace SymmetricMahler

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Apply the real matrix whose rows encode the strip constraints. -/
def measurement (A : J → I → ℝ) (v : I → ℝ) (j : J) : ℝ := ∑ i, A j i * v i

/-- Apply the transpose of the strip matrix to a vector of coefficients. -/
def push (A : J → I → ℝ) (p : J → ℝ) (i : I) : ℝ := ∑ j, A j i * p j

def stripBody (A : J → I → ℝ) : Set (I → ℝ) :=
  {v | ∀ j, |measurement A v j| ≤ 1}

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConformalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal series and its logarithmic derivative. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

def term (p k : ℕ) (w : ℂ) : ℂ := w ^ (2*k+1) / ((2*k+1 : ℕ) : ℂ)^p
def series (p : ℕ) (w : ℂ) : ℂ := ∑' k, term p k w
def F (w : ℂ) : ℂ := (8 / (Real.pi : ℂ)^2) * series 2 w
def H (w : ℂ) : ℂ := series 1 w

lemma odd_cast_ne (k : ℕ) : ((2*k+1 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (show 2*k+1 ≠ 0 by omega)

lemma series_zero (p : ℕ) : series p 0 = 0 := by
  simp [series, term]

lemma term_deriv_one (k : ℕ) (w : ℂ) :
    HasDerivAt (term 1 k) (w^(2*k)) w := by
  have hd := (hasDerivAt_pow (2*k+1) w).div_const (((2*k+1 : ℕ) : ℂ)^1)
  change HasDerivAt (term 1 k) _ w at hd
  convert hd using 1
  simp only [Nat.add_sub_cancel, pow_one]
  field_simp [odd_cast_ne k]
  exact (mul_div_cancel_right₀ _ (odd_cast_ne k)).symm

lemma term_deriv_two (k : ℕ) (w : ℂ) :
    HasDerivAt (term 2 k) (w^(2*k) / ((2*k+1 : ℕ) : ℂ)) w := by
  have hd := (hasDerivAt_pow (2*k+1) w).div_const (((2*k+1 : ℕ) : ℂ)^2)
  change HasDerivAt (term 2 k) _ w at hd
  convert hd using 1
  simp only [Nat.add_sub_cancel]
  field_simp [odd_cast_ne k]

lemma derivative_bound (k : ℕ) {w : ℂ} {r : ℝ} (_hr : 0 ≤ r) (hw : ‖w‖ < r) :
    ‖w^(2*k) / ((2*k+1 : ℕ) : ℂ)‖ ≤ r^(2*k) := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  exact (div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ 2*k+1 by omega))).trans
    (pow_le_pow_left₀ (norm_nonneg _) hw.le _)

theorem hasDerivAt_series_two {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (series 2) (∑' k : ℕ, w^(2*k) / ((2*k+1 : ℕ) : ℂ)) w := by
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hu : Summable (fun k : ℕ => r^(2*k)) := by
    exact (summable_geometric_of_lt_one hr0.le hr).comp_injective
      (by intro a b h; omega)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun k z _ => term_deriv_two k z)
    (fun k z hz => derivative_bound k hr0.le (by simpa using hz))
    (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
    (by simp [term]) (by simpa using hwr)

theorem hasDerivAt_H {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt H (1-w^2)⁻¹ w := by
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hu : Summable (fun k : ℕ => r^(2*k)) :=
    (summable_geometric_of_lt_one hr0.le hr).comp_injective (by intro a b h; omega)
  have hd : HasDerivAt H (∑' k : ℕ, w^(2*k)) w :=
    hasDerivAt_tsum_of_isPreconnected hu isOpen_ball
      (convex_ball (0 : ℂ) r).isPreconnected
      (fun k z _ => term_deriv_one k z)
      (fun k z hz => by
        change ‖z^(2*k)‖ ≤ r^(2*k)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (show ‖z‖ ≤ r from (show ‖z‖ < r by simpa using hz).le) _)
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
      (by simp [term]) (by simpa using hwr)
  have hw2 : ‖w^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hs : (∑' k : ℕ, w^(2*k)) = (1-w^2)⁻¹ := by
    simpa only [pow_mul] using tsum_geometric_of_norm_lt_one hw2
  rwa [hs] at hd

lemma one_sub_ne {w : ℂ} (hw : ‖w‖ < 1) : 1-w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hw

lemma one_add_ne {w : ℂ} (hw : ‖w‖ < 1) : 1+w ≠ 0 := by
  simpa using one_sub_ne (w := -w) (by simpa using hw)

lemma one_sub_sq_ne {w : ℂ} (hw : ‖w‖ < 1) : 1-w^2 ≠ 0 := by
  apply one_sub_ne
  rw [norm_pow]
  nlinarith [norm_nonneg w]

def cayley (w : ℂ) : ℂ := (1+w)/(1-w)

/-- The branch-domain assertion for the logarithmic derivative. -/
theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  have hn : w.re*w.re+w.im*w.im < 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  rw [cayley, Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr (one_sub_ne hw))
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.add_im, Complex.sub_im, Complex.one_im]
  nlinarith

lemma hasDerivAt_log_cayley {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (fun z => Complex.log (cayley z)) (2*(1-w^2)⁻¹) w := by
  have hq := ((hasDerivAt_const w (1 : ℂ)).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)) (one_sub_ne hw)
  have hd := (Complex.hasDerivAt_log (Or.inl (cayley_re_pos hw))).comp w hq
  change HasDerivAt (fun z => Complex.log (cayley z)) _ w at hd
  convert hd using 1
  dsimp [cayley]
  field_simp [one_sub_ne hw, one_add_ne hw, one_sub_sq_ne hw]
  ring

/-- Auxiliary logarithm identity, established without assuming a logarithmic series. -/
theorem two_H_eq_log {w : ℂ} (hw : ‖w‖ < 1) :
    2 * H w = Complex.log (cayley w) := by
  have h₁ : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun t => 2*H t) (2*(1-z^2)⁻¹) z := by
    intro z hz
    exact (hasDerivAt_H (by simpa using hz)).const_mul 2
  have h₂ : ∀ z ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun t => Complex.log (cayley t)) (2*(1-z^2)⁻¹) z := by
    intro z hz
    exact hasDerivAt_log_cayley (by simpa using hz)
  exact isOpen_ball.eqOn_of_deriv_eq (convex_ball (0 : ℂ) 1).isPreconnected
    (fun z hz => (h₁ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h₂ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (h₁ z hz).deriv.trans (h₂ z hz).deriv.symm)
    (show (0 : ℂ) ∈ ball 0 1 by simp)
    (by simp [H, series_zero, cayley]) (by simpa using hw)

def D (w : ℂ) : ℂ := ∑' k : ℕ, w^(2*k) / ((2*k+1 : ℕ) : ℂ)

lemma w_mul_D (w : ℂ) : w * D w = H w := by
  unfold D H series term
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [pow_succ]
  ring

/-- Termwise differentiation of the conformal series. -/
theorem hasDerivAt_F_series {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt F ((8/(Real.pi : ℂ)^2) * D w) w :=
  (hasDerivAt_series_two hw).const_mul _

/-- The derivative formula away from zero, with the principal logarithm. -/
theorem hasDerivAt_F_log {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    HasDerivAt F (4/((Real.pi : ℂ)^2*w) * Complex.log ((1+w)/(1-w))) w := by
  have he : (8/(Real.pi : ℂ)^2) * D w =
      4/((Real.pi : ℂ)^2*w) * Complex.log ((1+w)/(1-w)) := by
    rw [show Complex.log ((1+w)/(1-w)) = 2*H w from (two_H_eq_log hw).symm, ← w_mul_D]
    field_simp
    ring
  exact he ▸ hasDerivAt_F_series hw

/-- Oddness of the conformal map. -/
theorem F_odd (w : ℂ) : F (-w) = -F w := by
  have ht : ∀ k, term 2 k (-w) = -term 2 k w := by
    intro k
    simp [term, pow_add, pow_mul, neg_div]
  simp only [F, series, ht, tsum_neg, mul_neg]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular geometry of the conformal series. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

def polar (r θ : ℝ) : ℂ := r * Complex.exp (θ * I)
def Q (r θ : ℝ) : ℝ := (F (polar r θ)).re
def S (r θ : ℝ) : ℝ := (F (polar r θ)).im
def B (r θ : ℝ) : ℝ := 4 / Real.pi^2 * Real.arctan (2*r*Real.sin θ/(1-r^2))

lemma norm_polar {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖polar r θ‖ = r := by
  simp [polar, Complex.norm_exp, abs_of_nonneg hr]

lemma polar_ne_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : polar r θ ≠ 0 := by
  exact norm_pos_iff.mp (by rw [norm_polar hr.le]; exact hr)

lemma polar_im (r θ : ℝ) : (polar r θ).im = r * Real.sin θ := by
  simp [polar]

lemma hasDerivAt_polar_complex (r : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℂ => (r : ℂ) * Complex.exp (t * I))
      (I * ((r : ℂ) * Complex.exp (z * I))) z := by
  simpa only [id_eq, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id z).mul_const I).cexp.const_mul (r : ℂ))

lemma hasDerivAt_Q_arg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    HasDerivAt (Q r) (-(4 / Real.pi^2) * (cayley (polar r θ)).arg) θ := by
  have hw : ‖polar r θ‖ < 1 := by rwa [norm_polar hr.le]
  have hd := ((hasDerivAt_F_log hw (polar_ne_zero hr θ)).comp (θ : ℂ)
    (hasDerivAt_polar_complex r θ)).real_of_complex
  have he : (4 / ((Real.pi : ℂ)^2 * polar r θ) * Complex.log (cayley (polar r θ))) *
      (I * polar r θ) = (4 / (Real.pi : ℂ)^2) * I * Complex.log (cayley (polar r θ)) := by
    field_simp [polar_ne_zero hr θ]
  change HasDerivAt (Q r) _ θ at hd
  change HasDerivAt (Q r) ((4 / ((Real.pi : ℂ)^2 * polar r θ) *
    Complex.log (cayley (polar r θ))) * (I * polar r θ)).re θ at hd
  rw [he] at hd
  simpa [Complex.mul_re, Complex.log_im, ← Complex.ofReal_pow, ← Complex.ofReal_div] using hd

/-- The principal branch gives arctan, rather than an angle modulo pi. -/
lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm

lemma cayley_im_div_re {w : ℂ} (hw : ‖w‖ < 1) :
    (cayley w).im / (cayley w).re = 2*w.im/(1-‖w‖^2) := by
  have hden : Complex.normSq (1-w) ≠ 0 :=
    (Complex.normSq_pos.mpr (one_sub_ne hw)).ne'
  have hs : ‖w‖^2 = w.re^2 + w.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hn : 1-‖w‖^2 ≠ 0 := by nlinarith [norm_nonneg w]
  have hre : (cayley w).re = (1-‖w‖^2)/Complex.normSq (1-w) := by
    simp only [cayley, Complex.div_re, Complex.add_re, Complex.sub_re,
      Complex.one_re, Complex.add_im, Complex.sub_im, Complex.one_im]
    rw [hs]
    ring
  have him : (cayley w).im = 2*w.im/Complex.normSq (1-w) := by
    simp only [cayley, Complex.div_im, Complex.add_re, Complex.sub_re,
      Complex.one_re, Complex.add_im, Complex.sub_im, Complex.one_im]
    ring
  rw [hre, him]
  field_simp

/-- The branch-sensitive angular identity. -/
theorem arg_cayley_polar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (cayley (polar r θ)).arg = Real.arctan (2*r*Real.sin θ/(1-r^2)) := by
  have hw : ‖polar r θ‖ < 1 := by rwa [norm_polar hr.le]
  rw [arg_eq_arctan_of_re_pos (cayley_re_pos hw), cayley_im_div_re hw,
    norm_polar hr.le, polar_im]
  congr 1
  ring

/-- The derivative of the series' real part is minus B. -/
theorem hasDerivAt_Q {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    HasDerivAt (Q r) (-B r θ) θ := by
  simpa only [arg_cayley_polar hr hr1, B, neg_mul] using hasDerivAt_Q_arg hr hr1 θ

theorem B_pos {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) : 0 < B r θ := by
  unfold B
  apply mul_pos (div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
  apply Real.arctan_pos.mpr
  exact div_pos (mul_pos (mul_pos (by norm_num) hr) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ))
    (by nlinarith)

/-- Strict decrease includes the semicircle endpoints, whose derivatives vanish. -/
theorem Q_strictAntiOn {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    StrictAntiOn (Q r) (Icc 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun θ _ => (hasDerivAt_Q hr hr1 θ).continuousAt.continuousWithinAt)
  intro θ hθ
  rw [interior_Icc] at hθ
  rw [(hasDerivAt_Q hr hr1 θ).deriv]
  exact neg_neg_of_pos (B_pos hr hr1 hθ.1 hθ.2)

lemma polar_zero (r : ℝ) : polar r 0 = (r : ℂ) := by simp [polar]

lemma polar_pi (r : ℝ) : polar r Real.pi = -(r : ℂ) := by simp [polar]

theorem Q_zero (r : ℝ) : Q r 0 = (F (r : ℂ)).re := by rw [Q, polar_zero]

theorem Q_pi (r : ℝ) : Q r Real.pi = -(F (r : ℂ)).re := by
  rw [Q, polar_pi, F_odd, Complex.neg_re]

/-- Existence and uniqueness of the angle at a fixed radius.
The endpoint condition is stated with F(r) itself, with no radial theorem assumed. -/
theorem existsUnique_angle {r q : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hq : -(F (r : ℂ)).re < q) (hq' : q < (F (r : ℂ)).re) :
    ∃! θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ Q r θ = q := by
  have hcont : ContinuousOn (Q r) (Icc 0 Real.pi) :=
    fun θ _ => (hasDerivAt_Q hr hr1 θ).continuousAt.continuousWithinAt
  obtain ⟨θ, hθ, he⟩ := intermediate_value_Icc' Real.pi_pos.le hcont
    (show q ∈ Icc (Q r Real.pi) (Q r 0) by simpa [Q_zero, Q_pi] using And.intro hq.le hq'.le)
  have hi : θ ∈ Ioo 0 Real.pi := by
    constructor
    · refine lt_of_le_of_ne hθ.1 ?_
      intro h
      subst θ
      rw [Q_zero] at he
      linarith
    · refine lt_of_le_of_ne hθ.2 ?_
      intro h
      subst θ
      rw [Q_pi] at he
      linarith
  refine ⟨θ, ⟨hi, he⟩, ?_⟩
  intro φ hφ
  exact (Q_strictAntiOn hr hr1).injOn ⟨hφ.1.1.le, hφ.1.2.le⟩ hθ (hφ.2.trans he.symm)

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PlanarEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An elementary uniform reciprocal-arctangent estimate for the
planar construction, with the explicit absolute constant C=2. -/

namespace SymmetricMahler
open Real

/-- The angular-speed expression B as a real scalar function. -/
noncomputable def angularSpeed (r θ : ℝ) : ℝ :=
  (4 / Real.pi^2) * arctan (2 * r * sin θ / (1 - r^2))

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ErrorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real

/-- The radial derivative formula on 0<r<1.
Its removable value at r=0 is not asserted by this definition. -/
noncomputable def radialDerivative (r : ℝ) : ℝ :=
  4 / (Real.pi^2*r) * log ((1+r)/(1-r))

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- The unscaled error integrand. -/
noncomputable def errorIntegrand (M : ℝ → ℝ) (r₀ m r : ℝ) : ℝ :=
  m * r^(2*m-3/2 : ℝ) * sqrt (1-r^2) / sqrt (M r-M r₀)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_UniformError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory Set

noncomputable def radialCutoff (m : ℝ) : ℝ := 1-log m/m

/-- A uniform majorant for the unscaled E_m, independent of r₀. -/
noncomputable def errorEnvelope (m : ℝ) : ℝ :=
  2*m*(radialCutoff m)^(2*m-3/2 : ℝ)/sqrt (4/Real.pi^2) +
    sqrt (2/((2/Real.pi^2)*log m))*(1+4/exp 1)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RadialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex MeasureTheory Set

/-- The actual M(r)=F(r) on the real diameter, taking its real part for a
real-valued function on all of ℝ. The estimates use only 0≤r<1. -/
noncomputable def radialMap (r : ℝ) : ℝ := (MahlerConformal.F (r : ℂ)).re

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_VerticalSpeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology

noncomputable def polarCurve (θ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (r : ℂ)*Complex.exp ((θ r : ℂ)*Complex.I)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_AngularFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

noncomputable def fiberDomain (q : ℝ) : Set ℝ :=
  {r | 0 < r ∧ r < 1 ∧ |q| < radialMap r}

lemma exists_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ∃ θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ MahlerConformal.Q r θ = q := by
  have hq := abs_lt.mp hr.2.2
  exact (MahlerConformal.existsUnique_angle hr.1 hr.2.1 hq.1 hq.2).exists

/-- The unique upper-half-disk angle, extended by zero outside its open radial domain. -/
noncomputable def fiberAngle (q r : ℝ) : ℝ := by
  classical
  exact if hr : r ∈ fiberDomain q then Classical.choose (exists_fiberAngle hr) else 0

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiberHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

noncomputable def fiberHeight (q r : ℝ) : ℝ :=
  MahlerConformal.S r (fiberAngle q r)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PrimitiveBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- The radial form of the vertical primitive, before proving its equality
with the integral in the image domain. -/
noncomputable def radialPrimitiveDensity (θ : ℝ → ℝ) (m r : ℝ) : ℝ :=
  (4*m/Real.pi)*(r^(2*m-1 : ℝ)/angularSpeed r (θ r))

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiberPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- A concrete nonnegative error function, valid also for every smaller m≥2. -/
noncomputable def planarError (m : ℝ) : ℝ := max 0 (Real.pi*errorEnvelope m)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RadialPrimitiveDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

noncomputable def radialPrimitive (q r₀ m r : ℝ) : ℝ :=
  ∫ t in r₀..r, radialPrimitiveDensity (fiberAngle q) m t

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConformalInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The biholomorphic map and its inverse.
The vertical interval property and P_m estimates are not asserted here. -/

noncomputable section
open Complex Set Metric Filter
open scoped Topology
namespace MahlerConformal

def Omega : Set ℂ := F '' ball (0 : ℂ) 1
def inverseF : ℂ → ℂ := Function.invFunOn F (ball (0 : ℂ) 1)

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_VerticalRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical geometry of the actual inverse. The squared inverse radius has
positive vertical derivative on the image of the upper half-disk. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

def verticalRadiusSq (q ξ : ℝ) : ℝ := Complex.normSq (inverseF ((q : ℂ)+ξ*I))

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ActualVerticalPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- The actual inverse radius in a vertical line of Omega. -/
noncomputable def verticalRadius (q t : ℝ) : ℝ :=
  ‖MahlerConformal.inverseF ((q : ℂ)+(t : ℂ)*Complex.I)‖

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PlanarDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The vertical primitive density, written with squared norms
so smoothness at the zero is explicit for integral m. -/
noncomputable def planarDensity (m : ℕ) (u : ℂ) : ℝ :=
  (4*(m : ℝ)/Real.pi)*Complex.normSq (MahlerConformal.inverseF u)^(m-1)*
    Complex.normSq (deriv MahlerConformal.inverseF u)

/-- The original vertical integral, before its equality with the radial integral. -/
noncomputable def planarPrimitive (m : ℕ) (q t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_GlobalVerticalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global vertical intervals of the conformal image. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

/-- Exact vertical section of the previously constructed conformal image. -/
def verticalFiber (q : ℝ) : Set ℝ := {y | (q : ℂ) + (y : ℂ)*I ∈ Omega}

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ActualFiniteStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

noncomputable def stripCoordinate (A : J → I → ℝ) (z : (I → ℝ) × (I → ℝ)) (j : J) : ℂ :=
  (measurement A z.1 j : ℂ)+(measurement A z.2 j : ℂ)*Complex.I

noncomputable def stripDomain (A : J → I → ℝ) : Set ((I → ℝ) × (I → ℝ)) :=
  {z | ∀ j, stripCoordinate A z j ∈ Omega}

noncomputable def stripTau (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) : ℝ :=
  ∑ j, ‖inverseF (stripCoordinate A z j)‖^(2*(m : ℝ) : ℝ)

noncomputable def stripMap (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) :
    (I → ℝ) × (I → ℝ) :=
  (z.1,push A (fun j => planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)))

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_Hessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [normedAddCommGroupE : NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- Wirtinger derivative, defined from the real Frechet derivative. -/
noncomputable def dz (u : E → ℂ) (x v : E) : ℂ :=
  (fderiv ℝ u x v - I * fderiv ℝ u x (I • v)) / 2
/-- Conjugate Wirtinger derivative with the same normalization. -/
noncomputable def dbar (u : E → ℂ) (x v : E) : ℂ :=
  (fderiv ℝ u x v + I * fderiv ℝ u x (I • v)) / 2

variable {ι : Type*} [Fintype ι]
/-- The squared Euclidean norm of a finite holomorphic map. -/
noncomputable def tau (f : ι → E → ℂ) (x : E) : ℝ := ∑ j, normSq (f j x)
noncomputable def energy (f : ι → E → ℂ) (x : E) : ℂ := ∑ j, conj (f j x) * f j x
noncomputable def logTau (f : ι → E → ℂ) (x : E) : ℂ := (Real.log (tau f x) : ℂ)

noncomputable def numerator (f : ι → E → ℂ) (v x : E) : ℂ :=
  ∑ j, conj (f j x) * fderiv ℂ (f j) x v

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_Positivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators ComplexOrder
local notation "conj" => starRingEnd ℂ
namespace Mahler
variable {ι : Type*} [Fintype ι]

noncomputable def pairing (a b : ι → ℂ) : ℂ := ∑ j, conj (a j) * b j
noncomputable def sizeSq (a : ι → ℂ) : ℝ := ∑ j, normSq (a j)
noncomputable def logKernel (a b c : ι → ℂ) : ℂ :=
  ((sizeSq a : ℂ) * pairing b c - pairing a c * pairing b a) / (sizeSq a : ℂ)^2

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MatrixHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Complex Matrix
open scoped BigOperators ComplexOrder

namespace Mahler
variable {ι κ : Type*} [Fintype ι] [fintypeKappa : Fintype κ]

noncomputable def kernelMatrix (a : ι → ℂ) (B : κ → ι → ℂ) : Matrix κ κ ℂ :=
  fun i j => logKernel a (B i) (B j)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
/-- Mixed Hessian in a finite family of directions; the row is the conjugate index. -/
noncomputable def complexHessian (u : E → ℂ) (x : E) (e : κ → E) : Matrix κ κ ℂ :=
  fun i j => dbar (fun y => dz u y (e j)) x (e i)

noncomputable def jacobian (f : ι → E → ℂ) (x : E) (e : κ → E) : Matrix ι κ ℂ :=
  fun j i => fderiv ℂ (f j) x (e i)

/-- Complex Hessian indexing: row k is z_k, column l is bar z_l. -/
noncomputable def sourceHessian (u : E → ℂ) (x : E) (e : κ → E) : Matrix κ κ ℂ :=
  (complexHessian u x e).transpose

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Complex
open scoped BigOperators

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- The convention d^c u(v) = -D_R u(iv)/4. -/
noncomputable def dc (u : E → ℂ) (x v : E) : ℂ := -fderiv ℝ u x (I • v) / 4

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- Multiplication by i as a real continuous linear map. -/
noncomputable def complexStructure : E →L[ℝ] E :=
  (I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] lemma complexStructure_apply (v : E) : complexStructure v = I • v := rfl

/-- The operator d^c, bundled as a real continuous linear one-form. -/
noncomputable def dcLinear (u : E → ℂ) (x : E) : E →L[ℝ] ℂ :=
  (-1 / 4 : ℂ) • (fderiv ℝ u x).comp complexStructure

@[simp] lemma dcLinear_apply (u : E → ℂ) (x v : E) : dcLinear u x v = dc u x v := by
  simp [dcLinear, dc]
  ring

/-- A continuous linear one-form regarded as a continuous alternating one-form. -/
noncomputable def oneForm (a : E → E →L[ℝ] ℂ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ 0 (a x)

omit normedSpaceComplexE isScalarTowerRealComplexE in
@[simp] lemma oneForm_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a : E → E →L[ℝ] ℂ) (x : E) (v : Fin 1 → E) :
    oneForm a x v = a x (v 0) := rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HorizontalForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct
namespace Mahler
open AlternatingMap
variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/-- A form annihilates a vector in every slot. -/
def Horizontal {ι : Type*} (a : T [⋀^ι]→ₗ[ℝ] ℂ) (V : T) : Prop :=
  ∀ (v : ι → T) (i : ι), v i = V → a v = 0

/-- The exterior product uses the shuffle convention, with scalar
multiplication after the tensor-valued alternating product. -/
noncomputable def wedge {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) : T [⋀^ι ⊕ κ]→ₗ[ℝ] ℂ :=
  (LinearMap.mul' ℝ ℂ).compAlternatingMap (a.domCoprod b)

/-- Slot types retain the order of each two-form factor. -/
def WedgePowerSlots : ℕ → Type
  | 0 => Fin 0
  | n + 1 => Fin 2 ⊕ WedgePowerSlots n

instance wedgePowerSlotsFintype (n : ℕ) : Fintype (WedgePowerSlots n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 0))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin 2 ⊕ WedgePowerSlots n))

noncomputable instance wedgePowerSlotsDecidableEq (n : ℕ) : DecidableEq (WedgePowerSlots n) :=
  Classical.decEq _

/-- Iterated shuffle exterior power of an actual alternating two-form. -/
noncomputable def wedgePower (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    (n : ℕ) → T [⋀^WedgePowerSlots n]→ₗ[ℝ] ℂ
  | 0 => AlternatingMap.constOfIsEmpty ℝ T (Fin 0) 1
  | n + 1 => wedge a (wedgePower a n)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedge_smul_left (c : ℂ) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (c • a) b = c • wedge a b := by
  ext v
  change (LinearMap.mul' ℝ ℂ) ((c • a).domCoprod b v) =
    c * (LinearMap.mul' ℝ ℂ) (a.domCoprod b v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply,
      smul_eq_mul]
    simp only [Units.smul_def, TensorProduct.smul_tmul']
    simp only [LinearMap.mul'_apply]
    ring

lemma wedge_smul_right (c : ℂ) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge a (c • b) = c • wedge a b := by
  ext v
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod (c • b) v) =
    c * (LinearMap.mul' ℝ ℂ) (a.domCoprod b v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply,
      smul_eq_mul]
    simp only [Units.smul_def, TensorProduct.smul_tmul']
    simp only [LinearMap.mul'_apply]
    ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CovectorVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct BigOperators

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The alternating product of a family of real-linear complex covectors. -/
noncomputable def covectorVolume (l : ι → T →ₗ[ℝ] ℂ) : T [⋀^ι]→ₗ[ℝ] ℂ :=
  ((MultilinearMap.mkPiAlgebra ℝ ι ℂ).compLinearMap l).alternatization

lemma covectorVolume_apply (l : ι → T →ₗ[ℝ] ℂ) (v : ι → T) :
    covectorVolume l v = Matrix.det (Matrix.of (fun row column => l column (v row))) := by
  simp only [covectorVolume, MultilinearMap.alternatization_def, Matrix.det_apply,
    Matrix.of_apply, _root_.sum_apply, _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι : Type*} [AddCommGroup T] [Module ℝ T]
  [Fintype J] [Fintype ι] [DecidableEq ι]

noncomputable def complexCoord (b : Module.Basis J ℝ T) (j : J) : T →ₗ[ℝ] ℂ :=
  Complex.ofRealLI.toLinearMap.comp (b.coord j)

omit [Fintype J] in
@[simp] lemma complexCoord_apply [Fintype J] (b : Module.Basis J ℝ T) (j : J) (x : T) :
    complexCoord b j x = (b.repr x j : ℂ) := rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]

def prependFinEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  { toFun := Sum.elim (fun _ => 0) Fin.succ
    invFun := Fin.cases (Sum.inl 0) Sum.inr
    left_inv := by
      intro s
      cases s with
      | inl i => exact congrArg Sum.inl (Subsingleton.elim _ _)
      | inr i => rfl
    right_inv := by
      intro i
      refine Fin.cases rfl (fun j => rfl) i }

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedge_summand_eval (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (ι ⊕ κ)) (v : ι ⊕ κ → T) :
    (LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand a b (Quotient.mk'' σ) v) =
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        (a (fun i => v (σ (Sum.inl i))) * b (fun i => v (σ (Sum.inr i)))) := by
  rw [AlternatingMap.domCoprod.summand_mk'']
  change (LinearMap.mul' ℝ ℂ) ((Equiv.Perm.sign σ : ℤ) •
    (a (fun index => v (σ (Sum.inl index))) ⊗ₜ[ℝ]
      b (fun index => v (σ (Sum.inr index))))) = _
  rw [map_zsmul, LinearMap.mul'_apply, zsmul_eq_mul]

/-- The exact variation of an iterated shuffle power, without suppressing any
terms by a formal commutativity or integration-by-parts assumption. -/
noncomputable def wedgePowerVariation (a da : T [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    (k : ℕ) → T [⋀^WedgePowerSlots k]→ₗ[ℝ] ℂ
  | 0 => 0
  | k + 1 => wedge da (wedgePower a k) + wedge a (wedgePowerVariation a da k)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_BasisContinuousWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def continuousCovectorVolume (l : ι → E →ₗ[ℝ] ℂ) : E [⋀^ι]→L[ℝ] ℂ :=
  { covectorVolume l with
    cont := by
      change Continuous (fun v => covectorVolume l v)
      simp only [covectorVolume_apply]
      apply Continuous.matrix_det
      fun_prop }

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
@[simp] lemma continuousCovectorVolume_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (l : ι → E →ₗ[ℝ] ℂ) :
    (continuousCovectorVolume l).toAlternatingMap = covectorVolume l := rfl

noncomputable def basisContinuousWedge (basis : Module.Basis J ℝ E)
    (A : E [⋀^ι]→L[ℝ] ℂ) (B : E [⋀^κ]→L[ℝ] ℂ) : E [⋀^ι ⊕ κ]→L[ℝ] ℂ :=
  ∑ q : ι → J, ∑ r : κ → J,
    ((A (basis ∘ q) / (Fintype.card ι).factorial) *
      (B (basis ∘ r) / (Fintype.card κ).factorial)) •
      continuousCovectorVolume (Sum.elim (complexCoord basis ∘ q) (complexCoord basis ∘ r))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_DilationTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

noncomputable def realDilation (r : ℝ) : E →L[ℝ] E := r • ContinuousLinearMap.id ℝ E
omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
@[simp] lemma realDilation_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (r : ℝ) (x : E) : realDilation r x = r • x := rfl

/-- The full shuffle boundary form, using actual exterior differentiation. -/
noncomputable def boundaryForm (u : E → ℂ) (k : ℕ) (x : E) :
    E [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ :=
  wedge (oneForm (dcLinear u) x).toAlternatingMap
    (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap k)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_BoundaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology TensorProduct

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The linear operation taking a real derivative to d^c. -/
noncomputable def dcOperator : (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ) :=
  (-1 / 4 : ℂ) • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure

noncomputable def dcOneOperator : (E →L[ℝ] ℂ) →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℂ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
    (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp dcOperator

/-- The second derivative determines the actual exterior derivative of d^c. -/
noncomputable def ddcTwoJet (B : E →L[ℝ] (E →L[ℝ] ℂ)) :
    E [⋀^Fin 2]→L[ℝ] ℂ :=
  alternatizeUncurryFin (dcOneOperator.comp B)

abbrev RealComplexTwoJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] ℂ) × (E →L[ℝ] (E →L[ℝ] ℂ))

noncomputable def boundaryJet (p : RealComplexTwoJet E) (k : ℕ) :
    E [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ :=
  wedge (dcOneOperator p.1).toAlternatingMap
    (wedgePower (ddcTwoJet p.2).toAlternatingMap k)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_DCForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The usual pullback, defined using the actual derivative of the parametrization. -/
def pullbackForm {k : ℕ} (φ : V → E) (ω : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (y : V) : V [⋀^Fin k]→L[ℝ] ℝ :=
  (ω (φ y)).compContinuousLinearMap (fderiv ℝ φ y)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CoordinateBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace MahlerStokes

/-- The squared Euclidean radius, in real coordinates with standard Lebesgue measure. -/
def radiusSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2
/-- An actual Euclidean ball in coordinates; the ambient Pi norm is irrelevant. -/
def coordBall (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) := {x | radiusSq x < R ^ 2}
def chord {n : ℕ} (R : ℝ) (y : Fin n → ℝ) : ℝ := Real.sqrt (R ^ 2 - radiusSq y)

lemma radiusSq_insertNth {n : ℕ} (i : Fin (n+1)) (t : ℝ) (y : Fin n → ℝ) :
    radiusSq (i.insertNth t y) = t ^ 2 + radiusSq y := by
  unfold radiusSq
  rw [Fin.sum_univ_succAbove _ i]
  simp

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CoordinateAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- The closed annulus is used only for local differentiability and continuity. -/
def closedShell (n : ℕ) (a R : ℝ) : Set (Fin n → ℝ) :=
  {x | a^2 ≤ radiusSq x ∧ radiusSq x ≤ R^2}

/-- Open-ball puncture; the inner sphere has zero volume. -/
def coordAnnulus (n : ℕ) (a R : ℝ) : Set (Fin n → ℝ) :=
  coordBall n R \ coordBall n a

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ShellRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

def coordClosedBall (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) := {x | radiusSq x ≤ R^2}

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FormStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Ordered coordinate basis for dx_0 wedge ... wedge dx_n. -/
def coordinateBasis (n : ℕ) (i : Fin n) : Fin n → ℝ := Pi.single i 1

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ChartStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

/-- Actual coefficient of an n-form in the oriented omitted-coordinate basis. -/
def orientedCoefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (i : Fin (n+1)) (x : Fin (n+1) → ℝ) : ℝ :=
  (-1 : ℝ)^i.val * ω x (i.removeNth (coordinateBasis (n+1)))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularLevelCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

/-- Replace the k-th coordinate by the potential itself. -/
def levelCoordinates {d : ℕ} (g : (Fin d → ℝ) → ℝ) (k : Fin d)
    (x : Fin d → ℝ) : Fin d → ℝ := Function.update x k (g x)

def levelDerivative {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i => if i = k then L else ContinuousLinearMap.proj i

lemma levelDerivative_apply {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d)
    (x : Fin d → ℝ) (i : Fin d) :
    levelDerivative L k x i = if i = k then L x else x i := by
  by_cases hi : i = k <;> simp [levelDerivative, hi]

lemma levelDerivative_injective {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d)
    (hk : L (Pi.single k 1) ≠ 0) : Function.Injective (levelDerivative L k) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hxk : L x = 0 := by
    have := congrFun hx k
    simpa [levelDerivative_apply] using this
  have hxi (i : Fin d) (hi : i ≠ k) : x i = 0 := by
    have := congrFun hx i
    simpa [levelDerivative_apply, hi] using this
  have he : x = x k • Pi.single k (1 : ℝ) := by
    ext i
    by_cases hi : i = k
    · subst i; simp
    · simp [hi, hxi i hi]
  have hkx : x k = 0 := by
    rw [he, map_smul, smul_eq_mul] at hxk
    exact (mul_eq_zero.mp hxk).resolve_right hk
  rw [he, hkx, zero_smul]

def levelDerivativeEquiv {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) (k : Fin d)
    (hk : L (Pi.single k 1) ≠ 0) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.ofBijective (levelDerivative L k)
    (LinearMap.ker_eq_bot.mpr (levelDerivative_injective L k hk))
    (LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp (levelDerivative_injective L k hk)))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularSublevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

def regularSublevel {d : ℕ} (U : Set (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ) (R : ℝ) :=
  U ∩ {x | g x < R}

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularBoundaryAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

/-- A bounded open portion of a genuine regular-level chart, inside U. -/
structure RegularBoundaryPatch (d : ℕ) (U : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → ℝ) where
  coordinate : Fin d
  chart : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)
  domain : Set (Fin d → ℝ)
  open_domain : IsOpen domain
  bounded_domain : Bornology.IsBounded domain
  domain_source : domain ⊆ chart.source
  domain_U : domain ⊆ U
  chart_eq : ∀ z, chart z = levelCoordinates g coordinate z
  smooth_chart : ContDiffOn ℝ 2 chart chart.source
  smooth_inverse : ContDiffOn ℝ 2 chart.symm chart.target

/-- A finite cover extracted from actual derivative-based charts. -/
structure RegularBoundaryAtlas (d : ℕ) (U : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ)) where
  Index : Type
  finite : Fintype Index
  patch : Index → RegularBoundaryPatch d U g
  covers : K ⊆ ⋃ i, (patch i).domain

attribute [instance] RegularBoundaryAtlas.finite

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology Manifold
namespace MahlerStokes

/-- Adjoin the actual sublevel as the interior patch. This finite cover covers
the whole closure, so derivative cancellation can be used throughout D_R. -/
def sublevelPatchDomain {d : ℕ} {U : Set (Fin d → ℝ)} {g : (Fin d → ℝ) → ℝ}
    {R : ℝ} (a : RegularBoundaryAtlas d U g (frontier (regularSublevel U g R))) :
    Option a.Index → Set (Fin d → ℝ)
  | none => regularSublevel U g R
  | some i => (a.patch i).domain

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HalfspaceStokes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

def lowerHalfspace {d : ℕ} (k : Fin d) (R : ℝ) : Set (Fin d → ℝ) := {x | x k < R}

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OrientedChartIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

/-- Orientation of a real Jacobian. Its value at zero is immaterial for
change of variables; genuine local diffeomorphisms have nonzero Jacobian. -/
def jacobianOrientation (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ChartExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

/-- The oriented pullback, extended by zero outside the actual chart target. -/
def extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  e.target.indicator (fun y => jacobianOrientation (fderiv ℝ e.symm y).det •
    pullbackForm e.symm ω y)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def continuousReindex (e : ι ≃ κ) :
    (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] (E [⋀^κ]→L[ℝ] ℂ) :=
  AlternatingMap.mkContinuousLinear
    ((AlternatingMap.domDomCongrₗ ℝ e).comp
      (ContinuousAlternatingMap.toAlternatingMapLinear (R := ℝ))) 1 (by
    intro A v
    change ‖A (v ∘ e)‖ ≤ 1 * ‖A‖ * ∏ i, ‖v i‖
    simp only [one_mul]
    have h := A.le_opNorm (v ∘ e)
    simpa only [Function.comp_def, e.prod_comp (fun i => ‖v i‖)] using h)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma continuousReindex_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : E [⋀^ι]→L[ℝ] ℂ) (v : κ → E) :
    continuousReindex e A v = A (v ∘ e) := rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma continuousReindex_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : E [⋀^ι]→L[ℝ] ℂ) :
    (continuousReindex e A).toAlternatingMap = A.toAlternatingMap.domDomCongr e := rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler

/-- The recursive wedge slots list each coordinate's real slot before its
imaginary slot. This equivalence records that interleaved order. -/
def pairSlotEquiv : (k : ℕ) → WedgePowerSlots k ≃ Fin k × Fin 2
  | 0 => by
    change Fin 0 ≃ Fin 0 × Fin 2
    exact Equiv.equivOfIsEmpty _ _
  | k+1 =>
    { toFun := Sum.elim (fun j => (0,j))
        (fun s => ((pairSlotEquiv k s).1.succ, (pairSlotEquiv k s).2))
      invFun := fun p => Fin.cases (Sum.inl p.2)
        (fun i => Sum.inr ((pairSlotEquiv k).symm (i,p.2))) p.1
      left_inv := by
        intro s
        cases s with
        | inl j => rfl
        | inr s =>
          change Sum.inr ((pairSlotEquiv k).symm (pairSlotEquiv k s)) = Sum.inr s
          rw [Equiv.symm_apply_apply]
      right_inv := by
        rintro ⟨i,j⟩
        refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · change ((pairSlotEquiv k ((pairSlotEquiv k).symm (i, j))).1.succ,
            (pairSlotEquiv k ((pairSlotEquiv k).symm (i, j))).2) = (i.succ, j)
          rw [Equiv.apply_symm_apply] }

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

noncomputable def pairedCovectors {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ) :
    WedgePowerSlots k → T →ₗ[ℝ] ℂ :=
  fun s => p (pairSlotEquiv k s).1 (pairSlotEquiv k s).2

noncomputable def pairPermutation {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (WedgePowerSlots k) :=
  (pairSlotEquiv k).symm.permCongr (Equiv.prodCongrLeft (fun _ : Fin 2 => σ))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MassTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Mahler

abbrev ComplexEuclidean (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The hypotheses for the isolated-zero mass inequality.
This structure records hypotheses; it does not assert the inequality. -/
structure MassHypotheses (n N m : ℕ) (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ)
    (G : Fin N → MvPolynomial (Fin n) ℂ) : Prop where
  dimension_pos : 1 ≤ n
  degree_pos : 1 ≤ m
  open_domain : IsOpen U
  zero_mem : (0 : ComplexEuclidean n) ∈ U
  holomorphic : ∀ j, DifferentiableOn ℂ (f j) U
  isolated_zero : ∀ z ∈ U, (∀ j, f j z = 0) ↔ z = 0
  homogeneous : ∀ j, (G j).IsHomogeneous m
  leading_nonzero : ∀ z : ComplexEuclidean n, z ≠ 0 →
    ∃ j, MvPolynomial.eval (fun i => z i) (G j) ≠ 0
  taylor_remainder : Asymptotics.IsBigO (𝓝[≠] (0 : ComplexEuclidean n))
    (fun z => (WithLp.toLp 2 (fun j => f j z - MvPolynomial.eval (fun i => z i) (G j)) :
      ComplexEuclidean N)) (fun z => ‖z‖ ^ (m + 1))
  compact_sublevels : ∀ R : ℝ, 0 < R → R < 1 →
    IsCompact (closure (U ∩ {z | tau f z < R})) ∧
      closure (U ∩ {z | tau f z < R}) ⊆ U

/-- The density n! det(tau_{z_k bar z_l}) for the complex Hessian convention. -/
noncomputable def massDensity {n N : ℕ} (f : Fin N → ComplexEuclidean n → ℂ)
    (z : ComplexEuclidean n) : ℝ :=
  (n.factorial : ℝ) * (sourceHessian (energy f) z
    (fun i => EuclideanSpace.single i (1 : ℂ))).det.re

/-- The extended nonnegative integral allows infinite mass.
This definition does not assert its equality to an exterior-form integral. -/
noncomputable def massIntegral {n N : ℕ} (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) : ℝ≥0∞ :=
  ∫⁻ z in U ∩ {z | tau f z < 1}, ENNReal.ofReal (massDensity f z)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceHomogeneous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

namespace Mahler

noncomputable def polynomialMap {n N : ℕ} (G : Fin N → MvPolynomial (Fin n) ℂ)
    (j : Fin N) (z : ComplexEuclidean n) : ℂ := MvPolynomial.eval (fun i => z i) (G j)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The deformation beta, represented as a real-linear one-form. -/
noncomputable def betaLinear (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ)
    (x : E) : E →L[ℝ] ℂ := dcLinear (logTau f) x - (m : ℝ) • dcLinear (logTau g) x

/-- The actual one-form alpha_t = m alpha_0 + t beta. -/
noncomputable def alphaPath (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ)
    (t : ℝ) (x : E) : E →L[ℝ] ℂ :=
  (m : ℝ) • dcLinear (logTau g) x + t • betaLinear f g m x

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def coordinateMap (n : ℕ) (j : Fin n) (z : ComplexEuclidean n) : ℂ := z j

/-- The tangent hyperplane of a Euclidean sphere, with its usual real metric. -/
noncomputable def sphereTangent {n : ℕ} (z : ComplexEuclidean n) : Submodule ℝ (ComplexEuclidean n) :=
  (ℝ ∙ z)ᗮ

lemma circle_mem_sphereTangent {n : ℕ} (z : ComplexEuclidean n) : I • z ∈ sphereTangent z := by
  rw [sphereTangent, Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact real_inner_I_smul_self ℂ (z i)

noncomputable def circleTangent {n : ℕ} (z : ComplexEuclidean n) : sphereTangent z :=
  ⟨I • z, circle_mem_sphereTangent z⟩

noncomputable def tangentForm {n : ℕ} {ι : Type*} (z : ComplexEuclidean n)
    (a : ComplexEuclidean n [⋀^ι]→ₗ[ℝ] ℂ) : sphereTangent z [⋀^ι]→ₗ[ℝ] ℂ :=
  a.compLinearMap (sphereTangent z).subtype

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_NormSquareForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def normEnergy (n : ℕ) (z : ComplexEuclidean n) : ℂ := (‖z‖ ^ 2 : ℝ)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_NormExteriorPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def realCoordinate {n : ℕ} (j : Fin n) : ComplexEuclidean n →ₗ[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (Complex.reCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ))).toLinearMap
noncomputable def imagCoordinate {n : ℕ} (j : Fin n) : ComplexEuclidean n →ₗ[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (Complex.imCLM.comp ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ))).toLinearMap

@[simp] lemma realCoordinate_apply {n : ℕ} (j : Fin n) (v : ComplexEuclidean n) :
    realCoordinate j v = ((v j).re : ℂ) := rfl
@[simp] lemma imagCoordinate_apply {n : ℕ} (j : Fin n) (v : ComplexEuclidean n) :
    imagCoordinate j v = ((v j).im : ℂ) := rfl

noncomputable def coordinatePair {n : ℕ} (j : Fin n) : Fin 2 → ComplexEuclidean n →ₗ[ℝ] ℂ :=
  ![realCoordinate j, imagCoordinate j]

/-- The actual positive coordinate volume form, ordered dx_1,dy_1,... . -/
noncomputable def interleavedVolume (n : ℕ) :
    ComplexEuclidean n [⋀^WedgePowerSlots n]→ₗ[ℝ] ℂ :=
  covectorVolume (pairedCovectors (coordinatePair (n := n)))

/-- The positively ordered real coordinate basis, using the same recursive
slots as the exterior power. -/
noncomputable def interleavedBasis {n : ℕ} (s : WedgePowerSlots n) : ComplexEuclidean n :=
  EuclideanSpace.single (pairSlotEquiv n s).1 (if (pairSlotEquiv n s).2 = 0 then 1 else I)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric
open scoped BigOperators
namespace Mahler

/-- The concrete area measure induced by Euclidean volume on the unit sphere. -/
noncomputable def sphereArea (n : ℕ) : Measure (sphere (0 : ComplexEuclidean n) 1) :=
  (volume : Measure (ComplexEuclidean n)).toSphere

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OrientedSphereDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory Metric

namespace Mahler

section Cofactors
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}

/-- Outward surface coefficient in an ambient orthonormal frame. Division by
`Ω b` fixes the orientation to the specified ambient volume form. At a unit
normal x this is the cofactor formula for the restriction of B to x-perp. -/
noncomputable def orientedDensity (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) : ℂ :=
  (∑ i : Fin (d+1), (b.repr x i : ℂ) * (-1 : ℂ)^i.val * B (i.removeNth b)) / Ω b

/-- Exterior multiplication by the normal covector, expressed by the
standard alternating sum. It is used only to verify the surface density. -/
noncomputable def normalWedge (x : E) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) :
    E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ :=
  AlternatingMap.alternatizeUncurryFin ((innerSL ℝ x).toLinearMap.smulRight B)

end Cofactors

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereFluxIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric
open scoped BigOperators

namespace Mahler

/-- The order is recursive and interleaved, not an arbitrary finite equivalence. -/
def powerFinEquiv : (k : ℕ) → WedgePowerSlots k ≃ Fin (2*k)
  | 0 => Equiv.refl _
  | k+1 => (Equiv.sumCongr (Equiv.refl (Fin 2)) (powerFinEquiv k)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))

def boundaryFinEquiv (k : ℕ) : (Fin 1 ⊕ WedgePowerSlots k) ≃ Fin (2*k+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) (powerFinEquiv k)).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

def ambientFinEquiv (k : ℕ) : WedgePowerSlots (k+1) ≃ Fin ((2*k+1)+1) :=
  (powerFinEquiv (k+1)).trans (finCongr (by omega))

noncomputable def sphereVolume (k : ℕ) :
    ComplexEuclidean (k+1) [⋀^Fin ((2*k+1)+1)]→ₗ[ℝ] ℂ :=
  (interleavedVolume (k+1)).domDomCongr (ambientFinEquiv k)

noncomputable def sphereFrame (k : ℕ) :
    OrthonormalBasis (Fin ((2*k+1)+1)) ℝ (ComplexEuclidean (k+1)) :=
  (Pi.orthonormalBasis (fun _ : Fin (k+1) => Complex.orthonormalBasisOneI)).reindex
    ((Equiv.sigmaEquivProd (Fin (k+1)) (Fin 2)).trans
      ((pairSlotEquiv (k+1)).symm.trans (ambientFinEquiv k)))

/-- Actual boundary form, in its standard ordered slots. -/
noncomputable def boundaryFormFin {k : ℕ}
    (a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+1)) :
    ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ :=
  (wedge (oneForm a x).toAlternatingMap
    (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k)).domDomCongr (boundaryFinEquiv k)

/-- The integral uses Euclidean area and the cofactor surface density with
outward normal x on the unit sphere. -/
noncomputable def sphereFlux (k : ℕ)
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ) : ℝ :=
  ∫ x : sphere (0 : ComplexEuclidean (k+1)) 1,
    (orientedDensity (sphereFrame k) (sphereVolume k) (B x) x).re ∂sphereArea (k+1)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeTwoDifferentialAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

def twoOnePermutation : Equiv.Perm (Fin 3) :=
  (finSumFinEquiv (m := 2) (n := 1)).symm.trans
    ((Equiv.sumComm (Fin 2) (Fin 1)).trans finSumFinEquiv)

def derivativeLeftEquiv (n : ℕ) : Fin 3 ⊕ Fin n ≃ Fin (2+n+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def derivativeRightEquiv (n : ℕ) : Fin 2 ⊕ Fin (n+1) ≃ Fin (2+n+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorLeibnizTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

noncomputable def continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    (A : E [⋀^Fin p]→L[ℝ] ℂ) (B : E [⋀^Fin q]→L[ℝ] ℂ) :
    E [⋀^Fin (p+q)]→L[ℝ] ℂ :=
  continuousReindex finSumFinEquiv (basisContinuousWedge basis A B)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ReferencePole
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def referencePole (k : ℕ) : ComplexEuclidean (k+1) :=
  EuclideanSpace.single 0 1

lemma referencePole_inner {k : ℕ} (v : ComplexEuclidean (k+1)) :
    inner ℝ (referencePole k) v = (v 0).re := by
  simp [referencePole, PiLp.inner_apply, Complex.inner]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0; simp [hj0]
  · simp

lemma referencePole_tangent_iff {k : ℕ} (v : ComplexEuclidean (k+1)) :
    v ∈ sphereTangent (referencePole k) ↔ (v 0).re = 0 := by
  rw [sphereTangent, Submodule.mem_orthogonal_singleton_iff_inner_right, referencePole_inner]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ReferencePoleFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def poleFrameVector (k : ℕ) : Fin 1 ⊕ WedgePowerSlots k → ComplexEuclidean (k+1) :=
  Sum.elim (fun _ => EuclideanSpace.single 0 I)
    (fun s => EuclideanSpace.single (pairSlotEquiv k s).1.succ
      (if (pairSlotEquiv k s).2 = 0 then 1 else I))

lemma poleFrameVector_tangent {k : ℕ} (s : Fin 1 ⊕ WedgePowerSlots k) :
    poleFrameVector k s ∈ sphereTangent (referencePole k) := by
  rw [referencePole_tangent_iff]
  cases s <;> simp [poleFrameVector]

noncomputable def poleTangentFrame (k : ℕ) :
    Fin 1 ⊕ WedgePowerSlots k → sphereTangent (referencePole k) :=
  fun s => ⟨poleFrameVector k s, poleFrameVector_tangent s⟩

noncomputable def poleFrameFin (k : ℕ) : Fin (2*k+1) → ComplexEuclidean (k+1) :=
  poleFrameVector k ∘ (boundaryFinEquiv k).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousSphereIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric

namespace Mahler

/-- The flux along the one-form deformation. -/
noncomputable def homogeneousPathFlux (k N m : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) (t : ℝ) : ℝ :=
  sphereFlux k (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t))

/-- The actual homogeneous endpoint, with no flux-constancy premise. -/
noncomputable def homogeneousSphereFlux (k N : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) : ℝ :=
  sphereFlux k (boundaryFormFin (dcLinear (logTau (polynomialMap G))))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousDensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler

/-- The residual variation, retaining all terms and the actual exterior
spatial derivatives. Its sphere integral has not been asserted to vanish. -/
noncomputable def boundaryResidualFin {k : ℕ}
    (a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+1)) :
    ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ :=
  (wedge (oneForm a x).toAlternatingMap
    (wedgePowerVariation (extDeriv (oneForm a) x).toAlternatingMap
      (extDeriv (oneForm b) x).toAlternatingMap k)).domDomCongr (boundaryFinEquiv k)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ClosedWedgePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

noncomputable def basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    (A : E [⋀^Fin 2]→L[ℝ] ℂ) : (k : ℕ) → E [⋀^Fin (2*k)]→L[ℝ] ℂ
  | 0 => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | k+1 => continuousReindex (finCongr (by omega))
      (continuousWedgeFin basis A (basisContinuousWedgePower basis A k))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CompactIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace CompactIntegral

def tube (U : Set (ℂ × ℝ)) : Set ℂ := {z | ∀ t ∈ Icc (0 : ℝ) 1, (z,t) ∈ U}

end CompactIntegral

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_CoordinateEuclidean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric
namespace MahlerStokes

/-- Explicit identification with the L2 Euclidean norm, rather than the
ambient supremum norm on the coordinate function space. -/
theorem radiusSq_eq_euclidean_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    radiusSq x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2 := by
  simp [EuclideanSpace.real_norm_sq_eq, radiusSq]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ComplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory WithLp
open scoped ENNReal
namespace MahlerStokes

/-- Interleaved real coordinates: index 2i is real and index 2i+1 imaginary. -/
def interleavedEuclidean (n : ℕ) :
    EuclideanSpace ℝ (Fin (n*2)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun x := toLp 2 (fun i => ⟨x (finProdFinEquiv (i,0)), x (finProdFinEquiv (i,1))⟩)
  invFun z := toLp 2 (fun j => if (finProdFinEquiv.symm j).2 = 0 then
    (z (finProdFinEquiv.symm j).1).re else (z (finProdFinEquiv.symm j).1).im)
  left_inv x := by
    ext j
    obtain ⟨⟨i,k⟩, rfl⟩ := finProdFinEquiv.surjective j
    fin_cases k <;> simp
  right_inv z := by
    ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' c x := by
    ext i : 1
    apply Complex.ext <;> simp [Complex.real_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    rw [← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_two, Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
    rfl

/-- The same coordinate map on the ordinary Pi space used by the Stokes integrals. -/
def complexCoordinates (n : ℕ) :
    (Fin (n*2) → ℝ) ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n*2) => ℝ)).symm.trans
    (interleavedEuclidean n).toContinuousLinearEquiv

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_Jacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Matrix Real

noncomputable def weightedGram {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (c : Fin N → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := A.transpose * Matrix.diagonal c * A

noncomputable def hessianWeight (m : ℝ) (f d : ℂ) : ℝ :=
  m^2*‖f‖^(2*m-2 : ℝ)*‖d‖^2

noncomputable def verticalWeight (m : ℝ) (f d : ℂ) : ℝ :=
  (4*m/Real.pi)*‖f‖^(2*m-2 : ℝ)*‖d‖^2

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PlanarIntegralRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The fixed-interval parametrization of the entire vertical segment. -/
def segmentPoint (p : ℂ × ℝ) : ℂ := (p.1.re : ℂ) + (p.2 * p.1.im : ℝ) * I

def segmentParameterDomain : Set (ℂ × ℝ) := segmentPoint ⁻¹' MahlerConformal.Omega

def planarSegmentDomain : Set ℂ := CompactIntegral.tube segmentParameterDomain

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_StripDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open scoped Topology ContDiff
open MahlerConformal

variable {n N : ℕ}

noncomputable def rowCLM (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) :
    (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, A j i • ContinuousLinearMap.proj i

noncomputable def stripCoordinateCLM (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((rowCLM A j).comp (ContinuousLinearMap.fst ℝ _ _)) +
  Complex.I • Complex.ofRealCLM.comp ((rowCLM A j).comp (ContinuousLinearMap.snd ℝ _ _))

noncomputable def planarDifferential (m : ℕ) (u : ℂ) : ℂ →L[ℝ] ℝ :=
  fderiv ℝ (fun z : ℂ => planarPrimitive m z.re z.im) u

noncomputable def stripDerivative (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.pi fun i =>
    ∑ j, A j i • (planarDifferential m (stripCoordinate A z j)).comp (stripCoordinateCLM A j))

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_StripVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

noncomputable def stripSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) := stripDomain A ∩ {z | stripTau A m z < 1}

noncomputable def stripHessianDet (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  (weightedGram A (fun j => hessianWeight m (inverseF (stripCoordinate A z j))
    (deriv inverseF (stripCoordinate A z j)))).det

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ComplexStripMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

def complexToReal (z : Fin n → ℂ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => (z i).re,fun i => (z i).im)

def realToComplex (z : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℂ :=
  fun i => (z.1 i : ℂ)+(z.2 i : ℂ)*I

lemma realToComplex_complexToReal (z : Fin n → ℂ) : realToComplex (complexToReal z) = z := by
  funext i
  exact Complex.re_add_im (z i)

lemma complexToReal_realToComplex (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    complexToReal (realToComplex z) = z := by
  apply Prod.ext <;> funext i <;> simp [complexToReal,realToComplex]

noncomputable def complexRealLinearEquiv : (Fin n → ℂ) ≃ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) where
  toFun := complexToReal
  invFun := realToComplex
  left_inv := realToComplex_complexToReal
  right_inv := complexToReal_realToComplex
  map_add' z w := by apply Prod.ext <;> funext i <;> simp [complexToReal]
  map_smul' c z := by apply Prod.ext <;> funext i <;> simp [complexToReal]

noncomputable def complexRealEquiv : (Fin n → ℂ) ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  complexRealLinearEquiv.toContinuousLinearEquiv

noncomputable def complexRow (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) :
    (Fin n → ℂ) →L[ℂ] ℂ := ∑ i, (A j i : ℂ) • ContinuousLinearMap.proj i

noncomputable def complexStripDomain (A : Matrix (Fin N) (Fin n) ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, complexRow A j z ∈ Omega}

noncomputable def specialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) : Fin N → ℂ :=
  fun j => inverseF (complexRow A j z)^m

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ComplexVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory WithLp
open scoped ENNReal
namespace SymmetricMahler

variable (n : ℕ)

/-- Realification with the Euclidean norm on both groups of real coordinates. -/
noncomputable def complexEuclideanRealification :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) where
  toFun z := toLp 2 (toLp 2 (fun i => (z i).re), toLp 2 (fun i => (z i).im))
  invFun z := toLp 2 (fun i => ⟨(ofLp z).1 i, (ofLp z).2 i⟩)
  left_inv z := by ext i; rfl
  right_inv z := by rfl
  map_add' z w := by rfl
  map_smul' c z := by
    apply ofLp_injective 2
    apply Prod.ext <;> ext i <;> simp
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      Real.norm_eq_abs, sq_abs]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (z i).re ^ 2 + (z i).im ^ 2 = ‖z i‖ ^ 2
    simpa only [Complex.normSq_apply, pow_two] using (Complex.sq_norm (z i)).symm

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ContinuousWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The shuffle product bundled with its actual joint-vector continuity. -/
def continuousWedge (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    E [⋀^ι ⊕ κ]→L[ℝ] ℂ :=
  { wedge a.toAlternatingMap b.toAlternatingMap with
    cont := by
      change Continuous (fun v => wedge a.toAlternatingMap b.toAlternatingMap v)
      have ht (σ : Equiv.Perm.ModSumCongr ι κ) : Continuous
          (fun v : ι ⊕ κ → E => (LinearMap.mul' ℝ ℂ)
            (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap σ v)) := by
        induction σ using Quotient.inductionOn' with
        | h σ =>
          simp only [wedge_summand_eval]
          exact continuous_const.mul
            ((a.cont.comp (continuous_pi (fun i => continuous_apply _))).mul
              (b.cont.comp (continuous_pi (fun i => continuous_apply _))))
      simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
        _root_.sum_apply, _root_.map_sum] using
          continuous_finsetSum Finset.univ (fun σ _ => ht σ) }

@[simp] lemma continuousWedge_apply (a : E [⋀^ι]→L[ℝ] ℂ)
    (b : E [⋀^κ]→L[ℝ] ℂ) (v : ι ⊕ κ → E) :
    continuousWedge a b v = wedge a.toAlternatingMap b.toAlternatingMap v := rfl

instance finiteDimensional_continuousAlternatingMap [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (E [⋀^ι]→L[ℝ] ℂ) := by
  let L : (E [⋀^ι]→L[ℝ] ℂ) →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ :=
    { toFun := fun a => a.toAlternatingMap.toMultilinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective L (fun a b h => by
    ext v
    exact congrArg (fun c : MultilinearMap ℝ (fun _ : ι => E) ℂ => c v) h)

lemma continuousWedge_add_left (a a' : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge (a+a') b = continuousWedge a b + continuousWedge a' b := by
  ext v
  change wedge (a.toAlternatingMap + a'.toAlternatingMap) b.toAlternatingMap v =
    wedge a.toAlternatingMap b.toAlternatingMap v + wedge a'.toAlternatingMap b.toAlternatingMap v
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.add_tmul, map_add]
  rfl

lemma continuousWedge_add_right (a : E [⋀^ι]→L[ℝ] ℂ) (b b' : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge a (b+b') = continuousWedge a b + continuousWedge a b' := by
  ext v
  change wedge a.toAlternatingMap (b.toAlternatingMap + b'.toAlternatingMap) v =
    wedge a.toAlternatingMap b.toAlternatingMap v + wedge a.toAlternatingMap b'.toAlternatingMap v
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.tmul_add, map_add]
  rfl

lemma continuousWedge_smul_left (r : ℝ) (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge (r • a) b = r • continuousWedge a b := by
  have he : (r • a).toAlternatingMap = (r : ℂ) • a.toAlternatingMap := by
    ext v; simp [Complex.real_smul]
  ext v
  simp only [continuousWedge_apply, he, wedge_smul_left, AlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, Complex.real_smul, smul_eq_mul]

lemma continuousWedge_smul_right (r : ℝ) (a : E [⋀^ι]→L[ℝ] ℂ) (b : E [⋀^κ]→L[ℝ] ℂ) :
    continuousWedge a (r • b) = r • continuousWedge a b := by
  have he : (r • b).toAlternatingMap = (r : ℂ) • b.toAlternatingMap := by
    ext v; simp [Complex.real_smul]
  ext v
  simp only [continuousWedge_apply, he, wedge_smul_right, AlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, Complex.real_smul, smul_eq_mul]

/-- Exterior multiplication is an actual continuous bilinear map. -/
def continuousWedgeCLM [FiniteDimensional ℝ E] :
    (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap
        { toFun := continuousWedge a
          map_add' := continuousWedge_add_right a
          map_smul' := fun r b => continuousWedge_smul_right r a b }
      map_add' := fun a a' => by ext b v; exact congrArg (fun c => c v) (continuousWedge_add_left a a' b)
      map_smul' := fun r a => by ext b v; exact congrArg (fun c => c v) (continuousWedge_smul_left r a b) }

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConvexGeometry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [fintypeI : Fintype I] [fintypeJ : Fintype J] [decidableEqI : DecidableEq I]

/-- Independent coordinate rows followed by a finite prefix of polar rows. -/
def approximationRows (c : ℝ) (a : ℕ → I → ℝ) (N : ℕ) : (I ⊕ Fin N) → I → ℝ :=
  Sum.elim (fun i => Pi.single i c) (fun j => a j)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ConvexSequence
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {n : ℕ} {K : Set (Fin n → ℝ)}

def prependPolarBasis (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (j : ℕ) : coordinatePolar K :=
  if h : j < n then ⟨Pi.single ⟨j, h⟩ c, hcK ⟨j, h⟩⟩ else a (j-n)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SpecialLeadingTerm
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

noncomputable def inverseLinearCoefficient : ℂ := deriv inverseF 0

noncomputable def specialLeadingMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) : Fin N → ℂ := fun j => (inverseLinearCoefficient*complexRow A j z)^m

noncomputable def specialLeadingPolynomial (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) : MvPolynomial (Fin n) ℂ :=
  (∑ i, MvPolynomial.C (inverseLinearCoefficient*(A j i : ℂ))*MvPolynomial.X i)^m

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_StripRankGeometry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

/-- The complexification of the real strip matrix, in real pair coordinates. -/
def stripCoordinateLinear (A : J → I → ℝ) :
    ((I → ℝ) × (I → ℝ)) →ₗ[ℝ] (J → ℂ) where
  toFun := stripCoordinate A
  map_add' z w := by
    ext j ; simp [stripCoordinate, measurement, mul_add, sum_add_distrib] ; ring
  map_smul' c z := by
    ext j ; simp [stripCoordinate, measurement, Finset.mul_sum, mul_left_comm, mul_comm]

omit fintypeJ in
@[simp] lemma stripCoordinate_zero [Fintype J] (A : J → I → ℝ) : stripCoordinate A 0 = 0 := by
  ext j ; simp [stripCoordinate, measurement]

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SpecialMassHypotheses
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

/-- Squared Euclidean norm of the actual holomorphic vector, in coordinates. -/
noncomputable def specialTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) : ℝ :=
  ∑ j, ‖specialMap A m z j‖^2

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_EuclideanSpecialMap
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
variable {n N : ℕ}

noncomputable def euclideanCoordinates : Mahler.ComplexEuclidean n ≃L[ℂ] (Fin n → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)

noncomputable def euclideanStripDomain (A : Matrix (Fin N) (Fin n) ℝ) :
    Set (Mahler.ComplexEuclidean n) := euclideanCoordinates ⁻¹' complexStripDomain A

noncomputable def euclideanSpecialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) (z : Mahler.ComplexEuclidean n) : ℂ :=
  specialMap A m (euclideanCoordinates z) j

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_InverseRadialRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Complex Set Metric
namespace MahlerConformal

def inverseRadiusRadialSlope (u : ℂ) : ℝ :=
  2 * (u.re * (inverseF u * deriv F (inverseF u)).re +
    u.im * (inverseF u * deriv F (inverseF u)).im) / ‖deriv F (inverseF u)‖^2

@[simp] lemma inverseRadiusRadialSlope_zero : inverseRadiusRadialSlope 0 = 0 := by
  simp [inverseRadiusRadialSlope]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_StripRegularValues
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular positive levels of the literal strip tau. This specializes the
regular-value step to the actual conformal map; it is not a general Sard theorem. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

def stripTauRadialSlope (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) : ℝ :=
  ∑ j, (m : ℝ) * Complex.normSq (inverseF (stripCoordinate A z j)) ^ (m-1) *
    inverseRadiusRadialSlope (stripCoordinate A z j)

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_StripMassExhaustion
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit regular-level exhaustion and
continuity from below for arbitrary nonnegative mass densities. -/
noncomputable section
namespace SymmetricMahler
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {I J : Type*} [Fintype I] [Fintype J]

def stripRegularLevel (k : ℕ) : ℝ := 1 - (1/2 : ℝ) * (1/2 : ℝ)^k

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_EuclideanRegularLevels
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Filter
open scoped Topology
variable {n N : ℕ}

noncomputable def euclideanRealCoordinates : Mahler.ComplexEuclidean n ≃L[ℝ]
    ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).trans complexRealEquiv

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereTransport
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric
open scoped Pointwise
namespace MahlerStokes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual restriction of a real linear isometry to the unit sphere. -/
def sphereIsometry (e : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 := by
  refine { toEquiv := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact {
      toFun := fun x => ⟨e (x : E), by simpa only [mem_sphere, dist_zero_right, e.norm_map] using x.property⟩
      invFun := fun y => ⟨e.symm (y : F), by simpa only [mem_sphere, dist_zero_right, e.symm.norm_map] using y.property⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  · exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  · exact (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExactFormCoordinates
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff
namespace Mahler

/-- Coordinates in the positively oriented orthonormal frame already used by sphereFlux. -/
def fluxCoordinates (k : ℕ) :
    (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean (k+1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((2*k+1)+1) => ℝ)).symm.trans
    (sphereFrame k).repr.symm.toContinuousLinearEquiv

/-- Real-part projection on continuous forms, as a continuous linear map. -/
def realFormCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℕ) :
    (E [⋀^Fin q]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℝ (Fin q) Complex.reCLM

@[simp] lemma realFormCLM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} (a : E [⋀^Fin q]→L[ℝ] ℂ) (v : Fin q → E) :
    realFormCLM E q a v = (a v).re := rfl

/-- The actual real coordinate form, with the same ordered slots as eta. -/
def fluxPullback {k q : ℕ}
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ)
    (x : Fin ((2*k+1)+1) → ℝ) :
    (Fin ((2*k+1)+1) → ℝ) [⋀^Fin q]→L[ℝ] ℝ :=
  realFormCLM _ q ((eta (fluxCoordinates k x)).compContinuousLinearMap
    (fluxCoordinates k).toContinuousLinearMap)

end Mahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorAlternatization
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Equiv Fin
namespace Mahler
noncomputable section

/-- Insert the distinguished derivative slot at p, preserving the order of
all remaining slots before applying their permutation. -/
def orderedInsertPermutation {n : ℕ} (p : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n+1)) :=
  (Equiv.Perm.decomposeFin.symm (0, σ)).trans p.cycleRange.symm

@[simp] lemma orderedInsertPermutation_zero {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) : orderedInsertPermutation p σ 0 = p := by
  simp [orderedInsertPermutation]

@[simp] lemma orderedInsertPermutation_succ {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    orderedInsertPermutation p σ i.succ = p.succAbove (σ i) := by
  simp [orderedInsertPermutation, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fin.cycleRange_symm_succ]

/-- An order-preserving decomposition of every permutation into its first
image and a permutation of the remaining slots. -/
def orderedPermutationEquiv (n : ℕ) :
    (Fin (n+1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n+1)) where
  toFun q := orderedInsertPermutation q.1 q.2
  invFun σ := (σ 0, (Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange)).2)
  left_inv := by
    rintro ⟨p,σ⟩
    simp only [orderedInsertPermutation_zero]
    have he : (orderedInsertPermutation p σ).trans p.cycleRange =
        Equiv.Perm.decomposeFin.symm (0,σ) := by
      ext i
      simp [orderedInsertPermutation]
    rw [he]
    simp
  right_inv := by
    intro σ
    have hz : (Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange)).1 = 0 := by
      simp [Equiv.Perm.decomposeFin]
    have he : Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange) =
        (0, (Equiv.Perm.decomposeFin (σ.trans (σ 0).cycleRange)).2) :=
      Prod.ext hz rfl
    have hi := congrArg Equiv.Perm.decomposeFin.symm he
    simp only [Equiv.symm_apply_apply] at hi
    dsimp only
    unfold orderedInsertPermutation
    rw [← hi]
    ext i
    simp

@[simp] lemma orderedPermutationEquiv_apply (n : ℕ)
    (p : Fin (n+1) × Equiv.Perm (Fin n)) :
    orderedPermutationEquiv n p = orderedInsertPermutation p.1 p.2 := rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def rawUncurry {n : ℕ} (D : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    MultilinearMap ℝ (fun _ : Fin (n+1) => E) ℂ :=
  LinearMap.uncurryLeft
    { toFun := fun v => (D v).toMultilinearMap
      map_add' := fun _ _ => by ext w; simp
      map_smul' := fun _ _ => by ext w; simp }

@[simp] lemma rawUncurry_apply {n : ℕ} (D : E →ₗ[ℝ] E [⋀^Fin n]→ₗ[ℝ] ℂ)
    (v : Fin (n+1) → E) : rawUncurry D v = D (v 0) (fun i => v i.succ) := rfl

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_FiniteStripReduction
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ENNReal
variable {n N : ℕ}

def StripMassBound (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) : Prop :=
  ENNReal.ofReal ((Real.pi*(m : ℝ))^n/(Nat.factorial n : ℝ)) ≤
    ∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HemisphereChart
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma chord_sq {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    (chord 1 y)^2 = 1 - radiusSq y := by
  simp only [chord, one_pow]
  apply Real.sq_sqrt
  have h : radiusSq y < 1 := by simpa [coordBall] using hy
  linarith

/-- Upper hemisphere graph, in the precise coordinate order used by Stokes. -/
def hemisphereGraph {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  i.insertNth (chord 1 y) y

lemma radiusSq_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) : radiusSq (hemisphereGraph i y) = 1 := by
  rw [hemisphereGraph, radiusSq_insertNth, chord_sq hy]
  ring

/-- Radial coordinates on the open upper half-ball. The i-th domain
coordinate is radius; all remaining coordinates parametrize the hemisphere. -/
def hemisphereCone {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  x i • hemisphereGraph i (i.removeNth x)

def hemisphereConeDomain {n : ℕ} (i : Fin (n+1)) : Set (Fin (n+1) → ℝ) :=
  {x | x i ∈ Ioo (0 : ℝ) 1 ∧ i.removeNth x ∈ coordBall n 1}

/-- Real dot product as a continuous linear functional on coordinate space. -/
def coordinateDot {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, y j • ContinuousLinearMap.proj j

def chordDerivative {n : ℕ} (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  -(chord 1 y)⁻¹ • coordinateDot y

/-- Derivative of the hemisphere graph. -/
def hemisphereGraphDerivative {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (i.insertNth (chordDerivative y) (fun j => ContinuousLinearMap.proj j))

def removeCoordinate {n : ℕ} (i : Fin (n+1)) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (i.succAbove j))

def hemisphereConeDerivative {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (Fin (n+1) → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  x i • (hemisphereGraphDerivative i (i.removeNth x)).comp (removeCoordinate i) +
    (ContinuousLinearMap.proj i).smulRight (hemisphereGraph i (i.removeNth x))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HemisphereJacobian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

/-- Move the distinguished coordinate first without changing the relative
order of any other coordinates. The same reindexing is used on both matrix axes. -/
def splitCoordinate {n : ℕ} (i : Fin (n+1)) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  Equiv.ofBijective (Sum.elim (fun _ => i) i.succAbove) (by
    constructor
    · intro a b h
      rcases a with a | a <;> rcases b with b | b
      · congr 1; exact Subsingleton.elim _ _
      · exact (i.succAbove_ne b h.symm).elim
      · exact (i.succAbove_ne a h).elim
      · exact congrArg Sum.inr (i.succAbove_right_injective h)
    · rw [Function.Surjective, i.forall_iff_succAbove]
      exact ⟨⟨Sum.inl 0, rfl⟩, fun j => ⟨Sum.inr j, rfl⟩⟩)

def hemisphereFrameMatrix {n : ℕ} (y : Fin n → ℝ) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (fun _ _ => chord 1 y) (fun _ j => -(chord 1 y)⁻¹ * y j)
    (fun j _ => y j) 1

@[simp] lemma splitCoordinate_inl {n : ℕ} (i : Fin (n+1)) (index : Fin 1) :
    splitCoordinate i (Sum.inl index) = i := rfl

@[simp] lemma splitCoordinate_inr {n : ℕ} (i : Fin (n+1)) (index : Fin n) :
    splitCoordinate i (Sum.inr index) = i.succAbove index := rfl

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HemisphereMeasure
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace MahlerStokes

def coneStrip {n : ℕ} (i : Fin (n+1)) (S : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) :=
  {x | x i ∈ Ioo (0 : ℝ) 1 ∧ i.removeNth x ∈ S}

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HemisphereArea
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
open scoped ENNReal Pointwise
namespace MahlerStokes

/-- The upper hemisphere parametrization into the actual Euclidean unit sphere. -/
def hemisphereParam {n : ℕ} (i : Fin (n+1)) :
    coordBall n 1 → sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := fun y =>
  ⟨toLp 2 (hemisphereGraph i y), by
    simp only [mem_sphere, dist_zero_right]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← radiusSq_eq_euclidean_norm_sq, radiusSq_hemisphereGraph i y.property, one_pow]⟩

/-- Actual Euclidean hemisphere area in graph coordinates. -/
def hemisphereParameterArea (n : ℕ) : Measure (coordBall n 1) :=
  (volume.comap Subtype.val).withDensity
    (fun y => ENNReal.ofReal (chord 1 (y : Fin n → ℝ))⁻¹)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogScalarJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology

namespace SymmetricMahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def logD (t : ℝ) (A : E →L[ℝ] ℝ) := t⁻¹ • A

def logD2 (t : ℝ) (A : E →L[ℝ] ℝ) (B : E →L[ℝ] (E →L[ℝ] ℝ)) :=
  t⁻¹ • B + (-(t^2)⁻¹ • A).smulRight A

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E] [NormedSpace ℝ E]
    [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- Real or imaginary projection of a complex first derivative. -/
def projectD (p : ℂ →L[ℝ] ℝ) : (E →L[ℂ] ℂ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (compL ℝ E ℂ ℝ p).comp (restrictScalarsL ℂ E ℂ ℝ ℝ)

/-- Explicit restriction in both arguments of a nested complex derivative. -/
def projectD2 (p : ℂ →L[ℝ] ℝ) (B : E →L[ℂ] (E →L[ℂ] ℂ)) :
    E →L[ℝ] (E →L[ℝ] ℝ) := (projectD p).comp (B.restrictScalars ℝ)

/-- The square and its first two derivatives, with the second derivative
as an iterated continuous real linear map. -/
def squareD (v : ℝ) (A : E →L[ℝ] ℝ) := (2*v) • A

def squareD2 (v : ℝ) (A : E →L[ℝ] ℝ) (B : E →L[ℝ] (E →L[ℝ] ℝ)) :=
  (2*v) • B + ((2 : ℝ) • A).smulRight A

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_NormSquareJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype J]

abbrev ComplexTwoJet (E J : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  (J → ℂ) × (J → E →L[ℂ] ℂ) × (J → E →L[ℂ] (E →L[ℂ] ℂ))

def sumNormSq (v : J → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

def sumNormSqD (v : J → ℂ) (A : J → E →L[ℂ] ℂ) : E →L[ℝ] ℝ :=
  ∑ j, (squareD (v j).re (projectD Complex.reCLM (A j)) +
    squareD (v j).im (projectD Complex.imCLM (A j)))

def sumNormSqD2 (v : J → ℂ) (A : J → E →L[ℂ] ℂ)
    (B : J → E →L[ℂ] (E →L[ℂ] ℂ)) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∑ j, (squareD2 (v j).re (projectD Complex.reCLM (A j)) (projectD2 Complex.reCLM (B j)) +
    squareD2 (v j).im (projectD Complex.imCLM (A j)) (projectD2 Complex.imCLM (B j)))

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogNormSquare
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology

namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [normedSpaceRealE : NormedSpace ℝ E]
    [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E] [fintypeJ : Fintype J]

def actualComplexTwoJet (f : J → E → ℂ) (x : E) : ComplexTwoJet E J :=
  ((fun j => f j x), (fun j => fderiv ℂ (f j) x),
    (fun j => fderiv ℂ (fderiv ℂ (f j)) x))

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HolomorphicLogC2
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype J]

/-- A fixed closed annulus containing the unit sphere in its interior. -/
def logCompactAnnulus (n : ℕ) : Set (EuclideanSpace ℂ (Fin n)) :=
  closedBall 0 2 \ ball 0 (1/2)

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PrimitiveRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped TensorProduct

noncomputable section
namespace Mahler
variable {E X J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Continuous form for a fixed basis covector determinant. -/
def basisVolumeContinuous (b : Module.Basis J ℝ E) (q : ι → J) :
    E [⋀^ι]→L[ℝ] ℂ :=
  ((ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℂ).compContinuousLinearMap
    (fun i => { complexCoord b (q i) with
      cont := (complexCoord b (q i)).continuous_of_finiteDimensional })).alternatization

/-- Bundle an actual finite-dimensional form using its exact normalized basis
expansion. Forgetting continuity returns the original form. -/
def bundleFiniteForm (b : Module.Basis J ℝ E) (a : E [⋀^ι]→ₗ[ℝ] ℂ) :
    E [⋀^ι]→L[ℝ] ℂ :=
  ∑ q : ι → J, (a (b ∘ q) / (Fintype.card ι).factorial) • basisVolumeContinuous b q

end Mahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology BigOperators

namespace Mahler

/-- Reassociate the two leading real slots to preserve the interleaved order. -/
def sphereFrameSlots (k : ℕ) :
    Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k) ≃ WedgePowerSlots (k+1) where
  toFun s := match s with
    | .inl _ => .inl 0
    | .inr (.inl _) => .inl 1
    | .inr (.inr j) => .inr j
  invFun s := match s with
    | .inl i => if i = 0 then .inl 0 else .inr (.inl 0)
    | .inr j => .inr (.inr j)
  left_inv := by intro s; rcases s with i | (i | j) <;> simp; all_goals fin_cases i ; rfl
  right_inv := by intro s; rcases s with i | j; fin_cases i <;> rfl; rfl

/-- The positive frame is exactly x_1,y_1,...,x_n,y_n. -/
noncomputable def sphereFluxFrame (k : ℕ) :
    Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k) → ComplexEuclidean (k+1) :=
  interleavedBasis ∘ sphereFrameSlots k

/-- The real metric dual of the outward unit normal, with complex-valued output. -/
noncomputable def sphereNormal {n : ℕ} (z : ComplexEuclidean n) :
    ComplexEuclidean n [⋀^Fin 1]→ₗ[ℝ] ℂ :=
  (oneForm (fun _ => Complex.ofRealCLM.comp (innerSL ℝ z)) z).toAlternatingMap

/-- Surface density of a top degree form: evaluate normal^flat wedge omega
on the positively oriented Euclidean coordinate frame. -/
noncomputable def sphereDensity (k : ℕ) (z : ComplexEuclidean (k+1))
    (a : ComplexEuclidean (k+1) [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ) : ℂ :=
  wedge (sphereNormal z) a (sphereFluxFrame k)

noncomputable def sphereJetDensity (k : ℕ)
    (p : ComplexEuclidean (k+1) × RealComplexTwoJet (ComplexEuclidean (k+1))) : ℂ :=
  sphereDensity k p.1 (boundaryJet p.2 k)

/-- Actual complex Bochner integral against Euclidean unit-sphere area. -/
noncomputable def unitSphereFlux (k : ℕ) (u : ComplexEuclidean (k+1) → ℂ) : ℂ :=
  ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
    sphereDensity k z (boundaryForm u k z) ∂sphereArea (k+1)

/-- Radius-r sphere flux in the positive radial parametrization. The surface
Jacobian is r^(2k+1); the normal is z, directed out of the ball. -/
noncomputable def smallSphereFlux (k : ℕ) (u : ComplexEuclidean (k+1) → ℂ) (r : ℝ) : ℂ :=
  ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
    (r : ℂ)^(2*k+1) * sphereDensity k z (boundaryForm u k (r • (z : ComplexEuclidean (k+1))))
      ∂sphereArea (k+1)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousPrimitiveRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set

noncomputable section
namespace Mahler

/-- The order alpha, beta, followed by k ordered d-alpha factors. -/
def sourcePrimitiveSlots (k : ℕ) :
    (Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k)) ≃ Fin (2*(k+1)) :=
  (sphereFrameSlots k).trans (powerFinEquiv (k+1))

def sourcePrimitiveFin {k : ℕ}
    (a b : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+2)) :
    ComplexEuclidean (k+2) [⋀^Fin (2*(k+1))]→ₗ[ℝ] ℂ :=
  (wedge (oneForm a x).toAlternatingMap
    (wedge (oneForm b x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k))).domDomCongr
        (sourcePrimitiveSlots k)

/-- The literal homogeneous primitive, continuously bundled by exact finite
basis expansion. No exterior differentiation identity is assumed here. -/
def sourceHomogeneousPrimitive {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ)
    (x : ComplexEuclidean (k+2)) :
    ComplexEuclidean (k+2) [⋀^Fin (2*(k+1))]→L[ℝ] ℂ :=
  bundleFiniteForm (sphereFrame (k+1)).toBasis
    (sourcePrimitiveFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x)

end Mahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousVariationCoefficient
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler

/-- The residual with one explicit d beta factor and no suppressed placements.
The intermediate slot type keeps the original recursive order. -/
noncomputable def boundarySingleResidualFin {k : ℕ}
    (a b : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+2)) :
    ComplexEuclidean (k+2) [⋀^Fin (2*(k+1)+1)]→ₗ[ℝ] ℂ :=
  let B : ComplexEuclidean (k+2) [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ :=
    wedge (extDeriv (oneForm b) x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k)
  (wedge (oneForm a x).toAlternatingMap B).domDomCongr (boundaryFinEquiv (k+1))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PairTransgression
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The actual ordered two-form alpha wedge beta, as a continuous form. -/
noncomputable def pairExterior (a b : E →L[ℝ] ℂ) : E [⋀^Fin 2]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
      (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.mul ℝ ℂ).bilinearComp a b))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PowerTransgression
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

/-- The ordered primitive alpha wedge beta wedge (d alpha)^k. -/
noncomputable def powerTransgressionPrimitive (basis : Module.Basis J ℝ E)
    (a b : E → E →L[ℝ] ℂ) (k : ℕ) (x : E) : E [⋀^Fin (2*(k+1))]→L[ℝ] ℂ :=
  continuousReindex (finCongr (by omega))
    (continuousWedgeFin basis (pairExterior (a x) (b x))
      (basisContinuousWedgePower basis (extDeriv (oneForm a) x) k))

def primitiveFinEquiv (k : ℕ) :
    (Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k)) ≃ Fin (2*(k+1)) :=
  (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k)).symm.trans
    (((prependFinEquiv 1).sumCongr (powerFinEquiv k)).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousTransgression
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler

/-- The transgression primitive in every complex dimension k+2. -/
noncomputable def homogeneousPrimitive {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ) :=
  powerTransgressionPrimitive (sphereFrame (k+1)).toBasis
    (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
    (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) k

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularChartStokes
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- Actual oriented boundary-chart integral in the level coordinates. -/
def chartBoundaryFlux {n : ℕ}
    (e : OpenPartialHomeomorph (Fin (n+1) → ℝ) (Fin (n+1) → ℝ))
    (k : Fin (n+1)) (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  (-1 : ℝ)^k.val * ∫ y : Fin n → ℝ,
    extendedChartForm e ω (k.insertNth R y) (k.removeNth (coordinateBasis (n+1)))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LevelFace
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

def coordinateFace {n : ℕ} (k : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  k.insertNth R y

def faceLinear {n : ℕ} (k : Fin (n+1)) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (k.insertNth (0 : (Fin n → ℝ) →L[ℝ] ℝ)
    (fun j : Fin n => ContinuousLinearMap.proj j))

namespace RegularBoundaryPatch
variable {n : ℕ} {U : Set (Fin (n+1) → ℝ)} {g : (Fin (n+1) → ℝ) → ℝ}

def faceParam (p : RegularBoundaryPatch (n+1) U g) (R : ℝ) (y : Fin n → ℝ) :=
  p.chart.symm (coordinateFace p.coordinate R y)

def faceDomain (p : RegularBoundaryPatch (n+1) U g) (R : ℝ) : Set (Fin n → ℝ) :=
  (coordinateFace p.coordinate R) ⁻¹' (p.chart.target ∩ p.chart.symm ⁻¹' p.domain)

end RegularBoundaryPatch

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereFluxLimit
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler

noncomputable def actualRealComplexJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℂ) (x : E) : RealComplexTwoJet E :=
  (fderiv ℝ u x, fderiv ℝ (fderiv ℝ u) x)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogDilation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The rescaling epsilon^(-2m) tau(epsilon z), followed by log. -/
noncomputable def rescaledLog (τ : E → ℝ) (m : ℕ) (r : ℝ) (x : E) : ℂ :=
  (Real.log ((r^(2*m))⁻¹ * τ (r • x)) : ℂ)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MassLimit
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
open Set MeasureTheory Filter
open scoped Topology ENNReal
variable {n N : ℕ}

noncomputable def massBelow (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U ∩ {z | tau f z < R}, ENNReal.ofReal (massDensity f z)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MatrixExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

def pairSplitEquiv (n : ℕ) : WedgePowerSlots n ≃ Fin n ⊕ Fin n :=
  (pairSlotEquiv n).trans
    { toFun := fun p => if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
      invFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
      left_inv := by rintro ⟨i,j⟩; fin_cases j <;> simp
      right_inv := by intro s; cases s <;> simp }

/-- The complex-coordinate coefficient matrix, in split real/imaginary order. -/
noncomputable def hessianCovectorMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 1 (I • 1) H ((-I) • H)

noncomputable def splitCoordinates (n : ℕ) : (Fin n ⊕ Fin n) → ComplexEuclidean n →ₗ[ℝ] ℂ :=
  Sum.elim realCoordinate imagCoordinate

/-- Coordinate two-form associated with a complex Hessian. This is the
standard (i/2) sum H_ij dz_i wedge dbar(z_j), represented by covectors. -/
noncomputable def hessianPair {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Fin 2 → ComplexEuclidean n →ₗ[ℝ] ℂ :=
  ![realCoordinate i + I • imagCoordinate i,
    ∑ j, H i j • (realCoordinate j - I • imagCoordinate j)]

noncomputable def matrixTwoForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    ComplexEuclidean n [⋀^Fin 2]→ₗ[ℝ] ℂ :=
  (I/2) • ∑ i, covectorVolume (hessianPair H i)

noncomputable def matrixPairing {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (w v : ComplexEuclidean n) : ℂ := ∑ i, ∑ j, v i * star (w j) * H i j

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OpenExteriorNormalization
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

noncomputable def coordinateDirection {n : ℕ} (i : Fin n) : ComplexEuclidean n :=
  EuclideanSpace.single i 1

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PunctureCutoff
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- The sphere integral uses the outward orientation from the ball. -/
def sphereFlux {n : ℕ} (r : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin (n+1), (-1 : ℝ)^i.val * ∫ y in coordBall n r,
    ω (i.insertNth (chord r y) y) (i.removeNth (coordinateBasis (n+1))) -
      ω (i.insertNth (-chord r y) y) (i.removeNth (coordinateBasis (n+1)))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Tensor product of scalar multilinear forms before alternatization. -/
def rawProduct (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    MultilinearMap ℝ (fun _ : ι ⊕ κ => E) ℂ :=
  (LinearMap.mul' ℝ ℂ).compMultilinearMap (a.domCoprod b)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma rawProduct_apply [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) (v : ι ⊕ κ → E) :
    rawProduct a b v = a (fun i => v (Sum.inl i)) * b (fun i => v (Sum.inr i)) := rfl

/-- The raw ordered product of k bilinear factors. -/
def rawPower (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) :
    (k : ℕ) → MultilinearMap ℝ (fun _ : WedgePowerSlots k => E) ℂ
  | 0 => MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℂ)
  | k+1 => rawProduct B (rawPower B k)

def rawCovector (a : E →ₗ[ℝ] ℂ) : MultilinearMap ℝ (fun _ : Fin 1 => E) ℂ :=
  MultilinearMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) a

@[simp] lemma rawCovector_apply (a : E →ₗ[ℝ] ℂ) (v : Fin 1 → E) : rawCovector a v = a (v 0) := rfl

def rawBoundary (a : E →ₗ[ℝ] ℂ) (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) (k : ℕ) :
    MultilinearMap ℝ (fun _ : Fin 1 ⊕ WedgePowerSlots k => E) ℂ :=
  rawProduct (rawCovector a) (rawPower B k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawClosedProduct
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

@[simp] lemma raw_wedge_zero_left (b : E [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (0 : E [⋀^ι]→ₗ[ℝ] ℂ) b = 0 := by
  simpa only [zero_smul] using wedge_smul_left (0 : ℂ) (0 : E [⋀^ι]→ₗ[ℝ] ℂ) b

@[simp] lemma raw_wedge_zero_right (a : E [⋀^ι]→ₗ[ℝ] ℂ) :
    wedge a (0 : E [⋀^κ]→ₗ[ℝ] ℂ) = 0 := by
  simpa only [zero_smul] using wedge_smul_right (0 : ℂ) a (0 : E [⋀^κ]→ₗ[ℝ] ℂ)

/-- Adjoin the actual directional derivative as the first raw slot. -/
def rawPrefix (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) :
    MultilinearMap ℝ (fun _ : Fin 1 ⊕ ι => E) ℂ :=
  (MultilinearMap.ofSubsingleton ℝ E _ (0 : Fin 1) D).uncurrySum

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma rawPrefix_apply [Fintype ι] [DecidableEq ι] (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (v : Fin 1 ⊕ ι → E) :
    rawPrefix D v = D (v (Sum.inl 0)) (fun i => v (Sum.inr i)) := rfl

def rawProductVariation (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (Da : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ)
    (Db : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι ⊕ κ => E) ℂ where
  toFun v := rawProduct (Da v) b + rawProduct a (Db v)
  map_add' v w := by ext z; simp [rawProduct_apply]; ring
  map_smul' r v := by ext z; simp [rawProduct_apply]; ring

/-- Move a distinguished derivative slot past the left factor without
changing the order within either factor. -/
def rawMoveDerivative (ι κ : Type*) : ι ⊕ (Fin 1 ⊕ κ) ≃ Fin 1 ⊕ (ι ⊕ κ) :=
  (Equiv.sumAssoc ι (Fin 1) κ).symm |>.trans
    ((Equiv.sumCongr (Equiv.sumComm ι (Fin 1)) (Equiv.refl κ)).trans
      (Equiv.sumAssoc (Fin 1) ι κ))

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawClosedPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def rawPowerVariation (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ)
    (DB : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) :
    (k : ℕ) → E →ₗ[ℝ] MultilinearMap ℝ (fun _ : WedgePowerSlots k => E) ℂ
  | 0 => 0
  | k+1 => rawProductVariation B DB (rawPower B k) (rawPowerVariation B DB k)

/-- The uncurried derivative of a covector field, before alternation. -/
def rawCovectorVariation (Da : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 1 => E) ℂ where
  toFun v := rawCovector (Da v)
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawCoefficientDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rawCoefficientDerivative (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (v : ι → E) : E →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
  { toFun w := D w v
    map_add' w z := by simp
    map_smul' r w := by simp }

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma rawCoefficientDerivative_apply [Fintype ι] [DecidableEq ι]
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (v : ι → E) (w : E) :
    rawCoefficientDerivative D v w = D w v := rfl

/-- A coefficientwise derivative records actual HasFDerivAt proofs for
all tuples. It adds no differentiability or exterior-calculus assumptions. -/
def HasRawFDerivAt (a : E → MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (x : E) : Prop :=
  ∀ v, HasFDerivAt (fun y => a y v) (rawCoefficientDerivative D v) x

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawAlternationDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def rawAlternatedCoefficientDerivative
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) (v : ι → E) : E →L[ℝ] ℂ :=
  ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • rawCoefficientDerivative D (v ∘ σ)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RawReindexedDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative slot is numbered zero; all old slots follow in order. -/
def rawFrontFin (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n+1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))

@[simp] lemma rawFrontFin_inl (n : ℕ) (i : Fin 1) : rawFrontFin n (Sum.inl i) = 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

@[simp] lemma rawFrontFin_inr {n : ℕ} (i : Fin n) :
    rawFrontFin n (Sum.inr i) = i.succ := by
  apply Fin.ext
  simp [rawFrontFin]

def rawReindexDerivative {n : ℕ} (e : ι ≃ Fin n)
    (D : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : ι => E) ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => E) ℂ where
  toFun w := (D w).domDomCongr e
  map_add' w z := by ext v; simp [MultilinearMap.domDomCongr_apply]
  map_smul' r w := by ext v; simp [MultilinearMap.domDomCongr_apply]

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RescaledHolomorphic
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

noncomputable def rescale (f : E → ℂ) (m : ℕ) (ε : ℝ) (z : E) : ℂ :=
  (ε^m)⁻¹ • f (ε • z)

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RescaledMassMap
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology
variable {n N m : ℕ}

noncomputable def leadingComponent (G : Fin N → MvPolynomial (Fin n) ℂ)
    (j : Fin N) (z : Mahler.ComplexEuclidean n) : ℂ :=
  MvPolynomial.eval (fun i => z i) (G j)

noncomputable def taylorRemainder (f : Fin N → Mahler.ComplexEuclidean n → ℂ)
    (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N) (z : Mahler.ComplexEuclidean n) : ℂ :=
  f j z - leadingComponent G j z

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceLogC2
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology
namespace MahlerRescaling
noncomputable section
variable {n N m : ℕ} {U : Set (Mahler.ComplexEuclidean n)}
  {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
  {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The exact logarithm in the rescaled mass argument. -/
def rescaledLogEnergy (f : Fin N → Mahler.ComplexEuclidean n → ℂ) (m : ℕ)
    (ε : ℝ) (z : Mahler.ComplexEuclidean n) : ℝ :=
  Real.log (∑ j, Complex.normSq (rescale (f j) m ε z))

def leadingLogEnergy (G : Fin N → MvPolynomial (Fin n) ℂ)
    (z : Mahler.ComplexEuclidean n) : ℝ :=
  Real.log (∑ j, Complex.normSq (leadingComponent G j z))

end
end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceSphereLimit
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler

/-- A fixed closed annulus about the unit sphere. -/
def sphereAnnulus (n : ℕ) : Set (ComplexEuclidean n) :=
  closedBall 0 2 ∩ {z | (1/2 : ℝ) ≤ ‖z‖}

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RealLogBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Filter Set
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def complexifyDerivative : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℂ) :=
  ContinuousLinearMap.compL ℝ E ℝ ℂ Complex.ofRealCLM
noncomputable def complexifySecondDerivative :
    (E →L[ℝ] (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℂ)) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℂ) complexifyDerivative

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SpecialJacobian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set Finset
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

noncomputable def specialRowFactor (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) (j : Fin N) : ℂ :=
  (m : ℂ)*inverseF (complexRow A j z)^(m-1)*deriv inverseF (complexRow A j z)

noncomputable def specialDerivative (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun j => specialRowFactor A m z j • complexRow A j

noncomputable def specialJacobianMatrix (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) : Matrix (Fin N) (Fin n) ℂ := fun j k => specialRowFactor A m z j*(A j k : ℂ)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SpecialMassBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set Filter Finset MeasureTheory
open scoped Topology ENNReal
open MahlerConformal
variable {n N : ℕ}

/-- Real determinant of the actual holomorphic derivative's Hermitian Gram matrix. -/
noncomputable def specialGramDet (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) : ℝ :=
  ((specialJacobianMatrix A m z).conjTranspose * specialJacobianMatrix A m z).det.re

noncomputable def specialSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) : Set (Fin n → ℂ) :=
  {z | z ∈ complexStripDomain A ∧ specialTau A m z < 1}

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RegularMassReduction
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set MeasureTheory

/-- The regular-level mass bound for the finite-strip map. -/
def SpecialRegularMassBound {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (m k : ℕ) : Prop :=
  ENNReal.ofReal ((stripRegularLevel k)^n * (Real.pi*(m : ℝ))^n) ≤
    Mahler.massBelow (euclideanStripDomain A) (euclideanSpecialMap A m) (stripRegularLevel k)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceLevelFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The finite shuffle form used in both Stokes equations. -/
def sourceBoundaryForm (u : ComplexEuclidean n → ℂ) (k : ℕ) (x : ComplexEuclidean n) :
    ComplexEuclidean n [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ :=
  wedge (oneForm (dcLinear u) x).toAlternatingMap
    (wedgePower (extDeriv (oneForm (dcLinear u)) x).toAlternatingMap k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceFluxRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- Linear jet operator for the normalization -D(u)(iv)/4. -/
def sourceDCOperator : (E →L[ℝ] ℂ) →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℂ :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((-1/4 : ℂ) • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure)

/-- The recursive shuffle power as a continuous form. -/
def continuousWedgePower (a : E [⋀^Fin 2]→L[ℝ] ℂ) :
    (k : ℕ) → E [⋀^WedgePowerSlots k]→L[ℝ] ℂ
  | 0 => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | k+1 => continuousWedge a (continuousWedgePower a k)

def continuousSourceBoundaryForm (u : E → ℂ) (k : ℕ) (x : E) :
    E [⋀^Fin 1 ⊕ WedgePowerSlots k]→L[ℝ] ℂ :=
  continuousWedge (oneForm (dcLinear u) x)
    (continuousWedgePower (extDeriv (oneForm (dcLinear u)) x) k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceCoordinateForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Set Filter MeasureTheory
open scoped Topology Manifold

namespace Mahler
noncomputable section

/-- The leading one-form slot precedes the interleaved two-form slots. -/
def sourceBoundarySlots (k : ℕ) : Fin 1 ⊕ WedgePowerSlots k ≃ Fin (2*k+1) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) ((pairSlotEquiv k).trans finProdFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by omega))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def sourceReindex (e : ι ≃ κ) (a : E [⋀^ι]→L[ℝ] ℂ) : E [⋀^κ]→L[ℝ] ℂ :=
  { a.toAlternatingMap.domDomCongr e with
    cont := a.cont.comp (continuous_pi (fun i => continuous_apply (e i))) }

def sourceReindexCLM (e : ι ≃ κ) : (E [⋀^ι]→L[ℝ] ℂ) →L[ℝ] E [⋀^κ]→L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := sourceReindex e
      map_add' := fun _ _ => by ext v; rfl
      map_smul' := fun _ _ => by ext v; rfl }

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def sourceRealBoundaryForm (u : E → ℂ) (k : ℕ) (x : E) :
    E [⋀^Fin (2*k+1)]→L[ℝ] ℝ :=
  Complex.reCLM.compContinuousAlternatingMap
    (sourceReindex (sourceBoundarySlots k) (continuousSourceBoundaryForm u k x))

def sourceCoordinateForm {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] E)
    (u : E → ℂ) (k : ℕ) (x : Fin d → ℝ) :
    (Fin d → ℝ) [⋀^Fin (2*k+1)]→L[ℝ] ℝ :=
  (sourceRealBoundaryForm u k (Ψ x)).compContinuousLinearMap Ψ.toContinuousLinearMap

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereCoordinateIntegral
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- Outward cofactor density in the fixed ordered coordinate basis. The
argument x is the unit normal; r*x is the evaluation point of the form. -/
def coordinateSphereDensity {n : ℕ} (r : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  ∑ i : Fin (n+1), (-1 : ℝ)^i.val * x i *
    ω (r • x) (i.removeNth (coordinateBasis (n+1)))

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRawJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forget continuity only after taking the actual bundled derivative. -/
def rawCovectorJet (A : E →L[ℝ] E →L[ℝ] ℂ) : E →ₗ[ℝ] E [⋀^Fin 1]→ₗ[ℝ] ℂ where
  toFun v := AlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) (A v).toLinearMap
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

def rawFirstJet (A : E →L[ℝ] E →L[ℝ] ℂ) :
    MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ := rawUncurry (rawCovectorJet A)

@[simp] lemma rawFirstJet_apply (A : E →L[ℝ] E →L[ℝ] ℂ) (v : Fin 2 → E) :
    rawFirstJet A v = A (v 0) (v 1) := rfl

def rawSecondJet (H : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ) :
    E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ where
  toFun v := rawFirstJet (H v)
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

@[simp] lemma rawSecondJet_apply (H : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ)
    (v : E) (z : Fin 2 → E) : rawSecondJet H v z = H v (z 0) (z 1) := rfl

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRawCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def rawLinearJet (A : E →L[ℝ] E →L[ℝ] ℂ) : E →ₗ[ℝ] E →ₗ[ℝ] ℂ where
  toFun v := (A v).toLinearMap
  map_add' v w := by ext z; simp
  map_smul' r v := by ext z; simp

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRawOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Explicit order of the differentiated top form: first the two slots
created from derivative and one-form, then all existing interleaved pairs. -/
def sourceTopSlots (k : ℕ) : WedgePowerSlots (k+1) ≃ Fin ((2*k+1)+1) :=
  ((Equiv.sumCongr (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
      (Equiv.refl (WedgePowerSlots k))).symm.trans
    (Equiv.sumAssoc (Fin 1) (Fin 1) (WedgePowerSlots k))).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 1)) (sourceBoundarySlots k)).trans
        (rawFrontFin (2*k+1)))

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceTopCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section

def coordinateCast {a b : ℕ} (h : a = b) : (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) := by
  subst b
  exact ContinuousLinearEquiv.refl ℝ _

def sourceCoordinates (k : ℕ) : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean (k+1) :=
  (coordinateCast (show (2*k+1)+1 = (k+1)*2 by omega)).trans
    (MahlerStokes.complexCoordinates (k+1))

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceFluxCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
namespace Mahler

/-- The bundled complex form, with its specified boundary slot order. -/
def sourceFluxForm {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ)
    (x : ComplexEuclidean (k+1)) :
    ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ :=
  sourceReindex (sourceBoundarySlots k) (continuousSourceBoundaryForm u k x)

end Mahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceFullExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def sourceComplexBoundaryForm (u : E → ℂ) (k : ℕ) (x : E) : E [⋀^Fin (2*k+1)]→L[ℝ] ℂ :=
  sourceReindex (sourceBoundarySlots k) (continuousSourceBoundaryForm u k x)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereAreaTransport
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric Set
open scoped ENNReal

namespace Mahler

/-- Positive dilation sends the unit sphere to the radius-r sphere. -/
noncomputable def sphereDilation {n : ℕ} (r : ℝ) (hr : 0 < r) :
    sphere (0 : ComplexEuclidean n) 1 → sphere (0 : ComplexEuclidean n) r := fun z =>
  ⟨r • (z : ComplexEuclidean n), by
    have hz : ‖(z : ComplexEuclidean n)‖ = 1 := by simp
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz]⟩

/-- Euclidean sphere area at radius r, transported from the volume-induced
unit sphere measure with its positive tangential Jacobian. -/
noncomputable def radiusSphereArea (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Measure (sphere (0 : ComplexEuclidean n) r) :=
  ENNReal.ofReal (r^(2*n-1)) • (sphereArea n).map (sphereDilation r hr)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereOrientation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Set
open scoped Topology

namespace Mahler

/-- Flux on the radius-r sphere itself. For nonpositive radii we use zero;
this branch is irrelevant to the right-sided small-sphere limit. -/
noncomputable def radiusSphereFlux (k : ℕ) (u : ComplexEuclidean (k+1) → ℂ) (r : ℝ) : ℂ :=
  if hr : 0 < r then
    ∫ z : sphere (0 : ComplexEuclidean (k+1)) r,
      sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z)
        ∂radiusSphereArea (k+1) r hr
  else 0

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereDensityBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators TensorProduct
open MeasureTheory Metric

namespace Mahler

def restMap {κ : Type*} (σ : Equiv.Perm (Fin 1 ⊕ κ))
    (h : σ (Sum.inl 0) = Sum.inl 0) (j : κ) : κ :=
  match he : σ (Sum.inr j) with
  | .inl i => False.elim (by
      have hi : i = 0 := Subsingleton.elim _ _
      have hh := σ.injective (he.trans (by simpa [hi] using h.symm))
      cases hh)
  | .inr k => k

/-- Ordered identification of the normal slot and recursive boundary slots. -/
def densityBridgeSlots (k : ℕ) :
    (Fin 1 ⊕ (Fin 1 ⊕ WedgePowerSlots k)) ≃ Fin ((2*k+1)+1) :=
  (sphereFrameSlots k).trans (ambientFinEquiv k)

end Mahler

end OAI
end


