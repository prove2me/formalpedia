-- Prove2me | Definitions.Def_Malliavin_BrownianCylinderDensity
-- name    : Malliavin_BrownianCylinderDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:51:37.788599+00:00
-- url     : https://prove2.me/theorems/ecfd6827-4a40-4119-8061-5061972a2acb
-- title:
--   Brownian Cylinder Density
-- statement:
--   Definitions and structural lemmas for Brownian Cylinder Density, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_hasGaussianLaw_stepSum
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
section GaussianPolynomial
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure E) [IsGaussian μ]
omit [CompleteSpace E] [SecondCountableTopology E] in
/-- Every natural power of a continuous linear functional on a Gaussian space belongs to
`L²`. -/
theorem memLp_two_dual_pow (L : StrongDual ℝ E) (n : ℕ) :
    MemLp (fun x ↦ L x ^ n) 2 μ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hL : MemLp L (2 * n : ℕ) μ :=
    IsGaussian.memLp_dual μ L (2 * n : ℕ) (ENNReal.natCast_ne_top (2 * n))
  convert hL.integrable_norm_pow' using 1
  funext x
  simp only [Real.norm_eq_abs]
  have hnonneg : 0 ≤ L x ^ (2 * n) := by
    rw [mul_comm, pow_mul]
    positivity
  rw [← abs_pow, abs_of_nonneg hnonneg]
  ring
def gaussianLinearPowerLp (L : StrongDual ℝ E) (n : ℕ) : Lp ℝ 2 μ :=
  (memLp_two_dual_pow μ L n).toLp fun x ↦ L x ^ n
def gaussianPolynomialSpan : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (Set.range fun a : StrongDual ℝ E × ℕ ↦
    gaussianLinearPowerLp μ a.1 a.2)
end GaussianPolynomial
section BrownianPolynomial
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- A natural power of a finite Brownian step sum belongs to `L²(P)`. -/
theorem memLp_two_stepSum_pow (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    MemLp (fun w ↦ stepSum B v w ^ n) 2 P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [memLp_two_iff_integrable_sq
    ((hasGaussianLaw_stepSum hB v).aemeasurable.pow_const n).aestronglyMeasurable]
  have hX : MemLp (stepSum B v) (2 * n : ℕ) P :=
    (hasGaussianLaw_stepSum hB v).memLp (ENNReal.natCast_ne_top (2 * n))
  convert hX.integrable_norm_pow' using 1
  funext w
  simp only [Real.norm_eq_abs]
  have hnonneg : 0 ≤ stepSum B v w ^ (2 * n) := by
    rw [mul_comm, pow_mul]
    positivity
  rw [← abs_pow, abs_of_nonneg hnonneg]
  ring
def brownianStepPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) : RandomL2 P :=
  (memLp_two_stepSum_pow hB v n).toLp fun w ↦ stepSum B v w ^ n
def brownianPolynomialSpan (hB : IsPreBrownianReal B P) :
    Submodule ℝ (RandomL2 P) :=
  Submodule.span ℝ (Set.range fun a : (ℝ≥0 →₀ ℝ) × ℕ ↦
    brownianStepPowerLp hB a.1 a.2)
def brownianProcess (B : ℝ≥0 → W → ℝ) : W → (ℝ≥0 → ℝ) :=
  fun w t ↦ B t w
def brownianCylinderEvents (B : ℝ≥0 → W → ℝ) : Set (Set W) :=
  Set.preimage (brownianProcess B) '' measurableCylinders (fun _ : ℝ≥0 ↦ ℝ)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Brownian cylinders generate the ambient measurable space under `IsWienerGenerated`. -/
theorem ambient_eq_generateFrom_brownianCylinderEvents
    (hgen : IsWienerGenerated B) :
    ‹MeasurableSpace W› = MeasurableSpace.generateFrom (brownianCylinderEvents B) := by
  rw [← hgen]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (B t) (borel ℝ)) = _
  rw [← MeasurableSpace.comap_process_pi,
    ← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
  rfl
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Brownian cylinders are measurable when the process generates the ambient sigma-algebra. -/
theorem measurableSet_brownianCylinderEvents (hgen : IsWienerGenerated B)
    {s : Set W} (hs : s ∈ brownianCylinderEvents B) : MeasurableSet s := by
  rw [ambient_eq_generateFrom_brownianCylinderEvents hgen]
  exact MeasurableSpace.measurableSet_generateFrom hs
def brownianDualCoefficients (I : Finset ℝ≥0)
    (K : StrongDual ℝ (I → ℝ)) : ℝ≥0 →₀ ℝ :=
  (Finsupp.equivFunOnFinite.symm fun i ↦ K (Pi.single i 1)).embDomain
    (Function.Embedding.subtype fun t ↦ t ∈ I)
end BrownianPolynomial
end Malliavin


