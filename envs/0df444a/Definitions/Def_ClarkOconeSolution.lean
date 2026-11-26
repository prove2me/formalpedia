-- Prove2me | Definitions.Def_ClarkOconeSolution
-- name    : ClarkOconeSolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:49:12.549356+00:00
-- url     : https://prove2.me/theorems/315fdca7-22cd-4fc7-9393-712d833cdc32
-- title:
--   Clark Ocone Solution
-- statement:
--   Definitions and structural lemmas for Clark Ocone Solution, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/ClarkOconeSolution.lean

import Definitions.Def_Malliavin_BrownianClarkOconeCapstone
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
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
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
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
open scoped ENNReal NNReal Real Topology InnerProductSpace
noncomputable section
namespace PalomarClarkOcone
universe u
noncomputable def nonnegativeLebesgueMeasure : Measure ℝ≥0 :=
  Measure.comap ((↑) : ℝ≥0 → ℝ) (volume : Measure ℝ)
abbrev RandomL2 {W : Type u} [MeasurableSpace W] (P : Measure W) := Lp ℝ 2 P
abbrev TimeProcessL2 {W : Type u} [MeasurableSpace W] (P : Measure W) :=
  Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)
noncomputable abbrev PredictableProcessL2
    {W : Type u} [MeasurableSpace W]
    (filtration : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :=
  lpMeas ℝ ℝ filtration.predictable 2 (nonnegativeLebesgueMeasure.prod P)
abbrev processMeasurableSpace {W : Type u} (B : ℝ≥0 → W → ℝ) : MeasurableSpace W :=
  ⨆ t : ℝ≥0, MeasurableSpace.comap (B t) (borel ℝ)
def IsWienerGenerated {W : Type u} [MeasurableSpace W] (B : ℝ≥0 → W → ℝ) : Prop :=
  processMeasurableSpace B = ‹MeasurableSpace W›
noncomputable def expectationL2
    {W : Type u} [MeasurableSpace W] {P : Measure W} [IsFiniteMeasure P]
    (G : RandomL2 P) : RandomL2 P :=
  Lp.const 2 P (∫ w, G w ∂P)
noncomputable def CameronMartin.Space
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : Submodule ℝ (Lp ℝ 2 P) :=
  (StrongDual.toLp P 2 -
    (Lp.constL 2 P ℝ).comp
      (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂P))).range.topologicalClosure
namespace CameronMartin
noncomputable def centeredId
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : W → W :=
  id - fun _ ↦ ∫ x, x ∂P
theorem memLp_centeredId
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : MemLp (centeredId P) 2 P := by
  exact (IsGaussian.memLp_id P 2 (by norm_num)).sub (memLp_const (∫ x, x ∂P))
noncomputable def centeredIdLp
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : Lp W 2 P :=
  (memLp_centeredId P).toLp (centeredId P)
noncomputable def covarianceMap
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : Lp ℝ 2 P →L[ℝ] W :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := W)).lpPairing P 2 2).flip (centeredIdLp P)
noncomputable def inclusion
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : Space P →L[ℝ] W :=
  (covarianceMap P).domRestrict (Space P)
noncomputable def ofDual
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : StrongDual ℝ W →L[ℝ] Space P :=
  (StrongDual.toLp P 2 - (Lp.constL 2 P ℝ).comp
    (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂P))).codRestrict (Space P)
      fun L ↦ Submodule.le_topologicalClosure _ ⟨L, rfl⟩
instance instCompleteSpaceSpace
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] : CompleteSpace (Space P) :=
  inferInstanceAs (CompleteSpace
    ((StrongDual.toLp P 2 -
      (Lp.constL 2 P ℝ).comp
        (ContinuousLinearMap.apply ℝ ℝ (∫ x, x ∂P))).range.topologicalClosure))
end CameronMartin
noncomputable def mderiv
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P] (F : W → ℝ) (x : W) : CameronMartin.Space P :=
  (InnerProductSpace.toDual ℝ (CameronMartin.Space P)).symm
    ((fderiv ℝ F x).comp (CameronMartin.inclusion P))
noncomputable def smulLp
    {W E : Type u} [MeasurableSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {P : Measure W}
    (h : E) : RandomL2 P →L[ℝ] Lp E 2 P :=
  (ContinuousLinearMap.toSpanSingleton ℝ h).compLpL 2 P
structure IsSmoothBounded
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : W → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 F
  bounded : ∃ C, ∀ x, |F x| ≤ C
  bounded_fderiv : ∃ C, ∀ x, ‖fderiv ℝ F x‖ ≤ C
namespace IsSmoothBounded
theorem continuous_fderiv
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : W → ℝ} (hF : IsSmoothBounded F) : Continuous (fderiv ℝ F) :=
  hF.contDiff.continuous_fderiv one_ne_zero
theorem memLp
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {F : W → ℝ} (P : Measure W) [IsGaussian P]
    (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp F p P := by
  obtain ⟨C, hC⟩ := hF.bounded
  exact MemLp.of_bound hF.contDiff.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
theorem continuous_mderiv
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (P : Measure W) [IsGaussian P]
    (hF : IsSmoothBounded F) : Continuous (mderiv P F) := by
  unfold mderiv
  exact (InnerProductSpace.toDual ℝ (CameronMartin.Space P)).symm.continuous.comp
    (hF.continuous_fderiv.clm_comp continuous_const)
theorem exists_norm_mderiv_le
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (P : Measure W) [IsGaussian P]
    (hF : IsSmoothBounded F) : ∃ C, ∀ x, ‖mderiv P F x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hF.bounded_fderiv
  refine ⟨C * ‖CameronMartin.inclusion P‖, fun x ↦ ?_⟩
  unfold mderiv
  rw [LinearIsometryEquiv.norm_map]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hC x) (ContinuousLinearMap.opNorm_nonneg _))
theorem memLp_mderiv
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (P : Measure W) [IsGaussian P]
    (hF : IsSmoothBounded F) (p : ℝ≥0∞) : MemLp (mderiv P F) p P := by
  obtain ⟨C, hC⟩ := hF.exists_norm_mderiv_le P
  exact MemLp.of_bound (hF.continuous_mderiv P).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
noncomputable def toLp
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (P : Measure W) [IsGaussian P]
    (hF : IsSmoothBounded F) : Lp ℝ 2 P :=
  (hF.memLp P 2).toLp F
noncomputable def mderivLp
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {F : W → ℝ} (P : Measure W) [IsGaussian P]
    (hF : IsSmoothBounded F) : Lp (CameronMartin.Space P) 2 P :=
  (hF.memLp_mderiv P 2).toLp (mderiv P F)
end IsSmoothBounded
def InGraphClosure
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (P : Measure W) [IsGaussian P]
    (F : Lp ℝ 2 P) (η : Lp (CameronMartin.Space P) 2 P) : Prop :=
  ∃ Fk : ℕ → {f : W → ℝ // IsSmoothBounded f},
    Tendsto (fun k ↦ (Fk k).2.toLp P) atTop (𝓝 F) ∧
      Tendsto (fun k ↦ (Fk k).2.mderivLp P) atTop (𝓝 η)
theorem predictable_le_prod
    {W : Type u} [MeasurableSpace W]
    (filtration : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    filtration.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (filtration.le 0 A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (filtration.le t A hA)
noncomputable def predictableProjection
    {W : Type u} [MeasurableSpace W] {P : Measure W}
    (filtration : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    TimeProcessL2 P →L[ℝ] PredictableProcessL2 filtration P :=
  condExpL2 ℝ ℝ (predictable_le_prod filtration)
end PalomarClarkOcone


