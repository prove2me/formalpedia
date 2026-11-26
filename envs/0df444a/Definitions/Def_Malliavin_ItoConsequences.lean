-- Prove2me | Definitions.Def_Malliavin_ItoConsequences
-- name    : Malliavin_ItoConsequences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:44:36.289815+00:00
-- url     : https://prove2.me/theorems/1f2452ec-084a-525a-996e-7362d4cc9298
-- title:
--   Ito Consequences
-- statement:
--   Definitions and structural lemmas for Ito Consequences, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConsequences.lean

import Definitions.Def_Malliavin_ItoConstruction
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_brownianLp_zero
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictable_adaptedOne
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_naturalItoIntegral_elementaryPredictable
import Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.mem_symmetricSubmodule


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The construction-level terminal value with constant adapted coefficient `1` is the
corresponding Brownian increment. -/
theorem elementaryBrownianValue_adaptedOne
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) :
    elementaryBrownianValue hB hsm hnat hab (adaptedOne (P := P) 𝓅 a) =
      brownianLp hB b - brownianLp hB a := by
  apply Lp.ext
  have hOne : (adaptedOne (P := P) 𝓅 a : W → ℝ) =ᵐ[P]
      fun _ ↦ (1 : ℝ) := by
    change (Lp.const 2 P (1 : ℝ) : W → ℝ) =ᵐ[P] fun _ ↦ (1 : ℝ)
    exact Lp.coeFn_const 2 P (1 : ℝ)
  filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab
      (adaptedOne (P := P) 𝓅 a), hOne,
    Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
    coeFn_brownianLp hB b, coeFn_brownianLp hB a]
    with w hvalue hone hsub hb ha
  rw [hvalue, hone, hsub]
  simp only [Pi.sub_apply]
  rw [hb, ha]
  simp only [one_mul]
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- At initial time zero, the construction-level constant-coefficient elementary value is the
Brownian coordinate itself. -/
theorem elementaryBrownianValue_adaptedOne_zero
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    elementaryBrownianValue hB hsm hnat (zero_le : (0 : ℝ≥0) ≤ t)
        (adaptedOne (P := P) 𝓅 0) = brownianLp hB t := by
  rw [elementaryBrownianValue_adaptedOne, brownianLp_zero, sub_zero]
noncomputable def naturalItoDeterministicIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] RandomL2 P :=
  (naturalItoIntegral hB hsm hnat).comp
    (deterministicPredictableEmbedding 𝓅).toContinuousLinearMap
omit [CompleteSpace W] [BorelSpace W] in
/-- Evaluation of the deterministic restriction is composition with the deterministic
predictable embedding. -/
theorem naturalItoDeterministicIntegral_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    naturalItoDeterministicIntegral hB hsm hnat f =
      naturalItoIntegral hB hsm hnat (deterministicPredictableEmbedding 𝓅 f) :=
  rfl
omit [CompleteSpace W] [BorelSpace W] in
/-- On an initial interval indicator, the deterministic restriction is the Brownian
coordinate. -/
theorem naturalItoDeterministicIntegral_intervalIndicator
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (t : ℝ≥0) :
    naturalItoDeterministicIntegral hB hsm hnat (intervalIndicator t) =
      brownianLp hB t := by
  rw [naturalItoDeterministicIntegral_apply,
    ← elementaryPredictable_adaptedOne]
  rw [naturalItoIntegral_elementaryPredictable hB hsm hnat
    (zero_le : (0 : ℝ≥0) ≤ t) (adaptedOne (P := P) 𝓅 0)]
  exact elementaryBrownianValue_adaptedOne_zero hB hsm hnat t
omit [CompleteSpace W] [BorelSpace W] in
/-- The deterministic restriction of the constructed Itô integral is exactly the genuine Wiener
integral on all of deterministic `L²`. -/
theorem naturalItoDeterministicIntegral_eq_wienerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    naturalItoDeterministicIntegral hB hsm hnat = wienerIntegral hB := by
  apply ContinuousLinearMap.ext_on dense_span_intervalIndicator
  intro f hf
  obtain ⟨t, rfl⟩ := hf
  rw [naturalItoDeterministicIntegral_intervalIndicator,
    wienerIntegral_intervalIndicator]
omit [CompleteSpace W] [BorelSpace W] in
/-- The deterministic restriction preserves the `L²` norm. -/
theorem norm_naturalItoDeterministicIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖naturalItoDeterministicIntegral hB hsm hnat f‖ = ‖f‖ := by
  rw [naturalItoDeterministicIntegral_eq_wienerIntegral,
    norm_wienerIntegral]
noncomputable def naturalItoDeterministicIntegralIsometry
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] RandomL2 P where
  toLinearMap := (naturalItoDeterministicIntegral hB hsm hnat).toLinearMap
  norm_map' := norm_naturalItoDeterministicIntegral hB hsm hnat
def NaturalMartingaleRepresentation
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Prop :=
  ∀ G : RandomL2 P, ∃ U : PredictableProcessL2 𝓅 P,
    G = expectationL2 G + naturalItoIntegral hB hsm hnat U
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The expectation-valued constant has the same expectation as the original random variable. -/
theorem expectationMap_expectationL2 (G : RandomL2 P) :
    CameronMartin.expectationMap P (expectationL2 G) =
      CameronMartin.expectationMap P G := by
  rw [CameronMartin.expectationMap_apply, CameronMartin.expectationMap_apply,
    expectationL2]
  simp only [Lp.const_val, AEEqFun.coeFn_const_eq, integral_const, probReal_univ, smul_eq_mul, one_mul]
omit [CompleteSpace W] [BorelSpace W] in
/-- Martingale representation is exactly surjectivity onto the centered subspace. -/
theorem naturalMartingaleRepresentation_iff_surjective
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      Function.Surjective (centeredNaturalItoIntegralIsometry hB hsm hnat) := by
  constructor
  · intro hMRT G
    obtain ⟨U, hU⟩ := hMRT (G : RandomL2 P)
    have hexpect : expectationL2 (G : RandomL2 P) = 0 := by
      rw [expectationL2]
      have hmean : ∫ w, (G : RandomL2 P) w ∂P = 0 := by
        rw [← CameronMartin.expectationMap_apply]
        exact G.property
      rw [hmean]
      simp only [map_zero]
    refine ⟨U, Subtype.ext ?_⟩
    change naturalItoIntegral hB hsm hnat U = (G : RandomL2 P)
    rw [hexpect, zero_add] at hU
    exact hU.symm
  · intro hsurj G
    let G₀ : (CameronMartin.expectationMap P).ker :=
      ⟨G - expectationL2 G, by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.mpr (expectationMap_expectationL2 (P := P) G).symm⟩
    obtain ⟨U, hU⟩ := hsurj G₀
    refine ⟨U, ?_⟩
    have hambient : naturalItoIntegral hB hsm hnat U = G - expectationL2 G := by
      exact congrArg Subtype.val hU
    rw [hambient]
    abel
noncomputable def centeredNaturalItoEquiv
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat) :
    PredictableProcessL2 𝓅 P ≃ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker :=
  LinearIsometryEquiv.ofSurjective
    (centeredNaturalItoIntegralIsometry hB hsm hnat)
    ((naturalMartingaleRepresentation_iff_surjective hB hsm hnat).mp hMRT)
end Malliavin


