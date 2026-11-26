-- Prove2me | Definitions.Def_Malliavin_NaturalItoRange
-- name    : Malliavin_NaturalItoRange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:45:20.236771+00:00
-- url     : https://prove2.me/theorems/73bfc54f-73bc-524a-ac05-6fa09c6de581
-- title:
--   Natural Ito Range
-- statement:
--   Definitions and structural lemmas for Natural Ito Range, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean

import Definitions.Def_Malliavin_ItoConsequences
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_integral_wienerIntegral
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply


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
noncomputable def naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) : Submodule ℝ (RandomL2 P) :=
  LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap
noncomputable def centeredNaturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    Submodule ℝ (CameronMartin.expectationMap P).ker :=
  LinearMap.range (centeredNaturalItoIntegralIsometry hB hsm hnat).toLinearMap
omit [CompleteSpace W] [BorelSpace W] in
/-- The centered natural Itô range is closed. -/
theorem isClosed_centeredNaturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    IsClosed (centeredNaturalItoRange hB hsm hnat :
      Set (CameronMartin.expectationMap P).ker) := by
  let _ : Fact (𝓅.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × W))) :=
    ⟨predictable_le_prod 𝓅⟩
  exact (centeredNaturalItoIntegralIsometry hB hsm hnat).isometry
    |>.isClosedEmbedding.isClosed_range
noncomputable def centeredNaturalItoRangeProjection
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    (CameronMartin.expectationMap P).ker →L[ℝ]
      centeredNaturalItoRange hB hsm hnat := by
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  exact (centeredNaturalItoRange hB hsm hnat).orthogonalProjectionOnto
noncomputable def centeredNaturalItoRangeEquiv
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    PredictableProcessL2 𝓅 P ≃ₗᵢ[ℝ] centeredNaturalItoRange hB hsm hnat :=
  (centeredNaturalItoIntegralIsometry hB hsm hnat).equivRange
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The centered part `G - E[G]`, intrinsically regarded as an element of the expectation
kernel. -/
noncomputable def centeredPartL2 (G : RandomL2 P) :
    (CameronMartin.expectationMap P).ker :=
  ⟨G - expectationL2 G, by
    rw [LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr (expectationMap_expectationL2 (P := P) G).symm⟩
noncomputable def bestNaturalItoIntegrand
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    (CameronMartin.expectationMap P).ker →L[ℝ] PredictableProcessL2 𝓅 P :=
  (centeredNaturalItoRangeEquiv hB hsm hnat).toContinuousLinearEquiv.symm
    |>.toContinuousLinearMap.comp (centeredNaturalItoRangeProjection hB hsm hnat)
noncomputable def bestNaturalItoIntegrandOfRandom
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : RandomL2 P) : PredictableProcessL2 𝓅 P :=
  bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 G)
noncomputable def centeredWienerIntegral
    (hB : IsPreBrownianReal B P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (CameronMartin.expectationMap P).ker :=
  ⟨wienerIntegral hB g, by
    rw [LinearMap.mem_ker]
    change CameronMartin.expectationMap P (wienerIntegral hB g) = 0
    rw [CameronMartin.expectationMap_apply]
    exact integral_wienerIntegral hB g⟩
end Malliavin


