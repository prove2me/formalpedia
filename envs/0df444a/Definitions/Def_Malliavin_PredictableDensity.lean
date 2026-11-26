-- Prove2me | Definitions.Def_Malliavin_PredictableDensity
-- name    : Malliavin_PredictableDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:11:49.34316+00:00
-- url     : https://prove2.me/theorems/c3d27015-ed16-501e-9a43-f37f81f05b1d
-- title:
--   Predictable Density
-- statement:
--   Definitions and structural lemmas for Predictable Density, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean

import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The predictable-process subspace as the trimmed-measure `L²` model used by completion
constructions of the Itô integral. -/
noncomputable def predictableTrimEquiv
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    PredictableProcessL2 𝓕 P ≃ₗᵢ[ℝ]
      @Lp (ℝ≥0 × W) ℝ 𝓕.predictable _ 2
        ((nonnegativeLebesgueMeasure.prod P).trim (predictable_le_prod 𝓕)) :=
  lpMeasToLpTrimLie ℝ ℝ 2 (nonnegativeLebesgueMeasure.prod P) (predictable_le_prod 𝓕)
def predictableRectangle (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Set (Set (ℝ≥0 × W)) :=
  {S | ∃ F₀ : Set W, MeasurableSet[𝓕 0] F₀ ∧ S = ({(0 : ℝ≥0)} ×ˢ F₀)} ∪
  {S | ∃ a b : ℝ≥0, ∃ F : Set W,
    a < b ∧ MeasurableSet[𝓕 a] F ∧ S = (Set.Ioc a b ×ˢ F)}
noncomputable def adaptedIndicator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    lpMeas ℝ ℝ (𝓕 a) 2 P :=
  ⟨indicatorConstLp 2 (𝓕.le a F hF) (measure_ne_top P F) (1 : ℝ),
    mem_lpMeas_indicatorConstLp (𝓕.le a) hF (measure_ne_top P F)⟩
def elementaryPredictableSpan
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Submodule ℝ (PredictableProcessL2 𝓕 P) :=
  Submodule.span ℝ {U | ∃ a b : ℝ≥0,
    ∃ _hab : a ≤ b, ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P,
      U = elementaryPredictable 𝓕 a b Z}
end Malliavin


