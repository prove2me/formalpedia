-- Prove2me | Definitions.Def_Malliavin_PastCylinderDensity
-- name    : Malliavin_PastCylinderDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:44:36.466924+00:00
-- url     : https://prove2.me/theorems/63fbd1fd-bd23-4c33-a35c-01fdb7744e6b
-- title:
--   Past Cylinder Density
-- statement:
--   Definitions and structural lemmas for Past Cylinder Density, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
section PastProcess
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
def pastProcess (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) : W → (Set.Iic a → ℝ) :=
  fun w t ↦ B t w
def pastCylinderEvents (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) : Set (Set W) :=
  Set.preimage (pastProcess B a) ''
    measurableCylinders (fun _ : Set.Iic a ↦ ℝ)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] in
/-- The algebra of finite-coordinate past events generates the natural filtration at time `a`. -/
theorem natural_eq_generateFrom_pastCylinderEvents
    (hsm : ∀ t, StronglyMeasurable (B t)) (a : ℝ≥0) :
    Filtration.natural B hsm a =
      MeasurableSpace.generateFrom (pastCylinderEvents B a) := by
  rw [Filtration.natural_eq_comap, ← generateFrom_measurableCylinders,
    MeasurableSpace.comap_generateFrom]
  rfl
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P] in
/-- Every finite-coordinate past cylinder is measurable at the corresponding natural-filtration
time. -/
theorem measurableSet_pastCylinderEvents
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0)
    {s : Set W} (hs : s ∈ pastCylinderEvents B a) : MeasurableSet[𝓕 a] s := by
  rw [hnat, natural_eq_generateFrom_pastCylinderEvents hsm a]
  exact MeasurableSpace.measurableSet_generateFrom hs
end PastProcess
end Malliavin


