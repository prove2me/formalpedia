-- Prove2me | Definitions.Def_Malliavin_BrownianPolynomialHermite
-- name    : Malliavin_BrownianPolynomialHermite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:15.512497+00:00
-- url     : https://prove2.me/theorems/9f292d1e-5c33-595d-b77e-5559b3ece700
-- title:
--   Brownian Polynomial Hermite
-- statement:
--   Definitions and structural lemmas for Brownian Polynomial Hermite, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
noncomputable def brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) : RandomL2 P :=
  polynomialFamilyLinearMap (brownianStepPowerLp hB v)
    (varianceHermite (‖stepToLp v‖ ^ 2) n)
def BrownianWickChainCompatible (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, brownianWickPowerLp hB v n ∈
    (brownianOrderedChainSpan hB).topologicalClosure
def BrownianHigherWickChainCompatible (hB : IsPreBrownianReal B P) : Prop :=
  ∀ v n, 2 ≤ n → brownianWickPowerLp hB v n ∈
    (brownianOrderedChainSpan hB).topologicalClosure
end Malliavin.BrownianIteratedConstruction


