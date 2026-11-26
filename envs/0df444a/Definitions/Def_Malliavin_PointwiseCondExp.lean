-- Prove2me | Definitions.Def_Malliavin_PointwiseCondExp
-- name    : Malliavin_PointwiseCondExp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:11:43.932792+00:00
-- url     : https://prove2.me/theorems/1806dddd-8b49-5481-a044-e68640cece67
-- title:
--   Pointwise Cond Exp
-- statement:
--   Definitions and structural lemmas for Pointwise Cond Exp, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
section Sections
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
@[instance_reducible]
def filtrationPred (t : ℝ≥0) : MeasurableSpace W :=
  ⨆ (s : ℝ≥0) (_ : s < t), 𝓕 s
end Sections
section ClarkOconeIntegrand
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
section NaturalFiltration
variable {B : ℝ≥0 → W → ℝ}
end NaturalFiltration
end ClarkOconeIntegrand
end Malliavin


