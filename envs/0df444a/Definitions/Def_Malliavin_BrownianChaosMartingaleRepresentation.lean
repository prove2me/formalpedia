-- Prove2me | Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
-- name    : Malliavin_BrownianChaosMartingaleRepresentation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:56:41.023689+00:00
-- url     : https://prove2.me/theorems/6354ef04-d36a-4bc4-9d50-dd651c1272a2
-- title:
--   Brownian Chaos Martingale Representation
-- statement:
--   Definitions and structural lemmas for Brownian Chaos Martingale Representation, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosMartingaleRepresentation.lean

import Definitions.Def_Malliavin_BrownianChaos
import Definitions.Def_Malliavin_ChaosMartingaleRepresentation
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
def BrownianChaosTotal (hB : IsPreBrownianReal B P) : Prop :=
  (⨆ n : ℕ, (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P))
    ).topologicalClosure = ⊤
end Malliavin.BrownianIteratedConstruction


