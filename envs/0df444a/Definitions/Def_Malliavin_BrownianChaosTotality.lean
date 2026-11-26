-- Prove2me | Definitions.Def_Malliavin_BrownianChaosTotality
-- name    : Malliavin_BrownianChaosTotality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:57:23.453687+00:00
-- url     : https://prove2.me/theorems/9e83bca8-031a-5534-9cd7-9ea7962b558c
-- title:
--   Brownian Chaos Totality
-- statement:
--   Definitions and structural lemmas for Brownian Chaos Totality, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosTotality.lean

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
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
def brownianOrderedChainSet (hB : IsPreBrownianReal B P) : Set (RandomL2 P) :=
  Set.range fun a : Σ n : ℕ, OrderedBoxIndex n =>
    chainIntegralLp hB a.2.u a.2.v
def brownianOrderedChainSpan (hB : IsPreBrownianReal B P) :
    Submodule ℝ (RandomL2 P) :=
  Submodule.span ℝ (brownianOrderedChainSet hB)
end Malliavin.BrownianIteratedConstruction


