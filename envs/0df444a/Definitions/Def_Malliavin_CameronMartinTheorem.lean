-- Prove2me | Definitions.Def_Malliavin_CameronMartinTheorem
-- name    : Malliavin_CameronMartinTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:42:10.454096+00:00
-- url     : https://prove2.me/theorems/cfaa9221-5f07-5460-b75e-b836d4c3456d
-- title:
--   Cameron Martin Theorem
-- statement:
--   Definitions and structural lemmas for Cameron Martin Theorem, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
namespace Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
def densityExponent (h : Space μ) (x : W) : ℝ :=
  (h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2
def realDensity (h : Space μ) (x : W) : ℝ :=
  Real.exp (densityExponent μ h x)
def density (h : Space μ) (x : W) : ℝ≥0∞ :=
  ENNReal.ofReal (realDensity μ h x)
noncomputable def expectationMap : Lp ℝ 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2).flip (Lp.const 2 μ 1)
noncomputable def centeredGaussianPM (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 v, inferInstance⟩
noncomputable def lawPM {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEMeasurable f μ) : ProbabilityMeasure ℝ :=
  ⟨μ.map f, Measure.isProbabilityMeasure_map hf⟩
end Malliavin.CameronMartin


