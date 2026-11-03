-- Prove2me | Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension
-- name    : levy_foundations_isCompensatedPoissonL2Extension
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T12:15:54.152742+00:00
-- url     : https://prove2.me/theorems/a1c80eee-f52d-4c47-840e-bd8944f78b1c
-- title:
--   Linear centred L² extension of the compensated Poisson integral
-- statement:
--   Characterise the compensated Poisson L² extension as a linear norm-preserving map from L² of the intensity to L² of the probability space. Every image has zero expectation, and the map agrees almost everywhere with the centred point-family sum for measurable L¹∩L² test functions.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonCompensated.lean; independently authored Prove2Me draft pending remote elaboration. Definition follows the properties proved around source lines 699–956.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_levy_foundations_compensatedPoissonSum

open MeasureTheory
namespace LevyFoundations
structure IsCompensatedPoissonL2Extension
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (I : Lp ℝ 2 m → Lp ℝ 2 μ) : Prop where
  map_add : ∀ f g, I (f + g) = I f + I g
  map_smul : ∀ (c : ℝ) f, I (c • f) = c • I f
  norm_eq : ∀ f, ‖I f‖ = ‖f‖
  mean_zero : ∀ f, ∫ ω, I f ω ∂μ = 0
  agree_sum : ∀ (f : E → ℝ) (hf : Measurable f)
      (hf1 : Integrable f m) (hf2 : MemLp f 2 m),
    (fun ω => I (hf2.toLp f) ω) =ᵐ[μ]
      LevyFoundations.compensatedPoissonSum m K X f
end LevyFoundations


