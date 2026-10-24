-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
-- name    : KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:44:13.757267+00:00
-- url     : https://prove2.me/theorems/b51b9aa3-0d0d-4a63-a952-b49e04fc3805
-- title:
--   Local-slope Poincaré bounds
-- statement:
--   `Poincare.LocalSlope.Holds ν C` states that every locally Lipschitz, L²(ν), finite-energy test satisfies evariance f ≤ C times its ENNReal local-slope energy, where C is a finite NNReal constant. `Poincare.LocalSlope.Intrinsic.constant μ` is the ENNReal infimum of all finite constants satisfying this predicate for the intrinsic law of μ. If no finite constant is valid, the infimum is ⊤; the variance and energy remain in their extended-valued conventions.
-- source:
--   Source: Klartag, Logarithmic bounds for isoperimetry and slices of convex sets (arXiv:2303.14938v2), item D13; Klartag–Lehec, Bourgain’s slicing problem and KLS isoperimetry up to polylog (arXiv:2203.15551v2), item D5; Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), item DCP; E. Milman, On the role of convexity in isoperimetry, spectral gap and concentration (arXiv:0712.4092v5), item DPoin. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/LocalSlope/Basic.lean#L18-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.LocalSlope.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FunctionalInequalities
namespace Poincare
namespace LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- A finite bound on all literature tests in the displayed coordinate space.
The extended variance is finite by `Energy.LocalSlope.Admissible.memLp_two`;
no real-valued infinite integral is used. -/
def Holds (ν : ProbabilityMeasure E) (C : NNReal) : Prop :=
  ∀ f : E → ℝ, Energy.LocalSlope.Admissible ν f →
    evariance f (ν : Measure E) ≤ (C : ENNReal) * Energy.LocalSlope.energy ν f
/-- The literature optimum of the intrinsic law. Empty sets of finite constants give infinity. -/
def Intrinsic.constant (μ : ProbabilityMeasure E) : ENNReal :=
  ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds (Probability.intrinsicMeasure μ) C},
    (C.1 : ENNReal)
end LocalSlope
end Poincare
end FunctionalInequalities


