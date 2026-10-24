-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
-- name    : KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:43:55.611764+00:00
-- url     : https://prove2.me/theorems/32ebc2bd-1f76-4493-b04f-8677c38a5792
-- title:
--   Local metric slope energy and admissible tests
-- statement:
--   `Energy.LocalSlope.apply f x` is the ENNReal infimum over positive radii of the supremum of the real secant quotient in the corresponding ball, with the center included harmlessly because the quotient there is defined as zero. `Energy.LocalSlope.energy ν f` is the unnormalized ENNReal integral of the squared local slope under the probability measure ν. `Energy.LocalSlope.Admissible ν f` requires local Lipschitz regularity, membership in L²(ν), and finite energy, expressed as energy not equal to ⊤.
-- source:
--   Source: Ambrosio–Gigli–Savaré, Density of Lipschitz functions and equivalence of weak gradients in metric measure spaces (arXiv:1111.3730v3), item S21; E. Milman, On the role of convexity in isoperimetry, spectral gap and concentration (arXiv:0712.4092v5), item R23. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Basic.lean#L18-L157 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic`; the repository is private at upload time).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FunctionalInequalities
namespace Energy
namespace LocalSlope
section Metric
variable {X : Type*} [MetricSpace X]
/-- Pointwise local metric slope as the infimum of punctured-ball secant suprema.
The real quotient at `y = x` is zero, so including the center does not change the supremum.
At an isolated point the slope is zero. This is not the two-moving-point Lipschitz constant. -/
def apply (f : X → ℝ) (x : X) : ENNReal :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r),
    ENNReal.ofReal (dist (f y) (f x) / dist y x)
end Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
/-- The unnormalized squared local-slope integral in an intrinsic coordinate space. -/
def energy (ν : ProbabilityMeasure E) (f : E → ℝ) : ENNReal :=
  ∫⁻ x, apply f x ^ 2 ∂(ν : Measure E)
/-- The literature test domain, independent of the candidate Poincaré constant. -/
structure Admissible (ν : ProbabilityMeasure E) (f : E → ℝ) : Prop where
  locallyLipschitz : LocallyLipschitz f
  memLp_two : MemLp f 2 (ν : Measure E)
  finite_energy : energy ν f ≠ ⊤
end LocalSlope
end Energy
end FunctionalInequalities


