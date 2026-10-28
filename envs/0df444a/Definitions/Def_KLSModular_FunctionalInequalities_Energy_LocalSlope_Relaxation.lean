-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Relaxation
-- name    : KLSModular_FunctionalInequalities_Energy_LocalSlope_Relaxation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:12:42.397126+00:00
-- url     : https://prove2.me/theorems/5763c613-ee60-472a-abfb-a2d2d79c15c8
-- title:
--   Asymptotic Lipschitz and local-slope relaxations
-- statement:
--   `AsymptoticLipschitz.apply` assigns to a real-valued function $f$ at $x$ the infimum over $r>0$ of the two-point secant supremum on the open ball $B(x,r)$, with values in $[0,\infty]$. For a probability measure $\nu$, `AsymptoticLipschitz.energy` is the unnormalized integral $\int (\operatorname{Lip}_a f(x))^2\,d\nu(x)$, and `LocalSlope.preEnergy` realizes the squared local-slope energy on admissible locally Lipschitz tests in $L^2(\nu)$. `LocalSlope.relaxation` is the sequential $L^2(\nu)$ relaxation of this pre-energy; the bundle also includes the ambient realization theorem `preEnergy_toAmbient`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.LocalSlope.Gradient
--   import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
--   import FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
--   import FunctionalInequalities.L2.MeanVariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def apply (f : X → ℝ) (x : X) : ℝ≥0∞ :=
--     ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
--       ENNReal.ofReal (dist (f y) (f z) / dist y z)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/LocalSlope/Gradient`](https://prove2.me/theorems/d01ba6e3-090e-46a3-a175-38f38d850838), [`Energy/SmoothGradient/Intrinsic/Basic`](https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e), [`Energy/Relaxation/LowerSemicontinuous`](https://prove2.me/theorems/212961e9-bab7-4abf-a6d1-368cc11f24f3), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/LocalSlope/Relaxation.lean) · `FunctionalInequalities.Energy.LocalSlope.Relaxation` · Frozen source `408915f`.
-- source:
--   Source: Ambrosio–Gigli–Savaré, Density of Lipschitz functions and equivalence of weak gradients in metric measure spaces (arXiv:1111.3730v3), item E37. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Relaxation.lean#L49-L165 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Relaxation`, definition bundle `KLSModular_FunctionalInequalities_Energy_LocalSlope_Relaxation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LowerSemicontinuous
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities
namespace Energy
universe u
namespace AsymptoticLipschitz
section Metric
variable {X : Type*} [MetricSpace X]
/-- Pointwise asymptotic Lipschitz constant `Lip_a f (x) = inf_{r > 0} Lip(f, B(x, r))`, the
infimum over radii of the two-moving-point secant supremum on the open ball.  The real quotient
at `y = z` is zero, so coincident pairs do not change the supremum.  This is not the one-moving-
point local slope `Energy.LocalSlope.apply`, which it dominates pointwise. -/
def apply (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
    ENNReal.ofReal (dist (f y) (f z) / dist y z)
end Metric
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The unnormalized squared asymptotic-Lipschitz integral in a coordinate space. -/
def energy (ν : ProbabilityMeasure V) (f : V → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, apply f x ^ 2 ∂(ν : Measure V)
end AsymptoticLipschitz
namespace LocalSlope
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The finite squared local-slope pre-energy on the literature test domain, realized in real
`L²(ν)`.  The energy is finite on tests by `Admissible.finite_energy`, so `ENNReal.toNNReal`
loses nothing. -/
def preEnergy (ν : ProbabilityMeasure V) : PreEnergy (Lp ℝ 2 (ν : Measure V)) where
  Test := {f : V → ℝ // Admissible ν f}
  toAmbient f := f.2.memLp_two.toLp f.1
  energy f := (energy ν f.1).toNNReal
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The ambient realization of a local-slope test is its `L²(ν)` class. -/
@[simp]
theorem preEnergy_toAmbient (ν : ProbabilityMeasure V) (f : {f : V → ℝ // Admissible ν f}) :
    (preEnergy ν).toAmbient f = f.2.memLp_two.toLp f.1 :=
  rfl
/-- The sequential `L²(ν)` relaxation of the squared local-slope energy over locally Lipschitz
tests.  Twice the metric Cheeger energy in the Blueprint normalization; see `Cheeger.energy`. -/
def relaxation (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (preEnergy ν).sequentialRelaxation
end LocalSlope
end Energy
end FunctionalInequalities


