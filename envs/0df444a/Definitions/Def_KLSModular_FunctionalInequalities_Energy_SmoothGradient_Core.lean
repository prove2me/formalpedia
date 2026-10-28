-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core
-- name    : KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:13:26.771141+00:00
-- url     : https://prove2.me/theorems/3df73178-e378-4d68-a6db-28967184707a
-- title:
--   Local density hypotheses for smooth-gradient cores
-- statement:
--   `SmoothGradient.LocalDensity` records an open set $\Omega\subset V$, a measurable density $\rho$, the fact that $\nu(\Omega^c)=0$, and the identity $\nu|_\Omega=(m|_\Omega)\,\rho$ in `withDensity` form. It also requires $\rho>0$ $m$-almost everywhere on $\Omega$ and an essentially bounded reciprocal on every compact subset of $\Omega$. The theorem `LocalDensity.measure_eq` gives the density integral formula on measurable subsets of $\Omega$, and `LocalDensity.absolutelyContinuous` gives $\nu\ll m$; `lipschitzOperator` is the unit-weight gradient operator and `Test.memLp_gradient` supplies square-integrability of gradients of smooth tests.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.WeightedGradient.Core
--   import FunctionalInequalities.Energy.WeightedGradient.Closable
--   import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
--   import FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
--   import FunctionalInequalities.Energy.Form.Core
--   import FunctionalInequalities.L2.MeanVariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure LocalDensity (ν : ProbabilityMeasure V) (m : Measure V) where
--     /-- The open set carrying the law. -/
--     Ω : Set V
--     isOpen : IsOpen Ω
--     /-- The density on `Ω`. -/
--     ρ : V → ℝ
--     measurable : Measurable ρ
--     /-- The complement of `Ω` is `ν`-null. -/
--     compl_null : (ν : Measure V) Ωᶜ = 0
--     /-- On Borel subsets of `Ω`, `ν` integrates `ρ` against `m`. -/
--     restrict_eq : (ν : Measure V).restrict Ω =
--       (m.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (ρ x)
--     /-- The density is positive almost everywhere on `Ω`. -/
--     pos : ∀ᵐ x ∂m, x ∈ Ω → 0 < ρ x
--     /-- The reciprocal of the density is essentially bounded on compact subsets of `Ω`. -/
--     inv_locallyBounded : ∀ K : Set V, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ᵐ x ∂m, x ∈ K → (ρ x)⁻¹ ≤ C
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`Energy/WeightedGradient/Closable`](https://prove2.me/theorems/fa58e2ea-ffc7-4bbc-a6b9-318f0f549a06), [`Energy/SmoothGradient/Intrinsic/Basic`](https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e), [`Energy/Relaxation/LowerSemicontinuous`](https://prove2.me/theorems/212961e9-bab7-4abf-a6d1-368cc11f24f3), [`Energy/Form/Core`](https://prove2.me/theorems/b744e313-2578-4970-9b76-48a1c977a015), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Theorems in source order:
--
--   - [`subset_support`](https://prove2.me/theorems/4329dc1d-2277-4ded-bce3-2accbe5d4636)
--   - [`Test.exists_domain_sequence_tendsto`](https://prove2.me/theorems/751a102a-9a04-4eaa-a613-041165658667)
--   - [`lipschitzRelaxation_le_relaxation`](https://prove2.me/theorems/92fd2438-7dfd-4386-85e1-7181a8356f84)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean) · `FunctionalInequalities.Energy.SmoothGradient.Core` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L44-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Core`, definition bundle `KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LowerSemicontinuous
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities
namespace Energy
namespace SmoothGradient
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- Density hypotheses of the Blueprint: an open set `Ω` carrying `ν` on which `ν` has the
`m`-density `ρ`, positive almost everywhere with locally essentially bounded reciprocal. -/
structure LocalDensity (ν : ProbabilityMeasure V) (m : Measure V) where
  /-- The open set carrying the law. -/
  Ω : Set V
  isOpen : IsOpen Ω
  /-- The density on `Ω`. -/
  ρ : V → ℝ
  measurable : Measurable ρ
  /-- The complement of `Ω` is `ν`-null. -/
  compl_null : (ν : Measure V) Ωᶜ = 0
  /-- On Borel subsets of `Ω`, `ν` integrates `ρ` against `m`. -/
  restrict_eq : (ν : Measure V).restrict Ω =
    (m.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (ρ x)
  /-- The density is positive almost everywhere on `Ω`. -/
  pos : ∀ᵐ x ∂m, x ∈ Ω → 0 < ρ x
  /-- The reciprocal of the density is essentially bounded on compact subsets of `Ω`. -/
  inv_locallyBounded : ∀ K : Set V, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ᵐ x ∂m, x ∈ K → (ρ x)⁻¹ ≤ C
namespace LocalDensity
variable {ν : ProbabilityMeasure V} {m : Measure V} (D : LocalDensity ν m)
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The law of a measurable subset of `Ω` is the integral of the density. -/
theorem measure_eq {s : Set V} (hs : MeasurableSet s) (hsΩ : s ⊆ D.Ω) :
    (ν : Measure V) s = ∫⁻ x in s, ENNReal.ofReal (D.ρ x) ∂m := by
  have h1 : (ν : Measure V) s = ((ν : Measure V).restrict D.Ω) s := by
    rw [Measure.restrict_apply hs, Set.inter_eq_self_of_subset_left hsΩ]
  rw [h1, D.restrict_eq, withDensity_apply _ hs, Measure.restrict_restrict hs,
    Set.inter_eq_self_of_subset_left hsΩ]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
include D in
/-- The law is absolutely continuous with respect to `m`. -/
theorem absolutelyContinuous : (ν : Measure V) ≪ m := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  have hsplit := measure_inter_add_sdiff (μ := (ν : Measure V)) s D.isOpen.measurableSet
  have h1 : (ν : Measure V) (s ∩ D.Ω) = 0 := by
    rw [D.measure_eq (hs.inter D.isOpen.measurableSet) Set.inter_subset_right]
    exact setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left hs0)
  have h2 : (ν : Measure V) (s \ D.Ω) = 0 :=
    measure_mono_null (fun x hx ↦ hx.2) D.compl_null
  rw [← hsplit, h1, h2, add_zero]
variable [m.IsAddHaarMeasure]
end LocalDensity
section Agreement
variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure] (D : LocalDensity ν m)
open Energy.WeightedGradient Energy.Euclidean
/-- The unit-weight gradient operator on globally Lipschitz tests, under the density
hypotheses. -/
def lipschitzOperator : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  operator ν (ContinuousLinearMap.id ℝ V) D.absolutelyContinuous
omit [FiniteDimensional ℝ V] in
/-- The gradient of a smooth test is square integrable. -/
theorem Test.memLp_gradient (f : Test ν) : MemLp (gradient f.toFun) 2 (ν : Measure V) :=
  (memLp_two_iff_integrable_sq_norm (LipschitzApproximation.aestronglyMeasurable_gradient _ _)).mpr
    f.gradient_sq_integrable
end Agreement
end SmoothGradient
end Energy
end FunctionalInequalities


