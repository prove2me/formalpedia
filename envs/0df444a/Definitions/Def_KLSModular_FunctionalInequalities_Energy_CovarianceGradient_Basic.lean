-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Basic
-- name    : KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:23:48.048173+00:00
-- url     : https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43
-- title:
--   Covariance-weighted gradient energy and its relaxation
-- statement:
--   `CovarianceGradient.density ν g x` is $\langle\operatorname{Cov}(\nu)\nabla g(x),\nabla g(x)\rangle$, with nonnegativity supplied by the covariance form. A `CovarianceGradient.Test ν` is a globally Lipschitz real function in $L^2(\nu)$ whose covariance-weighted gradient density is ν-integrable; its finite `energy` is $\int\langle\operatorname{Cov}(\nu)\nabla g,\nabla g\rangle\,d\nu$. `preEnergy` realizes these tests in real $L^2(\nu)$, and `relaxation` is the sequential relaxation; the intrinsic declarations apply the same construction to the intrinsic law on the direction space of the affine support.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Measurable
--   import FunctionalInequalities.Energy.Relaxation.Basic
--   import FunctionalInequalities.Probability.AffineSupport
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.MeasureTheory.Function.L2Space
--   import Mathlib.MeasureTheory.Measure.Support
--   import Mathlib.Topology.MetricSpace.Lipschitz
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def density (ν : ProbabilityMeasure V) (g : V → ℝ) (x : V) : ℝ :=
--     inner ℝ (Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Euclidean/LipschitzApproximation/Measurable`](https://prove2.me/theorems/4ca87026-e2cc-45b4-8e9e-f0a5bba71236), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/CovarianceGradient/Basic.lean) · `FunctionalInequalities.Energy.CovarianceGradient.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/Basic.lean#L61-L284 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.Basic`, definition bundle `KLSModular_FunctionalInequalities_Energy_CovarianceGradient_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace FunctionalInequalities
namespace Energy
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V]
namespace CovarianceGradient
/-- The covariance-weighted squared gradient `⟪Σ ∇g x, ∇g x⟫` with `Σ = Covariance.operator ν`. -/
def density (ν : ProbabilityMeasure V) (g : V → ℝ) (x : V) : ℝ :=
  inner ℝ (Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x)
/-- The covariance-weighted gradient density is pointwise nonnegative, because the covariance
bilinear form is positive semidefinite (and zero without a second moment). -/
theorem density_nonneg (ν : ProbabilityMeasure V) (g : V → ℝ) (x : V) :
    0 ≤ density ν g x := by
  unfold density
  rw [Covariance.operator_inner]
  exact covarianceBilin_self_nonneg _
/-- A globally Lipschitz real `L²(ν)` test with integrable covariance-weighted gradient density. -/
structure Test (ν : ProbabilityMeasure V) where
  /-- The real-valued test function. -/
  toFun : V → ℝ
  /-- The test is globally Lipschitz for some finite constant. -/
  lipschitz : ∃ K : NNReal, LipschitzWith K toFun
  /-- The test defines an element of real `L²(ν)`. -/
  memLp_two : MemLp toFun 2 (ν : Measure V)
  /-- The covariance-weighted squared gradient is integrable. -/
  integrable : Integrable (density ν toFun) (ν : Measure V)
end CovarianceGradient
namespace CovarianceGradient
namespace Test
variable {ν : ProbabilityMeasure V}
instance : CoeFun (Test ν) (fun _ ↦ V → ℝ) :=
  ⟨toFun⟩
/-- The finite real integral underlying the covariance energy is nonnegative. -/
theorem integral_nonneg (f : Test ν) :
    0 ≤ ∫ x, Energy.CovarianceGradient.density ν f.toFun x ∂(ν : Measure V) :=
  MeasureTheory.integral_nonneg (Energy.CovarianceGradient.density_nonneg ν f.toFun)
/-- The finite covariance-weighted gradient energy `∫ ⟪Σ ∇g, ∇g⟫ dν`, valued in `NNReal`. -/
def energy (f : Test ν) : NNReal :=
  ⟨∫ x, Energy.CovarianceGradient.density ν f.toFun x ∂(ν : Measure V), f.integral_nonneg⟩
/-- Coercing the finite energy to `ℝ` recovers its defining integral. -/
@[simp, norm_cast]
theorem coe_energy (f : Test ν) :
    (f.energy : ℝ) = ∫ x, Energy.CovarianceGradient.density ν f.toFun x ∂(ν : Measure V) :=
  rfl
/-- The `L²(ν)` element represented by a test. -/
def toL2 (f : Test ν) : Lp ℝ 2 (ν : Measure V) :=
  f.memLp_two.toLp f.toFun
end Test
end CovarianceGradient
namespace CovarianceGradient
/-- The finite covariance-weighted gradient pre-energy on globally Lipschitz tests, realized in
real `L²(ν)`. -/
def preEnergy (ν : ProbabilityMeasure V) : PreEnergy (Lp ℝ 2 (ν : Measure V)) where
  Test := Test ν
  toAmbient := Test.toL2
  energy := Test.energy
/-- The ambient realization of the covariance pre-energy is the test's `L²` class. -/
@[simp]
theorem preEnergy_toAmbient (ν : ProbabilityMeasure V) (f : Test ν) :
    (preEnergy ν).toAmbient f = f.toL2 :=
  rfl
/-- The covariance pre-energy is exactly the finite covariance-weighted gradient integral. -/
@[simp]
theorem preEnergy_energy (ν : ProbabilityMeasure V) (f : Test ν) :
    (preEnergy ν).energy f = f.energy :=
  rfl
/-- The sequential `L²(ν)` relaxation of the covariance pre-energy. Closability, quadraticity
and agreement with the raw energy on tests are separate theorems, not part of this name. -/
def relaxation (ν : ProbabilityMeasure V) : Functional (Lp ℝ 2 (ν : Measure V)) :=
  (preEnergy ν).sequentialRelaxation
end CovarianceGradient
section Representative
variable [SecondCountableTopology V]
namespace Euclidean
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Continuous functions that agree `ν`-almost everywhere agree on the support of `ν`. -/
theorem eqOn_support_of_ae_eq {ν : Measure V} {g₁ g₂ : V → ℝ}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (h : g₁ =ᵐ[ν] g₂) :
    Set.EqOn g₁ g₂ ν.support := by
  have hopen : IsOpen {x | g₁ x ≠ g₂ x} := isOpen_ne_fun h₁ h₂
  have hnull : ν {x | g₁ x ≠ g₂ x} = 0 := h
  intro x hx
  by_contra hne
  exact Measure.subset_compl_support_of_isOpen hopen hnull hne hx
omit [BorelSpace V] in
/-- If the frontier of the support of `ν` is `ν`-null, continuous representatives of one
`ν`-almost everywhere class have `ν`-almost everywhere equal canonical gradients. The gradient
is compared through `fderiv`, which only depends on the germ of the function. -/
theorem gradient_ae_eq_of_ae_eq {ν : Measure V} (hfr : ν (frontier ν.support) = 0)
    {g₁ g₂ : V → ℝ} (h₁ : Continuous g₁) (h₂ : Continuous g₂) (h : g₁ =ᵐ[ν] g₂) :
    gradient g₁ =ᵐ[ν] gradient g₂ := by
  have heq := eqOn_support_of_ae_eq h₁ h₂ h
  have hsupp : ∀ᵐ x ∂ν, x ∈ ν.support := Measure.support_mem_ae
  have hfr' : ∀ᵐ x ∂ν, x ∉ frontier ν.support := compl_mem_ae_iff.mpr hfr
  filter_upwards [hsupp, hfr'] with x hx hxf
  have hint : x ∈ interior ν.support := by
    rw [Measure.isClosed_support.frontier_eq] at hxf
    exact by_contra fun hnot ↦ hxf ⟨hx, hnot⟩
  have hgerm : g₁ =ᶠ[𝓝 x] g₂ := by
    filter_upwards [isOpen_interior.mem_nhds hint] with y hy
    exact heq (interior_subset hy)
  simp only [gradient, hgerm.fderiv_eq]
end Euclidean
end Representative
end Energy
end FunctionalInequalities
namespace FunctionalInequalities
namespace Energy
namespace CovarianceGradient
namespace Intrinsic
open Energy.Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
/-- The affine covariance pre-energy `P^aff_μ`: the covariance pre-energy of the intrinsic law
of `μ` on the direction space of its affine support, with `Σ = Covariance.operator ν`. -/
def preEnergy (μ : ProbabilityMeasure E) :
    PreEnergy (Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :=
  Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ)
/-- The affine covariance relaxation `𝓔^aff_μ`: the sequential `L²(ν)` relaxation of the
affine covariance pre-energy on the intrinsic law `ν`. -/
def energy (μ : ProbabilityMeasure E) :
    Functional (Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)) :=
  (preEnergy μ).sequentialRelaxation
omit [CompleteSpace E] in
/-- The affine pre-energy is the covariance pre-energy of the intrinsic law. -/
@[simp]
theorem preEnergy_eq_intrinsicMeasure (μ : ProbabilityMeasure E) :
    preEnergy μ = Energy.CovarianceGradient.preEnergy (Probability.intrinsicMeasure μ) :=
  rfl
end Intrinsic
end CovarianceGradient
end Energy
end FunctionalInequalities


