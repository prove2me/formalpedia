-- Prove2me | Definitions.Def_OAIQ091C032
-- name    : OAIQ091C032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:12:19.701184+00:00
-- url     : https://prove2.me/theorems/5d6a43f6-3b1a-4f7a-a5fb-c22262eab78e
-- title:
--   Definitions bundle OAIQ091C032 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 249 declarations of OpenAI's Lean: 33 definitions, 3 instances and 213 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.deRhamIntersection`, `OAI.PositiveEinsteinFour.Geometry.deRhamIntersectionQuadratic`, `OAI.PositiveEinsteinFour.Geometry.deRhamSignature`, `OAI.PositiveEinsteinFour.Geometry.divergenceCokernelEquiv`, `OAI.PositiveEinsteinFour.Geometry.harmonicDeRhamIntersectionIsometry`, `OAI.PositiveEinsteinFour.Geometry.hodgeHeatDensity`, `OAI.PositiveEinsteinFour.Geometry.hodgeHeatRealDensity`, `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralLift`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatC0Linear`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatC0Value`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatEvaluation`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatFrameColumn`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatRealColumn`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatRealDiagonal`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatReconstructed`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatToC0`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatToContinuous`, `OAI.PositiveEinsteinFour.Geometry.oneFormLiftSynthesis`, `OAI.PositiveEinsteinFour.Geometry.oneFormTwoFormPotential`, `OAI.PositiveEinsteinFour.Geometry.scalarConstantDeRhamEquiv`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatDiagonal`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatKernel`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatRealColumn`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatRealDiagonal`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicDeRhamEquiv`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicResolventEquiv`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicWeakEquiv`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatFrameColumn`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatKernel`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatKernelTerm`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatRealColumn`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatRealSignedTrace`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatRealTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry11.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_GeodesicGeometry13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry13.lean), [`EinsteinFour_GeodesicGeometry14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry14.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C030` and `OAIQ091C031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C034`, `OAIQ091C048`, `OAIQ091C051` and `OAIQ091C052`; the statement `OAI_PositiveEinsteinFour_HighestHessian_traceComponent_pairing_hessian`; the proof of `OAI_PositiveEinsteinFour_Bianchi_matrixRotation_energy`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C030
import Definitions.Def_OAIQ091C031

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Compactness and the local no-corner argument give a minimizing radial
geodesic to every point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem frameExponential_surjective (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    Function.Surjective (frameExponential g o e) := fun q =>
  let ⟨v, hv, _⟩ := frameExponential_global_minimizing g o hRic e he q
  ⟨v, hv⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kernel of the actual smooth scalar Laplacian.  The proof uses
the actual parallel-flow Green formula, full support of base volume, and
constancy along the complete geodesics.  No elliptic kernel theorem is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

variable [PreconnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Vanishing actual scalar differential implies constancy on the connected
compact manifold. -/
theorem scalar_constants_of_gradient_eq_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hgrad : ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0) :
    ∃ c : ℝ, ∀ x, a x = c := by
  let x : M := Classical.arbitrary M
  let e : FrameBundle g := ⟨x, o.frame x⟩
  have he : e ∈ o.positive := o.frame_positive x
  refine ⟨a x, fun y => ?_⟩
  obtain ⟨v, hv⟩ := frameExponential_surjective g o hRic e he y
  rw [← hv]
  exact scalar_eq_on_exponential_of_gradient_eq_zero g o ha hgrad e he v

/-- A smooth harmonic scalar is constant for the actual normalized metric.
The Ricci normalization supplies the invariant flow data. -/
theorem scalarLaplacian_kernel_constants (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hLap : ∀ e : FrameBundle g, scalarLaplacian g a e = 0) :
    ∃ c : ℝ, ∀ x, a x = c := by
  let d := canonicalParallelMetricData g o hRic
  obtain ⟨s⟩ := d.scalarCalculus.toPetersenInput a ha
  have hgrad := scalarGradient_eq_zero_of_laplacian_eq_zero g o ha
    d.toMetricGreenData s hLap
  exact scalar_constants_of_gradient_eq_zero g o hRic ha hgrad

end
end PositiveEinsteinFour.Geometry
end


section

/-! The zeroth de Rham space is exactly the constant smooth functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]

include o

local instance instAddCommGroupSubtypeSmoothScalarMemSubmoduleRealZeroFormDeRhamCohomology_r3780e6_1 : AddCommGroup (ZeroFormDeRhamCohomology g) := Submodule.addCommGroup _
theorem scalarConstantToDeRham_surjective (hRic : RicciThree g) :
    Function.Surjective (scalarConstantToDeRham (g := g)) := by
  intro f
  have hdf : smoothScalarDifferential g f.val = 0 := f.property
  have hg (e : FrameBundle g) (i : Fin 4) : scalarGradient g f.val.val e i = 0 := by
    rw [← smoothScalarDifferential_framed, hdf]
    simp only [Submodule.coe_zero, covariantFieldFramed_eq, frameTensor, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero]
  obtain ⟨c, hc⟩ := scalar_constants_of_gradient_eq_zero g o hRic f.val.property hg
  refine ⟨c, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact funext (fun x => (hc x).symm)

def scalarConstantDeRhamEquiv (hRic : RicciThree g) :
    ℝ ≃ₗ[ℝ] ZeroFormDeRhamCohomology g :=
  LinearEquiv.ofBijective scalarConstantToDeRham
    ⟨scalarConstantToDeRham_injective, scalarConstantToDeRham_surjective (o := o) hRic⟩

theorem zeroFormDeRhamCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (ZeroFormDeRhamCohomology g) = 1 := by
  rw [← (scalarConstantDeRhamEquiv (o := o) hRic).finrank_eq]
  exact Module.finrank_self ℝ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pushforward of the actual exponential Jacobian on minimizing
vectors dominates Riemannian volume. The proof is local in output charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [MeasurableSpace M] [BorelSpace M]

variable [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

variable [SecondCountableTopology M]

theorem volumeMeasure_le_integral_exponentialJacobian (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      ∫⁻ v in actualMinimizingTangentDomain g o e,
        ENNReal.ofReal (frameExponentialJacobian g o e v) := by
  have h := volumeMeasure_le_exponentialAreaMeasure g o hRic e he univ
  rwa [exponentialAreaMeasure_apply g o e univ MeasurableSet.univ,
    preimage_univ, univ_inter] at h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Positive reciprocal solutions of the subcritical scalar equation
are constant. This supplies the rigidity step in the normalized
Sobolev minimization argument, independently of minimizer existence. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} {a : M → ℝ}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.nonlinearRigidity_frameCompact
/-- The Hessian sign identity forces any positive smooth reciprocal
solution with exponent below four to be constant. -/
theorem scalar_reciprocal_subcritical_constants (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (hpos : ∀ x, 0 < a x)
    (p : ℝ) (hp : p < 4)
    (hEq : ∀ e : FrameBundle g,
      a e.base * scalarLaplacian g a e -
        2 * (∑ i, scalarGradient g a e i ^ 2) + 2 * a e.base ^ 2 =
          2 * (a e.base) ^ (4 - p)) :
    ∃ c : ℝ, ∀ x, a x = c := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  obtain ⟨s⟩ := d.scalarCalculus.toPetersenInput a ha
  have hw : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun x => (a x ^ 3)⁻¹) :=
    (ha.pow 3).inv₀ (fun x => pow_ne_zero 3 (ne_of_gt (hpos x)))
  obtain ⟨v⟩ := d.scalarCalculus.toPetersenInput _ hw
  have h := s.weighted_traceFree_green v
  have he (e : FrameBundle g) :
      (∑ j, scalarGradient g a e j *
        ((∑ i, scalarGradient g (fun x => (a x ^ 3)⁻¹) e i *
          scalarTraceFreeHessian g a e i j) +
          (3 / 4 : ℝ) * (a e.base ^ 3)⁻¹ *
            ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j))) =
      scalarSubcriticalWeight p a e.base * (∑ j, scalarGradient g a e j ^ 2) := by
    simp_rw [scalar_inverse_hessian_divergence s p hpos v hEq]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [he] at h
  have hkpos (x : M) : 0 < scalarSubcriticalWeight p a x := by
    unfold scalarSubcriticalWeight
    have hx := hpos x
    have hsub : 0 < 4 - p := sub_pos.mpr hp
    positivity
  have hleft : 0 ≤ ∫ e, (a e.base ^ 3)⁻¹ *
      (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) ∂μ := by
    apply integral_nonneg
    intro e
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (hpos _).le _))
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hright : 0 ≤ ∫ e, scalarSubcriticalWeight p a e.base *
      (∑ j, scalarGradient g a e j ^ 2) ∂μ := by
    apply integral_nonneg
    intro e
    exact mul_nonneg (hkpos _).le (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hzero : (∫ e, scalarSubcriticalWeight p a e.base *
      (∑ j, scalarGradient g a e j ^ 2) ∂μ) = 0 := by
    linarith only [h, hleft, hright]
  have hk : Continuous (scalarSubcriticalWeight p a) := by
    have hr : Continuous (fun x => a x ^ (3 - p)) :=
      ha.continuous.rpow_const (fun x => Or.inl (ne_of_gt (hpos x)))
    exact ((continuous_const.div (ha.continuous.pow 4)
      (fun x => pow_ne_zero 4 (ne_of_gt (hpos x)))).mul continuous_const).mul hr
  exact scalar_constants_of_gradient_eq_zero g o hRic ha
    (scalarGradient_zero_of_weighted_energy g o ha hk hkpos hzero)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive subcritical Euler equation has only the unit solution
on the actual closed connected normalized Einstein manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

local instance eulerRigidity_frameCompact_r3780e6_1 (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g
theorem scalar_positive_subcritical_euler (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {u : M → ℝ}
    (hu : ContMDiff I4 𝓘(ℝ, ℝ) ∞ u) (hpos : ∀ x, 0 < u x)
    (p : ℝ) (hp₀ : 2 < p) (hp₁ : p < 4)
    (hEq : ∀ e : FrameBundle g, -scalarLaplacian g u e + 2 * u e.base =
      2 * u e.base ^ (p - 1)) : ∀ x, u x = 1 := by
  let d := canonicalParallelMetricData g o hRic
  obtain ⟨s⟩ := d.scalarCalculus.toPetersenInput u hu
  have hv : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun x => (u x)⁻¹) :=
    hu.inv₀ (fun x => ne_of_gt (hpos x))
  obtain ⟨v⟩ := d.scalarCalculus.toPetersenInput _ hv
  obtain ⟨c, hc⟩ := scalar_reciprocal_subcritical_constants g o hRic hv
    (fun x => inv_pos.mpr (hpos x)) p hp₁
    (scalar_reciprocal_euler_equation s hpos v p hEq)
  have hconst (x : M) : u x = c⁻¹ := by
    have h := congrArg Inv.inv (hc x)
    simpa only [inv_inv] using h
  have hG (e : FrameBundle g) (i : Fin 4) : scalarGradient g u e i = 0 := by
    obtain ⟨e₀, he⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
    have h := s.derivativeValue i 0 e₀
    have hf : (fun t => u ((d.toMetricGreenData.flow i).map t e₀).base) =
        (fun _ : ℝ => c⁻¹) := funext (fun _ => hconst _)
    rw [hf] at h
    have hz := h.unique (hasDerivAt_const 0 c⁻¹)
    rwa [he] at hz
  have hH (e : FrameBundle g) (i j : Fin 4) : scalarHessian g u e i j = 0 := by
    obtain ⟨e₀, he⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
    have h := s.derivativeGradient i j 0 e₀
    have hf : (fun t => scalarGradient g u ((d.toMetricGreenData.flow i).map t e₀) j) =
        (fun _ : ℝ => 0) := funext (fun _ => hG _ j)
    rw [hf] at h
    have hz := h.unique (hasDerivAt_const 0 0)
    rwa [he] at hz
  let x₀ : M := Classical.arbitrary M
  have hcpos : 0 < c⁻¹ := by rw [← hconst x₀]; exact hpos x₀
  have hunit := hEq (frameAt g x₀)
  simp only [scalarLaplacian, hH, Finset.sum_const_zero, neg_zero, zero_add, hconst] at hunit
  have hpEq : (c⁻¹) ^ (p - 2) = 1 := by
    have hpow : (c⁻¹) ^ (p - 1) = (c⁻¹) ^ (p - 2) * c⁻¹ := by
      calc
        _ = (c⁻¹) ^ ((p - 2) + 1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hcpos, Real.rpow_one]
    rw [hpow] at hunit
    nlinarith only [hunit, hcpos]
  have hcunit : c⁻¹ = 1 :=
    (Real.rpow_left_inj hcpos.le zero_le_one (ne_of_gt (sub_pos.mpr hp₀))).mp
      (by simpa only [Real.one_rpow] using hpEq)
  intro x
  exact (hconst x).trans hcunit

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed space of the actual scalar shifted resolvent is precisely the
constant functions on the connected manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

variable [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarFixed_frameCompact
theorem scalarBaseResolvent_fixed_constant (hRic : RicciThree g)
    (f : Lp ℝ 2 (normalizedVolume g)) (hf : scalarBaseResolvent g o d f = f) :
    ∃ c : ℝ, f = c • smoothScalarBaseL2 g (smoothScalarConst 1) := by
  obtain ⟨F, hF, hL⟩ := scalarBaseResolvent_fixed_smooth g o d f hf
  have hLap (e : FrameBundle g) : scalarLaplacian g F e = 0 := by
    rw [scalarLaplacian_eq_base]
    exact congrArg (fun a : SmoothScalar (M := M) => a.val e.base) hL
  obtain ⟨c, hc⟩ := scalarLaplacian_kernel_constants g o hRic F.property hLap
  have hFc : F = c • smoothScalarConst 1 := by
    apply Subtype.ext
    funext x
    change F.val x = c * 1
    simpa only [mul_one] using hc x
  refine ⟨c, ?_⟩
  rw [hF, hFc]
  apply (scalarBasePullback g o).injective
  rw [map_smul, scalarBasePullback_smooth, scalarBasePullback_smooth, map_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rescaling the normalized positive Euler minimizer to the already proved
unit-coefficient rigidity theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarEulerScaling_probability
/-- Once positive smooth regularity is known, the normalized minimum has
energy one and its representative is the constant one. -/
theorem scalar_positive_normalized_euler_minimum_one (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M))
    (hpos : ∀ x, 0 < a.val x) {p m : ℝ} (hp : 2 < p) (hp4 : p < 4) (hm : 0 < m)
    (hnorm : (∫ x, a.val x ^ p ∂normalizedVolume g) = 1)
    (hEq : ∀ e : FrameBundle g, -scalarLaplacian g a.val e + 2 * a.val e.base =
      2 * m * a.val e.base ^ (p - 1)) : m = 1 ∧ ∀ x, a.val x = 1 := by
  let c := m ^ (1 / (p - 2))
  have hc : 0 < c := Real.rpow_pos_of_pos hm _
  have hcm : c ^ (p - 2) = m := by
    rw [show c = m ^ (1 / (p - 2)) from rfl, ← Real.rpow_mul hm.le]
    have he : 1 / (p - 2) * (p - 2) = 1 := by
      field_simp [ne_of_gt (sub_pos.mpr hp)]
    rw [he, Real.rpow_one]
  have hcp : c ^ (p - 1) = m * c := by
    calc
      _ = c ^ ((p - 2) + 1) := by congr 1; ring
      _ = c ^ (p - 2) * c := by rw [Real.rpow_add hc, Real.rpow_one]
      _ = m * c := by rw [hcm]
  let d := canonicalParallelMetricData g o hRic
  let b : SmoothScalar (M := M) := c • a
  have hbpos (x : M) : 0 < b.val x := mul_pos hc (hpos x)
  have hbEq (e : FrameBundle g) : -scalarLaplacian g b.val e + 2 * b.val e.base =
      2 * b.val e.base ^ (p - 1) := by
    rw [show b = c • a from rfl, smoothScalarLaplacian_const_smul d]
    change -(c * scalarLaplacian g a.val e) + 2 * (c * a.val e.base) =
      2 * (c * a.val e.base) ^ (p - 1)
    rw [Real.mul_rpow hc.le (hpos e.base).le, hcp]
    linear_combination c * hEq e
  have hbunit := scalar_positive_subcritical_euler g o hRic b.property hbpos p hp hp4 hbEq
  have haconst (x : M) : a.val x = c⁻¹ := by
    have hu := hbunit x
    change c * a.val x = 1 at hu
    apply (mul_left_cancel₀ (ne_of_gt hc))
    rw [hu, mul_inv_cancel₀ (ne_of_gt hc)]
  have hpower : (c⁻¹) ^ p = 1 := by
    simpa only [haconst, integral_const, probReal_univ, one_smul] using hnorm
  have hcunit : c⁻¹ = 1 :=
    (Real.rpow_left_inj (inv_nonneg.mpr hc.le) zero_le_one (by linarith : p ≠ 0)).mp
      (by simpa only [Real.one_rpow] using hpower)
  have hc1 : c = 1 := by simpa only [inv_inv, inv_one] using congrArg Inv.inv hcunit
  refine ⟨?_, fun x => (haconst x).trans hcunit⟩
  simpa only [hc1, Real.one_rpow] using hcm.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeatConvolution_norm_le
    (R : ℝ → Lp ℝ 2 (normalizedVolume g)) (t : ℝ) (ht : 0 ≤ t) (B : ℝ)
    (hR : ∀ s ∈ Icc 0 t, ‖R s‖ ≤ B * s) :
    ‖scalarHeatConvolution g o d R t‖ ≤ B * t ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => B * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, B * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hi
      exact Filter.Eventually.of_forall fun s hs =>
        (scalarBaseHeat_contraction g o d (t - s).toNNReal (R s)).trans
          (hR s ⟨hs.1.le, hs.2⟩)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

theorem scalarHeatConvolution_eigen
    (R : ℝ → Lp ℝ 2 (normalizedVolume g)) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t))
    (i : ScalarBaseEigenIndex g o d) :
    inner ℝ (scalarHeatConvolution g o d R t) (scalarBaseEigenvector g o d i) =
      ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
        inner ℝ (R s) (scalarBaseEigenvector g o d i) := by
  have hi := scalarHeatConvolution_integrable g o d R t ht hR
  have hp := (innerSL ℝ (scalarBaseEigenvector g o d i)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t,
    inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseHeat g o d (t - s).toNNReal (R s))) =
      inner ℝ (scalarBaseEigenvector g o d i) (scalarHeatConvolution g o d R t) at hp
  rw [real_inner_comm, ← hp]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht] using hs
  change inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseHeat g o d (t - s).toNNReal (R s)) =
    Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) * inner ℝ (R s) (scalarBaseEigenvector g o d i)
  rw [real_inner_comm, scalarBaseHeat_selfAdjoint, scalarBaseHeat_eigenvector, real_inner_smul_right]
  unfold scalarBaseHeatWeight scalarBaseHeatRate
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs'.2)]
  ring_nf

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak minimum equation becomes the pointwise geometric Euler
equation once its actual representative is smooth and positive. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarSmoothEuler_frameCompact
local instance scalarSmoothEuler_probability_r3780e6_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_subcritical_minimum_one_of_positive_representative [PreconnectedSpace M]
    (g : SmoothMetric M) (o : FrameOrientation g) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : 0 < ‖w‖ ^ 2)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (a : SmoothScalar (M := M)) (hpos : ∀ x, 0 < a.val x)
    (hrep : scalarWeightedBaseLp g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w =ᵐ[normalizedVolume g] a.val) :
    ‖w‖ ^ 2 = 1 ∧ ∀ x, a.val x = 1 := by
  obtain ⟨hnorm, heuler⟩ := scalar_subcritical_pointwise_euler_of_positive_representative
    g o d hp hp4 w hw hmin a hpos hrep
  exact scalar_positive_normalized_euler_minimum_one g o hRic a hpos hp hp4 hm hnorm heuler

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp subcritical scalar inequality from the actual normalized
minimum, once its positive smooth representative has been established. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarSubcriticalBound_frameCompact
local instance scalarSubcriticalBound_probability_r3780e6_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_subcritical_bound_of_positive_representative
    (g : SmoothMetric M) (o : FrameOrientation g) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : 0 < ‖w‖ ^ 2)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (a : SmoothScalar (M := M)) (hpos : ∀ x, 0 < a.val x)
    (hrep : scalarWeightedBaseLp g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w =ᵐ[normalizedVolume g] a.val)
    (b : SmoothScalar (M := M)) :
    (∫ x, |b.val x| ^ p ∂normalizedVolume g) ^ (2 / p) ≤
      (∫ x, b.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet d b b / 2 := by
  have hmone := (scalar_subcritical_minimum_one_of_positive_representative
    g o hRic d hp hp4 w hw hm hmin a hpos hrep).1
  have h := hmin (smoothScalarToWeightedH1 d b)
  rw [hmone, one_mul, smoothScalarToWeightedH1_norm_sq o d b] at h
  have hnorm : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) (smoothScalarToWeightedH1 d b)‖ ^ 2 =
        (∫ x, |b.val x| ^ p ∂normalizedVolume g) ^ (2 / p) := by
    rw [scalarLp_norm_sq_eq_moment (by linarith : 0 < p)]
    congr 1
    apply integral_congr_ae
    filter_upwards [scalarWeightedBaseLp_smooth g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) b] with x hx
    rw [hx]
  rwa [hnorm] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Trace summability follows from the actual bounded scalar heat evaluation
map and integration of Bessel's inequality over normalized volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarTrace_probability
instance scalarBaseEigenIndex_countable : Countable (ScalarBaseEigenIndex g o d) := by
  apply Set.countable_univ_iff.mp
  have h := (scalarHeat_weight_summable g o d 1 zero_lt_one).countable_support
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  simp only [Set.mem_univ, Function.mem_support, scalarBaseHeatWeight, ne_eq, Real.exp_ne_zero,
    not_false_eq_true]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The scalar diagonal is the squared norm of the half-time evaluation
column. Its integral is the actual infinite spectral trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatDiagonal (t : ℝ≥0) (ht : 0 < t) (x : M) : ℝ :=
  ‖scalarHeatColumn g o d (t / 2) (half_pos ht) x‖ ^ 2

theorem scalarHeatColumn_norm_square (t : ℝ≥0) (ht : 0 < t) (x : M) :
    ‖scalarHeatColumn g o d t ht x‖ ^ 2 =
      ∑' i : ScalarBaseEigenIndex g o d,
        (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x) ^ 2 := by
  let v := scalarHeatColumn g o d t ht x
  have h := (scalarBaseEigenbasis g o d).repr.inner_map_map v v
  rw [lp.inner_eq_tsum] at h
  rw [← real_inner_self_eq_norm_sq, ← h]
  apply tsum_congr
  intro i
  rw [HilbertBasis.repr_apply_apply, real_inner_self_eq_norm_sq]
  have hbi : scalarBaseEigenbasis g o d i = scalarBaseEigenvector g o d i := by
    simp only [scalarBaseEigenbasis, HilbertBasis.coe_mk]
  rw [hbi]
  have he : inner ℝ (scalarBaseEigenvector g o d i) v =
      scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x :=
    (real_inner_comm _ _).trans (scalarHeatColumn_pairing g o d t ht x _)
  rw [he, Real.norm_eq_abs, sq_abs]

theorem scalarHeatDiagonal_series (t : ℝ≥0) (ht : 0 < t) (x : M) :
    scalarHeatDiagonal g o d t ht x =
      ∑' i : ScalarBaseEigenIndex g o d,
        (scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) x) ^ 2 :=
  scalarHeatColumn_norm_square g o d (t / 2) (half_pos ht) x

theorem scalarHeatDiagonal_integral (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, scalarHeatDiagonal g o d t ht x ∂normalizedVolume g) =
      ∑' i : ScalarBaseEigenIndex g o d, scalarBaseHeatWeight g o d t i := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let F := fun (i : ScalarBaseEigenIndex g o d) (x : M) =>
    (scalarHeatToContinuous g o d (t / 2) (half_pos ht) (scalarBaseEigenvector g o d i) x) ^ 2
  have hi (i : ScalarBaseEigenIndex g o d) : Integrable (F i) (normalizedVolume g) :=
    ((scalarHeatToContinuous g o d (t / 2) (half_pos ht) _).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖F i x‖ ∂normalizedVolume g) := by
    have h := scalarHeat_weight_square_summable g o d (t / 2) (half_pos ht)
    apply h.congr
    intro i
    simp only [F, Real.norm_eq_abs, abs_sq]
    exact (scalarHeat_eigen_integral g o d (t / 2) (half_pos ht) i).symm
  simp_rw [scalarHeatDiagonal_series]
  change (∫ x, ∑' i, F i x ∂normalizedVolume g) = _
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro i
  rw [scalarHeat_eigen_integral]
  simp only [scalarBaseHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeatLiftSource_resolvent (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarBaseResolvent g o d (scalarBaseHeatLiftSource g o d t ht f) = scalarBaseHeat g o d t f := by
  simpa only [pow_one, scalarBaseHeatLiftSource] using scalarBaseHeatPowerSource_resolvent g o d t ht 1 f

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant scalar heat mode has multiplicity exactly one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_9
theorem scalarBase_fixed_space_eq_span (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap 1 =
      Submodule.span ℝ {smoothScalarBaseL2 g (smoothScalarConst 1)} := by
  apply le_antisymm
  · intro f hf
    have hfix : scalarBaseResolvent g o d f = f := by
      have he : scalarBaseResolvent g o d f = (1 : ℝ) • f :=
        Module.End.mem_eigenspace_iff.mp hf
      exact he.trans (one_smul ℝ f)
    obtain ⟨c, hc⟩ := scalarBaseResolvent_fixed_constant g o d hRic f hfix
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton _))
  · apply Submodule.span_le.mpr
    intro f hf
    rw [mem_singleton_iff] at hf
    subst f
    apply Module.End.mem_eigenspace_iff.mpr
    change scalarBaseResolvent g o d (smoothScalarBaseL2 g (smoothScalarConst 1)) =
      (1 : ℝ) • smoothScalarBaseL2 g (smoothScalarConst 1)
    rw [one_smul]
    exact scalarBaseResolvent_fixed_one g o d

theorem scalarBase_fixed_finrank (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Module.finrank ℝ (Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap 1) = 1 := by
  rw [scalarBase_fixed_space_eq_span hRic d]
  exact finrank_span_singleton (smoothScalarBaseL2_one_ne_zero (o := o))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar heat output in H1, with its exact smooth realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_11
theorem scalarHeatH1Lift_value (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarH1BaseValue g o d (scalarHeatH1Lift d t ht f) = scalarBaseHeat g o d t f :=
  scalarBaseHeatLiftSource_resolvent g o d t ht f

theorem scalarHeatH1Lift_smooth (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (normalizedVolume g))
    (u : SmoothScalar (M := M)) (hu : scalarBaseHeat g o d t f = smoothScalarBaseL2 g u) :
    scalarHeatH1Lift d t ht f = smoothScalarToH1 d u := by
  apply scalarH1BaseValue_injective g o d
  rw [scalarHeatH1Lift_value, scalarH1BaseValue_smooth, hu]

theorem scalarHeatH1Lift_eigen (t : ℝ≥0) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    scalarHeatH1Lift d t ht (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i • smoothScalarToH1 d (scalarBaseEigenfunction g o d i) := by
  apply scalarH1BaseValue_injective g o d
  rw [scalarHeatH1Lift_value, map_smul, scalarH1BaseValue_smooth,
    ← scalarBaseEigenfunction_L2, scalarBaseHeat_eigenvector]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat kernel is obtained from actual evaluation columns.
Its integral action, symmetry and diagonal follow from the semigroup law. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarKernel_probability
theorem scalarHeatToContinuous_add (t s : ℝ≥0) (ht : 0 < t) (hs : 0 < s)
    (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarHeatToContinuous g o d (t + s) (add_pos ht hs) f =
      scalarHeatToContinuous g o d t ht (scalarBaseHeat g o d s f) := by
  let := normalizedVolume_isOpenPosMeasure g
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)
  rw [scalarHeatToContinuous_L2, scalarHeatToContinuous_L2, scalarBaseHeat_add]

def scalarHeatKernel (t : ℝ≥0) (ht : 0 < t) (x y : M) : ℝ :=
  scalarHeatToContinuous g o d (t / 2) (half_pos ht)
    (scalarHeatColumn g o d (t / 2) (half_pos ht) x) y

theorem scalarHeatKernel_pairing (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    scalarHeatKernel g o d t ht x y = inner ℝ
      (scalarHeatColumn g o d (t / 2) (half_pos ht) y)
      (scalarHeatColumn g o d (t / 2) (half_pos ht) x) :=
  (scalarHeatColumn_pairing g o d (t / 2) (half_pos ht) y _).symm

theorem scalarHeatKernel_diagonal (t : ℝ≥0) (ht : 0 < t) (x : M) :
    scalarHeatKernel g o d t ht x x = scalarHeatDiagonal g o d t ht x := by
  rw [scalarHeatKernel_pairing, real_inner_self_eq_norm_sq]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual scalar heat kernel. The spectral
series converges uniformly, using the bounded positive-time evaluation map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeatContinuous_eigen_split (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) :
    scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d (t / 2) i •
        scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) := by
  have h := scalarHeatToContinuous_add g o d (t / 2) (t / 2)
    (half_pos ht) (half_pos ht) (scalarBaseEigenvector g o d i)
  simpa only [add_halves, scalarBaseHeat_eigenvector, map_smul] using h

theorem scalarHeatContinuous_eigen_bound (t : ℝ≥0) (ht : 0 < t)
    (i : ScalarBaseEigenIndex g o d) (x : M) :
    |scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x| ≤
      scalarBaseHeatWeight g o d (t / 2) i *
        ‖scalarHeatToContinuous g o d (t / 2) (half_pos ht)‖ := by
  rw [scalarHeatContinuous_eigen_split]
  change |scalarBaseHeatWeight g o d (t / 2) i * _| ≤ _
  have hp : 0 < scalarBaseHeatWeight g o d (t / 2) i := Real.exp_pos _
  rw [abs_mul, abs_of_pos hp]
  have h := scalarHeatToContinuous_bound g o d (t / 2) (half_pos ht)
    (scalarBaseEigenvector g o d i) x
  rw [(scalarBaseEigenvector_orthonormal g o d).1 i] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h hp.le

theorem scalarHeatKernel_hasSum (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    HasSum (fun i : ScalarBaseEigenIndex g o d =>
      scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) y *
        scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) x)
      (scalarHeatKernel g o d t ht x y) := by
  have h := (scalarBaseEigenbasis g o d).hasSum_inner_mul_inner
    (scalarHeatColumn g o d (t / 2) (half_pos ht) y)
    (scalarHeatColumn g o d (t / 2) (half_pos ht) x)
  rw [← scalarHeatKernel_pairing g o d t ht x y] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  rw [scalarBaseEigenbasis_apply, scalarHeatColumn_pairing]
  rw [← scalarHeatColumn_pairing g o d (t / 2) (half_pos ht) x]
  exact congrArg (_ * ·) (real_inner_comm _ _)

theorem scalarHeatKernel_continuous (t : ℝ≥0) (ht : 0 < t) :
    Continuous (fun p : M × M => scalarHeatKernel g o d t ht p.1 p.2) := by
  let C := ‖scalarHeatToContinuous g o d (t / 2 / 2) (half_pos (half_pos ht))‖
  have hs : Summable (fun i : ScalarBaseEigenIndex g o d =>
      scalarBaseHeatWeight g o d (t / 2) i * C ^ 2) :=
    (scalarHeat_weight_summable g o d (t / 2) (half_pos ht)).mul_right _
  have hb (i : ScalarBaseEigenIndex g o d) (p : M × M) :
      ‖scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) p.2 *
        scalarHeatToContinuous g o d (t / 2) (half_pos ht)
          (scalarBaseEigenvector g o d i) p.1‖ ≤
        scalarBaseHeatWeight g o d (t / 2) i * C ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul]
    have hx := scalarHeatContinuous_eigen_bound g o d (t / 2) (half_pos ht) i p.1
    have hy := scalarHeatContinuous_eigen_bound g o d (t / 2) (half_pos ht) i p.2
    have hp : 0 ≤ scalarBaseHeatWeight g o d (t / 2 / 2) i := (Real.exp_pos _).le
    refine (mul_le_mul hy hx (abs_nonneg _) (mul_nonneg hp
      (norm_nonneg (scalarHeatToContinuous g o d (t / 2 / 2)
        (half_pos (half_pos ht)))))).trans_eq ?_
    dsimp only [C]
    rw [mul_mul_mul_comm, ← pow_two, scalarBaseHeatWeight_half_sq]
    rw [pow_two]
  have hc := continuous_tsum
    (fun i : ScalarBaseEigenIndex g o d =>
      ((scalarHeatToContinuous g o d (t / 2) (half_pos ht)
        (scalarBaseEigenvector g o d i)).continuous.comp continuous_snd).mul
      ((scalarHeatToContinuous g o d (t / 2) (half_pos ht)
        (scalarBaseEigenvector g o d i)).continuous.comp continuous_fst)) hs hb
  exact hc.congr (fun p => (scalarHeatKernel_hasSum g o d t ht p.1 p.2).tsum_eq)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-time versions of the actual scalar heat evaluation column and
diagonal, with their exact squared-column identity at doubled time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatRealColumn (t : ℝ) (x : M) : Lp ℝ 2 (normalizedVolume g) :=
  if ht : 0 < t then scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht) x else 0

def scalarHeatRealDiagonal (t : ℝ) (x : M) : ℝ :=
  if ht : 0 < t then scalarHeatDiagonal g o d t.toNNReal (Real.toNNReal_pos.mpr ht) x else 0

theorem scalarHeatRealColumn_pos (t : ℝ) (ht : 0 < t) (x : M) :
    scalarHeatRealColumn g o d t x =
      scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht) x := dite_eq_left ht

theorem scalarHeatRealDiagonal_columns (t : ℝ) (ht : 0 < t) (x : M) :
    scalarHeatRealDiagonal g o d (t + t) x = ‖scalarHeatRealColumn g o d t x‖ ^ 2 := by
  have he : (t + t).toNNReal / 2 = t.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_ofNat, Real.coe_toNNReal _ ht.le,
      Real.coe_toNNReal _ (add_nonneg ht.le ht.le)]
    ring
  rw [scalarHeatRealDiagonal, dite_eq_left (add_pos ht ht), scalarHeatRealColumn_pos g o d t ht]
  unfold scalarHeatDiagonal
  simp only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp scalar Sobolev inequality and the two Weyl gaps follow from
actual variational minima, their proved positive smooth regularity, Euler
rigidity and the critical exponent limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.sharpScalar_frameCompact
theorem actual_scalar_subcritical_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ) (hp : 2 < p) (hp4 : p < 4) (b : SmoothScalar (M := M)) :
    (∫ x, |b.val x| ^ p ∂normalizedVolume g) ^ (2 / p) ≤
      (∫ x, b.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet d b b / 2 := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)⟩
  obtain ⟨w, hw, hm, hm1, hn, hmin⟩ :=
    scalar_subcritical_nonnegative_minimum g o d hp hp4
  obtain ⟨v, hv, hrep, hpos⟩ :=
    scalar_subcritical_minimum_positive_smooth g o d hp hp4 w hw hm1 hmin hn
  exact scalar_subcritical_bound_of_positive_representative g o hRic d hp hp4
    w hw hm hmin ⟨v, hv⟩ hpos hrep b

theorem actual_sharpScalarSobolev (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    SharpScalarSobolev o d :=
  sharpScalarSobolev_of_subcritical_moments g o d
    (fun p hp hp4 b => actual_scalar_subcritical_bound g o hRic d p hp hp4 b)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-one de Rham vanishing: every actual smooth closed one-form is
the differential of a smooth scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothScalar_primitive (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hu : smoothOneFormExterior (o := o) u = 0) :
    ∃ f : SmoothScalar (M := M), u = smoothScalarDifferential g f := by
  obtain ⟨f, hf, hlap⟩ := actual_petersen_poisson g o hRic
    (oneFormDivergence g u) (oneFormDivergence_smooth u)
  let F : SmoothScalar (M := M) := ⟨f,hf⟩
  let v := u - smoothScalarDifferential g F
  have hc : smoothOneFormExterior (o := o) v = 0 := by
    change smoothOneFormExteriorLinear (u - smoothScalarDifferential g F) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hu.trans (smoothScalarDifferential_closed F).symm)
  have hm := oneFormDivergence_mean_zero (o := o) hRic u
  have ht (e : FrameBundle g) :
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g v.val) e ![i,i]) = 0 := by
    rw [← oneFormDivergence_eq_frame]
    have hd := congrArg (fun a : SmoothScalar (M := M) => a.val e.base)
      (map_sub (smoothOneFormDivergence g) u (smoothScalarDifferential g F))
    change oneFormDivergence g v e.base =
      oneFormDivergence g u e.base - oneFormDivergence g (smoothScalarDifferential g F) e.base at hd
    rw [hd, oneFormDivergence_differential]
    have hl := hlap e
    rw [hm, sub_zero] at hl
    exact sub_eq_zero.mpr hl.symm
  have hv : v = 0 := oneForm_harmonic_eq_zero hRic v hc ht
  exact ⟨F, sub_eq_zero.mp hv⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual regularized Weyl energy and sharp scalar inequality give
the limiting Holder inequality needed for equality rigidity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.gapLimitFrameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.gapLimitProbability
theorem actual_weyl_gap_limiting_inequality (hRic : RicciThree g) :
    Real.sqrt (∫ x, ((plusNorm o x ^ 2) ^ (1 / 3 : ℝ)) ^ 2 ∂normalizedVolume g) ≤
      ∫ x, plusNorm o x * (plusNorm o x ^ 2) ^ (1 / 3 : ℝ) ∂normalizedVolume g := by
  let p := canonicalParallelMetricData g o hRic
  let d := p.toMetricGreenData
  let v : C(M, ℝ) := ⟨plusNorm o, continuous_plusNorm g o⟩
  have hs (n : ℕ) :
      Real.sqrt (∫ x, (v x ^ 2 + weylGapEpsilon n ^ 2) ^ (2 / 3 : ℝ) ∂normalizedVolume g) ≤
        (∫ x, v x * (v x ^ 2 + weylGapEpsilon n ^ 2) ^ (1 / 3 : ℝ) ∂normalizedVolume g) +
          weylGapEpsilon n ^ (2 / 3 : ℝ) := by
    let ε := weylGapEpsilon n
    have hε := weylGapEpsilon_pos n
    have hsob := sharpScalarSobolev_regularized o p (canonicalParallelMetricData_orientation o hRic)
      (actual_sharpScalarSobolev g o hRic p) ε hε
    have henergy := d.weylRoot_energy_le ε hε
    have hi₁ : Integrable (fun e => ∑ i, d.weylRootFirstField ε hε i e ^ 2)
        (canonicalFrameMeasure g o) :=
      (continuous_finsetSum _ (fun i _ => (d.weylRootFirstField ε hε i).continuous.pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi₂ : Integrable (fun e => 2 * d.weylRootField ε e ^ 2)
        (canonicalFrameMeasure g o) :=
      ((d.weylRootField ε).continuous.pow 2).const_mul 2
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_add hi₁ hi₂, integral_const_mul, probReal_univ, mul_one] at henergy
    have hbound : Real.sqrt (∫ e, d.weylRootField ε e ^ 4 ∂canonicalFrameMeasure g o) ≤
        (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) *
          d.weylRootField ε e ^ 2 ∂canonicalFrameMeasure g o) + ε ^ (2 / 3 : ℝ) := by
      linarith
    have h4 := weylRoot_weighted_moment (o := o) hRic ε 0 4
    have h2 := weylRoot_weighted_moment (o := o) hRic ε 1 2
    norm_num only [pow_zero, one_mul, pow_one, Nat.cast_ofNat] at h4 h2
    simpa only [h4, h2, v, ContinuousMap.coe_mk, d, p, ε] using hbound
  have ht4 := integral_weyl_regularized_power_tendsto (normalizedVolume g) v 1
    (2 / 3 : ℝ) (by norm_num)
  simp only [ContinuousMap.one_apply, one_mul] at ht4
  have ht2 := integral_weyl_regularized_power_tendsto (normalizedVolume g) v v
    (1 / 3 : ℝ) (by norm_num)
  have htε := weylGapEpsilon_tendsto.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))
  have hlim := le_of_tendsto_of_tendsto (Real.continuous_sqrt.continuousAt.tendsto.comp ht4)
    (ht2.add htε) (Eventually.of_forall hs)
  simp only [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), add_zero] at hlim
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Real.rpow_mul_natCast (sq_nonneg _)]
  norm_num [v]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual closed/exact degree-one quotient vanishes under Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFieldsSmoothClosedOneForms
theorem smoothExactOneForms_eq_top (hRic : RicciThree g) :
    smoothExactOneForms (o := o) = ⊤ := by
  apply top_unique
  intro u _
  obtain ⟨f, hf⟩ := exists_smoothScalar_primitive hRic u.val u.property
  change u.val ∈ LinearMap.range (smoothScalarDifferentialLinear g)
  exact ⟨f, hf.symm⟩

theorem oneFormDeRhamCohomology_eq_zero (hRic : RicciThree g)
    (u : OneFormDeRhamCohomology (o := o)) : u = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := smoothExactOneForms (o := o)) u
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [smoothExactOneForms_eq_top hRic]
  trivial

theorem oneFormDeRhamCohomology_subsingleton (hRic : RicciThree g) :
    Subsingleton (OneFormDeRhamCohomology (o := o)) :=
  ⟨fun u v => (oneFormDeRhamCohomology_eq_zero hRic u).trans
    (oneFormDeRhamCohomology_eq_zero hRic v).symm⟩

theorem oneFormDeRhamCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (OneFormDeRhamCohomology (o := o)) = 0 := by
  let _ := oneFormDeRhamCohomology_subsingleton (o := o) hRic
  exact Module.finrank_zero_of_subsingleton

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual weak harmonic kernel and the smooth closed and coclosed
two-forms coincide. The equivalence uses proved elliptic regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHarmonicToWeak_surjective (hRic : RicciThree g) :
    Function.Surjective (smoothHarmonicToWeak (o := o) hRic) := by
  intro u
  obtain ⟨v, hv, he⟩ := twoFormHarmonic_smooth_H1 hRic u.val u.property
  refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
  exact he.symm

def smoothHarmonicWeakEquiv (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) ≃ₗ[ℝ] twoFormWeitzenbockKernel (o := o) :=
  LinearEquiv.ofBijective (smoothHarmonicToWeak hRic)
    ⟨smoothHarmonicToWeak_injective hRic, smoothHarmonicToWeak_surjective hRic⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The eigenvalue one of the actual shifted resolvent is exactly the
smooth harmonic space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothHarmonicResolventEquiv (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) ≃ₗ[ℝ]
      Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 :=
  (smoothHarmonicWeakEquiv hRic).trans (twoFormWeakHarmonicResolventEquiv hRic)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal harmonic projection and smooth Poisson decomposition of
actual two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothHodge_decomposition (hRic : RicciThree g) (f : smoothTwoForms o) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∃ u : smoothTwoForms o, f = h + smoothHodgeLaplacian hRic u := by
  obtain ⟨h, hh, hperp⟩ := exists_smoothHarmonic_projection hRic f
  obtain ⟨u, hu⟩ := exists_smoothHodgePoisson_pointwise hRic (f - h) hperp
  refine ⟨h, hh, u, ?_⟩
  rw [hu]
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! The geometric Hodge Laplacian splits as dδ + *dδ*. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothHodge_exact_coexact (hRic : RicciThree g) (f : smoothTwoForms o) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∃ a b : smoothCovariantFields (M := M) 1,
        f = h + smoothOneFormExterior a + smoothTwoFormHodge o (smoothOneFormExterior b) := by
  obtain ⟨h, hh, u, hu⟩ := exists_smoothHodge_decomposition hRic f
  refine ⟨h, hh, smoothTwoFormCodifferentialField u,
    smoothTwoFormCodifferentialField (smoothTwoFormHodge o u), ?_⟩
  rw [smoothHodgeLaplacian_dDelta_hodge hRic] at hu
  exact hu.trans (by abel)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closed two-forms are orthogonal to coexact forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem exists_smoothHodge_closed_decomposition (hRic : RicciThree g)
    (f : smoothTwoForms o) (hf : smoothTwoFormExterior f = 0) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∃ a : smoothCovariantFields (M := M) 1, f = h + smoothOneFormExterior a := by
  obtain ⟨h, hh, a, b, he⟩ := exists_smoothHodge_exact_coexact hRic f
  let w := smoothTwoFormHodge o (smoothOneFormExterior b)
  have hhclosed : smoothTwoFormExterior h = 0 := hh.1
  have ha := smoothOneFormExterior_closed (o := o) hRic a
  have hF := smoothOneForm_coexact_orthogonal_closed hRic b f hf
  have hH := smoothOneForm_coexact_orthogonal_closed hRic b h hhclosed
  have hA := smoothOneForm_coexact_orthogonal_closed hRic b (smoothOneFormExterior a) ha
  change smoothTwoFormL2Inner w f = 0 at hF
  change smoothTwoFormL2Inner w h = 0 at hH
  change smoothTwoFormL2Inner w (smoothOneFormExterior a) = 0 at hA
  have hw : smoothTwoFormL2Inner w w = 0 := by
    rw [he, smoothTwoFormL2Inner_add_right, smoothTwoFormL2Inner_add_right,
      hH, hA, zero_add] at hF
    simpa only [zero_add] using hF
  have hwzero : w = 0 := by
    exact (@inner_self_eq_zero ℝ (SmoothL2TwoForm o) _ _ _ (w : SmoothL2TwoForm o)).mp hw
  refine ⟨h, hh, a, ?_⟩
  change f = h + smoothOneFormExterior a + w at he
  rwa [hwzero, add_zero] at he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-two de Rham cohomology of the actual smooth exterior complex,
and its harmonic representative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_1
theorem smoothHarmonicToDeRham_surjective (hRic : RicciThree g) :
    Function.Surjective (smoothHarmonicToDeRham (o := o)) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (p := smoothExactTwoForms (o := o)) q
  obtain ⟨h, hh, a, he⟩ := exists_smoothHodge_closed_decomposition hRic f.val f.property
  refine ⟨⟨h, hh⟩, ?_⟩
  apply (Submodule.Quotient.eq (smoothExactTwoForms (o := o))).mpr
  change h - f.val ∈ LinearMap.range (smoothOneFormExteriorLinear (o := o))
  refine ⟨-a, ?_⟩
  rw [map_neg]
  change -smoothOneFormExterior a = h - f.val
  rw [he]
  abel

def smoothHarmonicDeRhamEquiv (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) ≃ₗ[ℝ] TwoFormDeRhamCohomology (o := o) :=
  LinearEquiv.ofBijective smoothHarmonicToDeRham
    ⟨smoothHarmonicToDeRham_injective hRic, smoothHarmonicToDeRham_surjective hRic⟩

theorem twoFormDeRhamCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (TwoFormDeRhamCohomology (o := o)) =
      Module.finrank ℝ (smoothHarmonicTwoForms (o := o)) :=
  (smoothHarmonicDeRhamEquiv (o := o) hRic).symm.finrank_eq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second de Rham dimension is the sum of the two actual Hodge
eigenspace dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_2
theorem twoFormDeRhamCohomology_hodge_dimension (hRic : RicciThree g) :
    Module.finrank ℝ (TwoFormDeRhamCohomology (o := o)) =
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) +
        Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  rw [twoFormDeRhamCohomology_finrank hRic,
    ← (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq, Module.finrank_prod]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual coclosed/codifferential quotient. This is the upper-degree
Hodge-dual complex written in one-form coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.hodgeDualClosedAddGroup
theorem smoothCoexactOneForms_eq_top (hRic : RicciThree g) :
    smoothCoexactOneForms (o := o) = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := exists_smoothCoexact_of_divergence_eq_zero (o := o) hRic v.val v.property
  change v.val ∈ LinearMap.range (smoothTwoFormCodifferentialLinear (o := o))
  exact ⟨u, hu.symm⟩

theorem hodgeDualOneCohomology_eq_zero (hRic : RicciThree g)
    (q : HodgeDualOneCohomology (o := o)) : q = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := smoothCoexactOneForms (o := o)) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [smoothCoexactOneForms_eq_top hRic]
  trivial

theorem hodgeDualOneCohomology_subsingleton (hRic : RicciThree g) :
    Subsingleton (HodgeDualOneCohomology (o := o)) :=
  ⟨fun u v => (hodgeDualOneCohomology_eq_zero hRic u).trans
    (hodgeDualOneCohomology_eq_zero hRic v).symm⟩

theorem hodgeDualOneCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (HodgeDualOneCohomology (o := o)) = 0 := by
  let _ := hodgeDualOneCohomology_subsingleton (o := o) hRic
  exact Module.finrank_zero_of_subsingleton

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cokernel of actual smooth divergence is measured exactly by the
scalar integral. No upper-degree index identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M}

variable [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.divergenceMeanCompactFrames
theorem mem_divergence_range_iff_mean_zero (o : FrameOrientation g) (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) :
    f ∈ LinearMap.range (smoothOneFormDivergence g) ↔ smoothScalarMean g o f = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact oneFormDivergence_mean_zero (o := o) hRic v
  · intro hmean
    obtain ⟨φ, hφ, hlap⟩ := actual_petersen_poisson g o hRic f.val f.property
    let F : SmoothScalar (M := M) := ⟨φ, hφ⟩
    refine ⟨smoothScalarDifferential g F, ?_⟩
    apply Subtype.ext
    funext x
    let e := frameAt g x
    have he := hlap e
    change (∫ e, f.val e.base ∂canonicalFrameMeasure g o) = 0 at hmean
    rw [hmean, sub_zero] at he
    exact (oneFormDivergence_differential F e).trans he

theorem divergenceCokernelMean_zero (o : FrameOrientation g) (hRic : RicciThree g)
    (q : DivergenceCokernel g) (hq : divergenceCokernelMean o hRic q = 0) : q = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := LinearMap.range (smoothOneFormDivergence g)) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (mem_divergence_range_iff_mean_zero o hRic f).mpr
  exact hq

theorem divergenceCokernelMean_bijective (o : FrameOrientation g) (hRic : RicciThree g) :
    Function.Bijective (divergenceCokernelMean o hRic) := by
  constructor
  · intro u v huv
    apply sub_eq_zero.mp
    apply divergenceCokernelMean_zero o hRic
    rw [map_sub, huv, sub_self]
  · intro r
    refine ⟨(LinearMap.range (smoothOneFormDivergence g)).mkQ (smoothScalarConst r), ?_⟩
    exact smoothScalarMean_const o r

def divergenceCokernelEquiv (o : FrameOrientation g) (hRic : RicciThree g) :
    DivergenceCokernel g ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (divergenceCokernelMean o hRic)
    (divergenceCokernelMean_bijective o hRic)

theorem divergenceCokernel_finrank (o : FrameOrientation g) (hRic : RicciThree g) :
    Module.finrank ℝ (DivergenceCokernel g) = 1 := by
  rw [(divergenceCokernelEquiv o hRic).finrank_eq]
  exact Module.finrank_self ℝ

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The integral intersection form descends to the actual de Rham
quotient and is nondegenerate there. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_4_r3780e6_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms_1
def deRhamIntersection (hRic : RicciThree g) :
    TwoFormDeRhamCohomology (o := o) →ₗ[ℝ] TwoFormDeRhamCohomology (o := o) →ₗ[ℝ] ℝ :=
  (smoothHarmonicIntersection (o := o)).compl₁₂
    (smoothHarmonicDeRhamEquiv hRic).symm.toLinearMap
    (smoothHarmonicDeRhamEquiv hRic).symm.toLinearMap

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute convergence of the actual positive-time spectral heat kernel.
Splitting the time in half reduces convergence to the proved diagonal bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatSection_pointwise_square_summable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (x : M) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := twoFormHeat_diagonal_bound (o := o) hRic t ht
  exact summable_of_sum_le (fun _ => sq_nonneg _) (fun s => hC s x)

def twoFormHeatKernelTerm (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) (i : TwoFormEigenIndex (o := o) hRic) : TwoFormFour →L[ℝ] TwoFormFour :=
  InnerProductSpace.rankOne ℝ
    ((twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x)
    ((twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val y)

theorem twoFormHeatKernelTerm_norm_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) : Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖twoFormHeatKernelTerm hRic t ht x y i‖) := by
  have hx := twoFormHeatSection_pointwise_square_summable (o := o) hRic (t / 2) (half_pos ht) x
  have hy := twoFormHeatSection_pointwise_square_summable (o := o) hRic (t / 2) (half_pos ht) y
  apply (hx.add hy).of_norm_bounded
  intro i
  rw [norm_norm, twoFormHeatKernelTerm, InnerProductSpace.norm_rankOne]
  nlinarith [sq_nonneg
    (‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ -
      ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val y‖)]

theorem twoFormHeatKernelTerm_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) : Summable (twoFormHeatKernelTerm (o := o) hRic t ht x y) := by
  have := FiniteDimensional.complete ℝ (TwoFormFour →L[ℝ] TwoFormFour)
  exact (twoFormHeatKernelTerm_norm_summable (o := o) hRic t ht x y).of_norm

def twoFormHeatKernel (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    TwoFormFour →L[ℝ] TwoFormFour :=
  ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatKernelTerm hRic t ht x y i

theorem twoFormHeatKernel_hasSum (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    HasSum (twoFormHeatKernelTerm (o := o) hRic t ht x y) (twoFormHeatKernel (o := o) hRic t ht x y) :=
  (twoFormHeatKernelTerm_summable hRic t ht x y).hasSum

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signature of the actual degree-two de Rham intersection form,
defined by its maximal positive and negative dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.deRhamSignatureHarmonicAddGroup
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.deRhamSignatureClosedAddGroup
def deRhamIntersectionQuadratic (hRic : RicciThree g) :
    QuadraticForm ℝ (TwoFormDeRhamCohomology (o := o)) :=
  LinearMap.BilinMap.toQuadraticMap (deRhamIntersection hRic)

def harmonicDeRhamIntersectionIsometry (hRic : RicciThree g) :
    (harmonicIntersectionQuadratic (o := o)).IsometryEquiv
      (deRhamIntersectionQuadratic (o := o) hRic) where
  toLinearEquiv := smoothHarmonicDeRhamEquiv hRic
  map_app' u := by
    change smoothHarmonicIntersection
      ((smoothHarmonicDeRhamEquiv hRic).symm ((smoothHarmonicDeRhamEquiv hRic) u))
      ((smoothHarmonicDeRhamEquiv hRic).symm ((smoothHarmonicDeRhamEquiv hRic) u)) =
        smoothHarmonicIntersection u u
    rw [LinearEquiv.symm_apply_apply]

theorem deRhamIntersection_sigPos (hRic : RicciThree g) :
    sigPos (deRhamIntersectionQuadratic (o := o) hRic) =
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  have he : (harmonicIntersectionQuadratic (o := o)).Equivalent
      (deRhamIntersectionQuadratic hRic) := ⟨harmonicDeRhamIntersectionIsometry hRic⟩
  exact he.sigPos_eq.symm.trans (harmonicIntersection_sigPos hRic)

theorem deRhamIntersection_sigNeg (hRic : RicciThree g) :
    sigNeg (deRhamIntersectionQuadratic (o := o) hRic) =
      Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  have he : (harmonicIntersectionQuadratic (o := o)).Equivalent
      (deRhamIntersectionQuadratic hRic) := ⟨harmonicDeRhamIntersectionIsometry hRic⟩
  exact he.sigNeg_eq.symm.trans (harmonicIntersection_sigNeg hRic)

def deRhamSignature (hRic : RicciThree g) : ℤ :=
  (sigPos (deRhamIntersectionQuadratic (o := o) hRic) : ℤ) -
    (sigNeg (deRhamIntersectionQuadratic (o := o) hRic) : ℤ)

theorem deRhamSignature_hodge (hRic : RicciThree g) :
    deRhamSignature (o := o) hRic =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [deRhamSignature, deRhamIntersection_sigPos, deRhamIntersection_sigNeg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual infinite spectral kernel has the expected integrated
diagonal trace. Absolute convergence justifies both exchanges. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

instance twoFormEigenIndexCountable (hRic : RicciThree g) :
    Countable (TwoFormEigenIndex (o := o) hRic) := by
  apply Set.countable_univ_iff.mp
  have h := (twoFormHeat_weight_summable (o := o) hRic 1 zero_lt_one).countable_support
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  simp only [Set.mem_univ, Function.mem_support, twoFormHeatWeight, ne_eq, Real.exp_ne_zero,
    not_false_eq_true]

theorem twoFormHeatKernel_diagonal_trace (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x : M) :
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x) =
      ∑' i : TwoFormEigenIndex (o := o) hRic,
        ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ ^ 2 := by
  have h := (twoFormHeatKernel_hasSum (o := o) hRic t ht x x).mapL twoFormFiberTrace
  simpa only [twoFormFiberTrace_apply, twoFormHeatKernelTerm, InnerProductSpace.trace_rankOne,
    real_inner_self_eq_norm_sq] using h.tsum_eq.symm

theorem twoFormHeatKernel_trace_integral (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x) ∂normalizedVolume g) =
      ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let F := fun (i : TwoFormEigenIndex (o := o) hRic) (x : M) =>
    ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ ^ 2
  have hFi (i : TwoFormEigenIndex (o := o) hRic) : Integrable (F i) (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFsum : Summable (fun i => ∫ x, ‖F i x‖ ∂normalizedVolume g) := by
    have h := twoFormHeat_weight_square_summable (o := o) hRic (t / 2) (half_pos ht)
    apply h.congr
    intro i
    simp only [F, Real.norm_eq_abs, abs_sq]
    exact (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).symm
  simp_rw [twoFormHeatKernel_diagonal_trace]
  change (∫ x, ∑' i, F i x ∂normalizedVolume g) = _
  rw [← integral_tsum_of_summable_integral_norm hFi hFsum]
  apply tsum_congr
  intro i
  exact (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).trans
    (twoFormHeatWeight_half_sq hRic t i.1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer of Hodge trace cancellation to the actual L2 eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSmoothEigenEquiv_hodge (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (u : TwoFormSmoothEigenSpace hRic μ) :
    twoFormSmoothEigenEquiv hRic μ (twoFormSmoothEigenHodge hRic μ u) =
      twoFormEigenspaceHodge hRic μ.val (twoFormSmoothEigenEquiv hRic μ u) := by
  apply Subtype.ext
  exact (twoFormL2Hodge_smooth (u.val : SmoothL2TwoForm o)).symm

theorem twoFormEigenspaceHodge_conj (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    (twoFormSmoothEigenEquiv hRic μ).conj (twoFormSmoothEigenHodge hRic μ) =
      twoFormEigenspaceHodge hRic μ.val := by
  apply LinearMap.ext
  intro f
  obtain ⟨u, rfl⟩ := (twoFormSmoothEigenEquiv hRic μ).surjective f
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact twoFormSmoothEigenEquiv_hodge hRic μ u

theorem twoFormEigenspaceHodge_trace_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val ≠ 1) :
    LinearMap.trace ℝ (TwoFormSpectralSpace hRic μ) (twoFormEigenspaceHodge hRic μ.val) = 0 := by
  rw [← twoFormEigenspaceHodge_conj]
  exact (LinearMap.trace_conj' (R := ℝ) (M := TwoFormSmoothEigenSpace hRic μ)
    (N := TwoFormSpectralSpace hRic μ) (twoFormSmoothEigenHodge hRic μ)
    (twoFormSmoothEigenEquiv hRic μ)).trans (twoFormSmoothEigenHodge_trace_zero hRic μ hμ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The trace on the harmonic eigenspace is the difference of the two
actual harmonic Hodge dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.harmonicTraceAddGroup
theorem smoothHarmonicResolventEquiv_val (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o)) :
    (smoothHarmonicResolventEquiv hRic u).val =
      smoothTwoFormToL2 (u.val : SmoothL2TwoForm o) := by
  change twoFormH1ToL2 (smoothTwoFormToH1 (u.val : SmoothH1TwoForm o)) = _
  exact twoFormH1ToL2_smooth (u.val : SmoothH1TwoForm o)

theorem smoothHarmonicResolventEquiv_hodge (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o)) :
    smoothHarmonicResolventEquiv hRic (smoothHarmonicHodge hRic u) =
      twoFormEigenspaceHodge hRic 1 (smoothHarmonicResolventEquiv hRic u) := by
  apply Subtype.ext
  rw [smoothHarmonicResolventEquiv_val]
  change smoothTwoFormToL2 (smoothL2Hodge (u.val : SmoothL2TwoForm o)) =
    twoFormL2Hodge (smoothHarmonicResolventEquiv hRic u).val
  rw [smoothHarmonicResolventEquiv_val]
  exact (twoFormL2Hodge_smooth (u.val : SmoothL2TwoForm o)).symm

theorem twoFormHarmonicEigenspace_trace (hRic : RicciThree g) :
    LinearMap.trace ℝ (Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1)
      (twoFormEigenspaceHodge hRic 1) =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) := by
  have he : (smoothHarmonicResolventEquiv (o := o) hRic).conj (smoothHarmonicHodge hRic) =
      twoFormEigenspaceHodge hRic 1 := by
    apply LinearMap.ext
    intro f
    obtain ⟨u, rfl⟩ := (smoothHarmonicResolventEquiv hRic).surjective f
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact smoothHarmonicResolventEquiv_hodge hRic u
  rw [← he, LinearMap.trace_conj']
  exact smoothHarmonicHodge_trace hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimensions entering the Euler and signature indices of the
actual scalar/one-form/two-form Hodge complex. Identification of these
indices with curvature integrals is a separate local index calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance hodgeIndexZeroAddGroup_r3780e6_1 : AddCommGroup (ZeroFormDeRhamCohomology g) :=
  Submodule.addCommGroup _
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.hodgeIndexClosedAddGroup
theorem hodgeComplexEuler_hodge (hRic : RicciThree g) :
    hodgeComplexEuler g o = 2 +
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) +
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [hodgeComplexEuler, zeroFormDeRhamCohomology_finrank (o := o) hRic,
    oneFormDeRhamCohomology_finrank hRic, twoFormDeRhamCohomology_hodge_dimension hRic,
    hodgeDualOneCohomology_finrank hRic, divergenceCokernel_finrank o hRic]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalized exterior derivatives of the coexact one-form modes.
They give actual orthonormal two-form lifts, not arbitrary spectral preimages. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

theorem oneFormCoexact_exterior_inner (i j : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothTwoFormL2Inner
      (smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic i))
      (smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic j)) =
        (j.1.val⁻¹ - 1) * inner ℝ (oneFormCoexactEigenvector hRic i) (oneFormCoexactEigenvector hRic j) := by
  rw [smoothTwoFormL2Inner_comm, ← smoothTwoFormCodifferential_pairing hRic,
    oneFormCoexactEigensection_codiff_exterior hRic,
    smoothOneFormL2Pairing_smul]
  rw [← smoothOneFormL2Linear_inner, oneFormCoexactEigensection_L2,
    oneFormCoexactEigensection_L2, real_inner_comm]

theorem oneFormCoexactLift_orthonormal : Orthonormal ℝ (oneFormCoexactLiftL2 (o := o) hRic) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℝ (smoothTwoFormToL2 _ ) (smoothTwoFormToL2 _) = _
  have hp := smoothTwoFormToL2_inner (oneFormCoexactLift hRic i : SmoothL2TwoForm o)
    (oneFormCoexactLift hRic j : SmoothL2TwoForm o)
  change _ = smoothTwoFormL2Inner (oneFormCoexactLift hRic i) (oneFormCoexactLift hRic j) at hp
  rw [hp]
  change smoothTwoFormL2Inner ((Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • _)
    ((Real.sqrt (j.1.val⁻¹ - 1))⁻¹ • _) = _
  rw [smoothTwoFormL2Inner_smul, smoothTwoFormL2Inner_comm,
    smoothTwoFormL2Inner_smul, smoothTwoFormL2Inner_comm, oneFormCoexact_exterior_inner hRic]
  rw [orthonormal_iff_ite.mp (oneFormCoexactEigenvector_orthonormal hRic)]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, if_true]
    have hs := Real.sq_sqrt (oneFormCoexactEigenvector_rate_pos hRic i).le
    calc
      _ = ((Real.sqrt (i.1.val⁻¹ - 1)) ^ 2)⁻¹ * (i.1.val⁻¹ - 1) := by ring
      _ = 1 := by rw [hs, inv_mul_cancel₀ (oneFormCoexactEigenvector_rate_pos hRic i).ne']
  · simp only [hij, ite_false, if_false, mul_zero]

theorem oneFormCoexactLift_codifferential (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField (oneFormCoexactLift hRic i)) =
      Real.sqrt (i.1.val⁻¹ - 1) • oneFormCoexactEigenvector hRic i := by
  rw [oneFormCoexactLift, smoothTwoFormCodifferentialField_smul,
    oneFormCoexactEigensection_codiff_exterior hRic, map_smul, map_smul,
    oneFormCoexactEigensection_L2, smul_smul]
  congr 1
  have hs := Real.sq_sqrt (oneFormCoexactEigenvector_rate_pos hRic i).le
  have hn : Real.sqrt (i.1.val⁻¹ - 1) ≠ 0 :=
    (Real.sqrt_pos.mpr (oneFormCoexactEigenvector_rate_pos hRic i)).ne'
  calc
    _ = (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ * (Real.sqrt (i.1.val⁻¹ - 1)) ^ 2 := by rw [hs]
    _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem oneFormCoexactLift_eigen (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothHodgeLaplacian hRic (oneFormCoexactLift hRic i) =
      (i.1.val⁻¹ - 1) • oneFormCoexactLift hRic i := by
  rw [oneFormCoexactLift, smoothHodgeLaplacian_smul, smoothHodgeLaplacian_exterior hRic,
    oneFormCoexactEigensection_eigen hRic]
  change _ • smoothOneFormExteriorLinear (_ • _) = _
  rw [map_smul]
  exact smul_comm _ _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each nonzero two-form Hodge eigenspace consists of two copies of its
actual coexact one-form image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_nonzero_coexact_multiplicity (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val ≠ 1) :
    Module.finrank ℝ (TwoFormSpectralSpace hRic μ) =
      2 * Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) := by
  have hκ : μ.val⁻¹ - 1 ≠ 0 := by
    simpa only [ne_eq, sub_eq_zero, inv_eq_one] using hμ
  have hS (u : TwoFormSmoothEigenSpace hRic μ) :
      twoFormSmoothEigenHodge hRic μ (twoFormSmoothEigenHodge hRic μ u) = u :=
    congrArg (fun T : Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) => T u)
      (twoFormEigenHodge_square hRic μ)
  have hCA (u : TwoFormSmoothEigenSpace hRic μ) :
      oneFormCodiffEigenMap hRic μ (twoFormSmoothEigenDDelta hRic μ u) =
        (μ.val⁻¹ - 1) • oneFormCodiffEigenMap hRic μ u :=
    congrArg (fun T : TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] OneFormL2 o => T u)
      (twoFormEigenCodiff_DDelta hRic μ)
  have hCSA (u : TwoFormSmoothEigenSpace hRic μ) :
      oneFormCodiffEigenMap hRic μ
        (twoFormSmoothEigenHodge hRic μ (twoFormSmoothEigenDDelta hRic μ u)) = 0 :=
    congrArg (fun T : TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] OneFormL2 o => T u)
      (twoFormEigenCodiff_hodge_DDelta hRic μ)
  have hker (u : TwoFormSmoothEigenSpace hRic μ) (hu : oneFormCodiffEigenMap hRic μ u = 0) :
      twoFormSmoothEigenDDelta hRic μ u = 0 := by
    change smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u.val) = 0 at hu
    have hz : smoothTwoFormCodifferentialField u.val = 0 :=
      smoothOneFormL2Linear_injective (hu.trans (map_zero smoothOneFormL2Linear).symm)
    apply Subtype.ext
    change smoothOneFormExterior (o := o) (smoothTwoFormCodifferentialField u.val) = 0
    rw [hz]
    exact smoothOneFormExteriorLinear.map_zero
  have hs (u : TwoFormSmoothEigenSpace hRic μ) :
      twoFormSmoothEigenDDelta hRic μ u +
        twoFormSmoothEigenHodge hRic μ
          (twoFormSmoothEigenDDelta hRic μ (twoFormSmoothEigenHodge hRic μ u)) =
      (μ.val⁻¹ - 1) • u :=
    congrArg (fun T : Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) => T u)
      (twoFormEigen_DDelta_hodge_split hRic μ)
  have hd := finite_hodge_multiplicity (V := TwoFormSmoothEigenSpace hRic μ)
    (W := OneFormL2 o) (oneFormCodiffEigenMap hRic μ)
    (twoFormSmoothEigenDDelta hRic μ) (twoFormSmoothEigenHodge hRic μ)
    (μ.val⁻¹ - 1) hκ hS hCA hCSA hker hs
  exact (twoFormSmoothEigenEquiv hRic μ).finrank_eq.symm.trans hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The convergent kernel is the spectral kernel formed from the actual
normalized smooth eigenforms, with the original heat weights. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatSection_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatSection hRic t ht (twoFormEigenvector hRic i) =
      twoFormHeatWeight hRic t i.1 • twoFormEigenSection hRic i := by
  have he : smoothTwoFormToL2
        (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i) : SmoothL2TwoForm o) =
      smoothTwoFormToL2
        (twoFormHeatWeight hRic t i.1 • twoFormEigenSection hRic i : SmoothL2TwoForm o) := by
    calc
      _ = twoFormHeat hRic t (twoFormEigenvector hRic i) := twoFormHeatSection_L2 hRic t ht _
      _ = twoFormHeatWeight hRic t i.1 • twoFormEigenvector hRic i := twoFormHeat_eigenvector hRic t i
      _ = _ := ((smoothTwoFormToL2.map_smul (twoFormHeatWeight hRic t i.1)
        (twoFormEigenSection hRic i : SmoothL2TwoForm o)).trans
          (congrArg (twoFormHeatWeight hRic t i.1 • ·) (twoFormEigenSection_L2 hRic i))).symm
  exact smoothTwoFormToL2_injective he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral lifts from actual one-forms to their scalar and
closed two-form potentials. The lifts preserve the spectral parameter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff lp

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

def oneFormLiftSynthesis : ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) →ₗᵢ[ℝ] TwoFormL2 o :=
  modeSynthesis _ (oneFormCoexactLift_orthonormal hRic)

def oneFormCoexactSpectralLift : OneFormL2 o →L[ℝ] TwoFormL2 o :=
  (oneFormLiftSynthesis hRic).toContinuousLinearMap.comp
    (oneFormCoexactSynthesis hRic).toContinuousLinearMap.adjoint

theorem oneFormCoexactSpectralLift_eigen (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormCoexactSpectralLift hRic (oneFormCoexactEigenvector hRic i) = oneFormCoexactLiftL2 hRic i := by
  classical
  have hi := modeSynthesis_single _ (oneFormCoexactEigenvector_orthonormal hRic) i
  change oneFormCoexactSynthesis hRic (lp.single 2 i (1 : ℝ)) = _ at hi
  change oneFormLiftSynthesis hRic
    ((oneFormCoexactSynthesis hRic).toContinuousLinearMap.adjoint _) = _
  rw [← hi]
  have ha := congrArg (fun A : ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) →L[ℝ]
      ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) => A (lp.single 2 i (1 : ℝ)))
    (oneFormCoexactSynthesis hRic).adjoint_comp_self
  change (oneFormCoexactSynthesis hRic).toContinuousLinearMap.adjoint
    (oneFormCoexactSynthesis hRic (lp.single 2 i (1 : ℝ))) = lp.single 2 i (1 : ℝ) at ha
  rw [ha]
  exact modeSynthesis_single _ (oneFormCoexactLift_orthonormal hRic) i

variable [SecondCountableTopology M]
variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormCoexactSpectralLift_exact (i : OneFormExactEigenIndex g o d) :
    oneFormCoexactSpectralLift hRic (oneFormExactEigenvector g o d i) = 0 := by
  have hz : (oneFormCoexactSynthesis (o := o) hRic).toContinuousLinearMap.adjoint
      (oneFormExactEigenvector g o d i) = 0 := by
    apply lp.ext
    funext j
    rw [show (oneFormCoexactSynthesis (o := o) hRic).toContinuousLinearMap.adjoint =
      (modeSynthesis _ (oneFormCoexactEigenvector_orthonormal hRic)).toContinuousLinearMap.adjoint from rfl,
      modeAnalysis_coordinate]
    change _ = 0
    obtain ⟨u, hu, _⟩ := oneFormCoexactEigenvector_smooth (o := o) hRic j
    rw [hu, oneFormExactEigenvector, real_inner_smul_right, real_inner_comm]
    rw [oneForm_exact_coexact_orthogonal hRic, mul_zero]
  change oneFormLiftSynthesis hRic _ = _
  exact (congrArg (oneFormLiftSynthesis hRic) hz).trans (map_zero _)

theorem oneFormExactSpectralLift_eigen (i : OneFormExactEigenIndex g o d) :
    oneFormExactSpectralLift d (oneFormExactEigenvector g o d i) = scalarBaseEigenvector g o d i.val := by
  classical
  have hi := modeSynthesis_single _ (oneFormExactEigenvector_orthonormal g o d) i
  change oneFormExactSynthesis d (lp.single 2 i (1 : ℝ)) = _ at hi
  change scalarPositiveSynthesis d
    ((oneFormExactSynthesis d).toContinuousLinearMap.adjoint _) = _
  rw [← hi]
  have ha := congrArg (fun A : ℓ²(OneFormExactEigenIndex g o d, ℝ) →L[ℝ]
      ℓ²(OneFormExactEigenIndex g o d, ℝ) => A (lp.single 2 i (1 : ℝ)))
    (oneFormExactSynthesis d).adjoint_comp_self
  change (oneFormExactSynthesis d).toContinuousLinearMap.adjoint
    (oneFormExactSynthesis d (lp.single 2 i (1 : ℝ))) = lp.single 2 i (1 : ℝ) at ha
  rw [ha]
  exact modeSynthesis_single _ ((scalarBaseEigenvector_orthonormal g o d).comp (fun i : OneFormExactEigenIndex g o d => i.val) Subtype.val_injective) i

theorem oneFormExactSpectralLift_coexact (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormExactSpectralLift d (oneFormCoexactEigenvector hRic i) = 0 := by
  have hz : (oneFormExactSynthesis d).toContinuousLinearMap.adjoint (oneFormCoexactEigenvector hRic i) = 0 := by
    apply lp.ext
    funext j
    rw [show (oneFormExactSynthesis d).toContinuousLinearMap.adjoint =
      (modeSynthesis _ (oneFormExactEigenvector_orthonormal g o d)).toContinuousLinearMap.adjoint from rfl,
      modeAnalysis_coordinate]
    change _ = 0
    obtain ⟨u, hu, _⟩ := oneFormCoexactEigenvector_smooth (o := o) hRic i
    rw [hu, oneFormExactEigenvector, real_inner_smul_left,
      oneForm_exact_coexact_orthogonal hRic, mul_zero]
  change scalarPositiveSynthesis d _ = _
  exact (congrArg (scalarPositiveSynthesis d) hz).trans (map_zero _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact H1 realizations of smooth two-form heat outputs and coexact lifts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

theorem twoFormHeat_coexactLift (t : ℝ≥0) (i : OneFormCoexactEigenIndex (o := o) hRic) :
    twoFormHeat hRic t (oneFormCoexactLiftL2 hRic i) =
      twoFormHeatWeight hRic t i.1 • oneFormCoexactLiftL2 hRic i := by
  apply twoFormHeat_eigenvalue hRic t i.1
  apply Module.End.mem_eigenspace_iff.mpr
  apply smoothTwoForm_resolvent_eigen hRic i.1.val (i.1.val⁻¹ - 1) _ (oneFormCoexactLift hRic i)
    (oneFormCoexactLift_eigen hRic i)
  have hn := (twoFormSpectralValue_bounds hRic i.1).1.ne'
  simp only [sub_add_cancel, mul_inv_cancel₀ hn]

theorem twoFormHeatLift_coexactLift (t : ℝ≥0) (ht : 0 < t)
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    twoFormHeatLift hRic t ht (oneFormCoexactLiftL2 hRic i) =
      twoFormHeatWeight hRic t i.1 • smoothTwoFormToH1 (oneFormCoexactLift hRic i : SmoothH1TwoForm o) := by
  apply twoFormH1ToL2_injective hRic
  rw [twoFormHeatLift_value, map_smul]
  exact (twoFormHeat_coexactLift hRic t i).trans
    (congrArg (twoFormHeatWeight hRic t i.1 • ·)
      (twoFormH1ToL2_smooth (oneFormCoexactLift hRic i : SmoothH1TwoForm o)).symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 spectral heat column with one frame and component fixed.
Square summability follows from the proved positive-time diagonal estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatFrameCoefficient_eq (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatFrameCoefficient hRic t e l i =
      twoFormFrameValue o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e l := by
  have h := congrArg (fun v : smoothTwoForms o => twoFormFrameValue o v.val e l)
    (twoFormHeatSection_eigen hRic t ht i)
  change _ = twoFormFrameValue o
    (twoFormHeatWeight hRic t i.1 • (twoFormEigenSection hRic i).val) e l at h
  rw [twoFormFrameValue_smul] at h
  exact h.symm

theorem twoFormHeatFrameCoefficient_mem (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) : Memℓp (twoFormHeatFrameCoefficient (o := o) hRic t e l) 2 := by
  have hs := twoFormHeatSection_pointwise_square_summable (o := o) hRic t ht e.base
  have hn : Memℓp (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e.base‖) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_norm] using hs
  apply hn.mono
  intro i
  rw [twoFormHeatFrameCoefficient_eq hRic t ht]
  exact (PiLp.norm_apply_le _ l).trans_eq
    (twoFormFrameValue_norm o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e)

def twoFormHeatFrameColumn (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) : TwoFormL2 o :=
  (twoFormEigenbasis hRic).repr.symm
    ⟨twoFormHeatFrameCoefficient hRic t e l, twoFormHeatFrameCoefficient_mem hRic t ht e l⟩

theorem twoFormHeatFrameColumn_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) (i : TwoFormEigenIndex (o := o) hRic) :
    inner ℝ (twoFormHeatFrameColumn hRic t ht e l) (twoFormEigenvector hRic i) =
      twoFormHeatFrameCoefficient hRic t e l i := by
  rw [real_inner_comm, ← twoFormEigenbasis_apply hRic i,
    ← HilbertBasis.repr_apply_apply, twoFormHeatFrameColumn,
    LinearIsometryEquiv.apply_symm_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The diagonal trace of the actual heat kernel is the sum of squared
L2 norms of its six half-time frame columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology NNReal ENNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatFrameCoefficient_sq_summable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 6) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      twoFormHeatFrameCoefficient hRic t e l i ^ 2) := by
  have h := (twoFormHeatFrameCoefficient_mem (o := o) hRic t ht e l).summable
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

theorem twoFormHeatFrameColumn_norm_sq (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 6) :
    ‖twoFormHeatFrameColumn (o := o) hRic t ht e l‖ ^ 2 =
      ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatFrameCoefficient hRic t e l i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    ← (twoFormEigenbasis hRic).tsum_inner_mul_inner]
  apply tsum_congr
  intro i
  rw [twoFormEigenbasis_apply, real_inner_comm (twoFormHeatFrameColumn hRic t ht e l),
    twoFormHeatFrameColumn_eigen, pow_two]

theorem twoFormHeatKernel_trace_columns (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) :
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic (t + t) (add_pos ht ht) e.base e.base) =
      ∑ l : Fin 6, ‖twoFormHeatFrameColumn (o := o) hRic t ht e l‖ ^ 2 := by
  rw [twoFormHeatKernel_diagonal_trace]
  have htime : (t + t) / 2 = t := by ring
  simp_rw [htime, twoFormHeatFrameColumn_norm_sq]
  rw [← Summable.tsum_finsetSum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 6))) =>
    twoFormHeatFrameCoefficient_sq_summable hRic t ht e l)]
  apply tsum_congr
  intro i
  rw [← twoFormFrameValue_norm o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e,
    EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro l _
  rw [twoFormHeatFrameCoefficient_eq hRic t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact grouping of the scalar, one-form and two-form heat traces
by the finite eigenspaces of the actual shifted resolvents. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [PreconnectedSpace M] in
theorem oneFormHeatTrace_split (t : ℝ≥0) (ht : 0 < t) :
    oneFormHeatTrace hRic d t = oneFormExactHeatTrace d t + oneFormCoexactHeatTrace (o := o) hRic t := by
  have h := oneFormHeat_weight_summable hRic d t ht
  exact (h.comp_injective (i := Sum.inl) Sum.inl_injective).tsum_sum
    (h.comp_injective (i := Sum.inr) Sum.inr_injective)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem twoFormHeatTrace_grouped (t : ℝ≥0) (ht : 0 < t) :
    twoFormHeatSpectralTrace (o := o) hRic t = ∑' μ : TwoFormSpectralValue (o := o) hRic,
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) := by
  rw [twoFormHeatSpectralTrace, (twoFormHeat_weight_summable hRic t ht).tsum_sigma]
  apply tsum_congr
  intro μ
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormCoexactHeatTrace_grouped (t : ℝ≥0) (ht : 0 < t) :
    oneFormCoexactHeatTrace (o := o) hRic t = ∑' μ : TwoFormSpectralValue (o := o) hRic,
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ) := by
  have h := (twoFormHeat_weight_summable (o := o) hRic t ht).comp_injective
    (i := oneFormCoexactToTwoFormIndex (o := o) hRic) (oneFormCoexactToTwoFormIndex_injective hRic)
  change Summable (fun i : OneFormCoexactEigenIndex (o := o) hRic =>
    twoFormHeatWeight hRic t i.1) at h
  rw [oneFormCoexactHeatTrace, h.tsum_sigma]
  apply tsum_congr
  intro μ
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem twoForm_heat_multiplicity_term (t : ℝ≥0) (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormHeatWeight hRic t μ * (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) =
      2 * (twoFormHeatWeight hRic t μ * (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ)) +
        if μ.val = 1 then (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) else 0 := by
  split_ifs with hμ
  · rw [ oneFormCoexact_harmonic_eq_bot hRic μ hμ, finrank_bot]
    have hw : twoFormHeatWeight hRic t μ = 1 := by simp [twoFormHeatWeight, twoFormHeatRate, hμ]
    rw [hw]
    ring
  · rw [ twoForm_nonzero_coexact_multiplicity hRic μ hμ]
    push_cast
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-time notation for the spectral columns and diagonal trace, with
the zero extension used only to express limits through positive time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatRealColumn (hRic : RicciThree g) (t : ℝ) (e : FrameBundle g)
    (l : Fin 6) : TwoFormL2 o :=
  if ht : 0 < t then twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e l else 0

theorem twoFormHeatRealColumn_pos (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) :
    twoFormHeatRealColumn (o := o) hRic t e l =
      twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e l :=
  dite_eq_left ht

def twoFormHeatRealTrace (hRic : RicciThree g) (t : ℝ) (x : M) : ℝ :=
  if ht : 0 < t then
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t.toNNReal (Real.toNNReal_pos.mpr ht) x x)
  else 0

theorem twoFormHeatRealTrace_columns (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (e : FrameBundle g) :
    twoFormHeatRealTrace (o := o) hRic (t + t) e.base =
      ∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2 := by
  simpa only [twoFormHeatRealTrace, dite_eq_left (add_pos ht ht), twoFormHeatRealColumn,
    dite_eq_left ht, Real.toNNReal_add ht.le ht.le] using
    twoFormHeatKernel_trace_columns hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneFormHeatConvolution_norm_le (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (R : ℝ → OneFormL2 o) (t : ℝ) (ht : 0 ≤ t) (B : ℝ)
    (hR : ∀ s ∈ Icc 0 t, ‖R s‖ ≤ B * s) :
    ‖oneFormHeatConvolution hRic d R t‖ ≤ B * t ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => B * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, B * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hi
      exact Filter.Eventually.of_forall fun s hs =>
        (oneFormHeat_contraction hRic d (t - s).toNNReal (R s)).trans
          (hR s ⟨hs.1.le, hs.2⟩)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A bounded inverse square root on the strictly positive degree-one spectrum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormInverseSquareRoot_eigen (i : OneFormEigenIndex hRic d) :
    oneFormInverseSquareRoot hRic d (oneFormEigenvector hRic d i) =
      (Real.sqrt (oneFormHeatRate hRic d i))⁻¹ • oneFormEigenvector hRic d i := by
  classical
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext j
  rw [oneFormInverseSquareRoot, oneFormSpectralMultiplier_coordinate, map_smul]
  have hbi : oneFormEigenbasis hRic d i = oneFormEigenvector hRic d i := by
    simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  have hb : oneFormSpectralEquiv hRic d (oneFormEigenvector hRic d i) = lp.single 2 i (1 : ℝ) := by
    change (oneFormEigenbasis hRic d).repr _ = _
    simpa only [hbi] using (oneFormEigenbasis hRic d).repr_self i
  rw [hb]
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

def oneFormTwoFormPotential : OneFormL2 o →L[ℝ] TwoFormL2 o :=
  (oneFormCoexactSpectralLift hRic).comp (oneFormInverseSquareRoot hRic d)

theorem oneFormScalarPotential_exact (i : OneFormExactEigenIndex g o d) :
    oneFormScalarPotential hRic d (oneFormExactEigenvector g o d i) =
      (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • scalarBaseEigenvector g o d i.val := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inl i)
  change oneFormInverseSquareRoot hRic d (oneFormExactEigenvector g o d i) =
    (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • oneFormExactEigenvector g o d i at h
  change oneFormExactSpectralLift d (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormExactSpectralLift_eigen]

theorem oneFormScalarPotential_coexact (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormScalarPotential hRic d (oneFormCoexactEigenvector hRic i) = 0 := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inr i)
  change oneFormInverseSquareRoot hRic d (oneFormCoexactEigenvector hRic i) =
    (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • oneFormCoexactEigenvector hRic i at h
  change oneFormExactSpectralLift d (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormExactSpectralLift_coexact, smul_zero]

theorem oneFormTwoFormPotential_coexact (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormTwoFormPotential hRic d (oneFormCoexactEigenvector hRic i) =
      (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • oneFormCoexactLiftL2 hRic i := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inr i)
  change oneFormInverseSquareRoot hRic d (oneFormCoexactEigenvector hRic i) =
    (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • oneFormCoexactEigenvector hRic i at h
  change oneFormCoexactSpectralLift hRic (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormCoexactSpectralLift_eigen]

theorem oneFormTwoFormPotential_exact (i : OneFormExactEigenIndex g o d) :
    oneFormTwoFormPotential hRic d (oneFormExactEigenvector g o d i) = 0 := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inl i)
  change oneFormInverseSquareRoot hRic d (oneFormExactEigenvector g o d i) =
    (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • oneFormExactEigenvector g o d i at h
  change oneFormCoexactSpectralLift hRic (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormCoexactSpectralLift_exact, smul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Counting a fixed eigenvalue in the actual finite eigenspace indexing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeat_zero_weight_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : ScalarBaseEigenIndex g o d => if i.1.val = 1 then (1 : ℝ) else 0) := by
  classical
  apply Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity) _
    (scalarHeat_weight_summable g o d t ht)
  intro i
  split_ifs with hi
  · simp only [scalarBaseHeatWeight, scalarBaseHeatRate, hi, inv_one, sub_self,
      mul_zero, Real.exp_zero, le_refl]
  · exact (Real.exp_pos _).le

theorem scalarHeat_zero_weight_sum (t : ℝ≥0) (ht : 0 < t) :
    (∑' i : ScalarBaseEigenIndex g o d, if i.1.val = 1 then (1 : ℝ) else 0) =
      (Module.finrank ℝ (Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap 1) : ℝ) := by
  classical
  rw [(scalarHeat_zero_weight_summable d t ht).tsum_sigma]
  convert tsum_eigenvalue_finrank (scalarBaseResolvent g o d).toLinearMap using 1
  all_goals try with_reducible_and_instances rfl
  apply tsum_congr
  intro μ
  rw [tsum_fintype]
  split_ifs <;> simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic Hodge-signed diagonal trace of the actual heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatKernel_signed_diagonal (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (x : M) :
    twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t ht x x) =
      ∑' i : TwoFormEigenIndex (o := o) hRic,
        inner ℝ ((twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x)
          (twoFormHodge ((twoFormHeatSection hRic (t / 2) (half_pos ht)
            (twoFormEigenvector hRic i)).val x)) := by
  have hs := (twoFormHeatKernel_hasSum (o := o) hRic t ht x x).mapL twoFormFiberSignedTrace
  simpa only [twoFormHeatKernelTerm, twoFormFiberSignedTrace_rankOne] using hs.tsum_eq.symm

theorem twoFormHeatSection_signed_integral (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ x, inner ℝ ((twoFormHeatSection hRic (t / 2) (half_pos ht)
        (twoFormEigenvector hRic i)).val x)
      (twoFormHodge ((twoFormHeatSection hRic (t / 2) (half_pos ht)
        (twoFormEigenvector hRic i)).val x)) ∂normalizedVolume g) =
      twoFormHeatWeight hRic t i.1 *
        inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i)) := by
  rw [smoothTwoForm_hodge_pairing_integral, twoFormHeatSection_L2, twoFormHeat_eigenvector,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← pow_two, twoFormHeatWeight_half_sq]

theorem twoFormHeatKernel_signed_integral (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t ht x x)
      ∂normalizedVolume g) =
      ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 *
        inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i)) := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let w := fun i : TwoFormEigenIndex (o := o) hRic =>
    twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)
  let F := fun i x => inner ℝ ((w i).val x) (twoFormHodge ((w i).val x))
  have hFi (i) : Integrable (F i) (normalizedVolume g) :=
    smoothTwoForm_pairing_integrable (w i) (smoothTwoFormHodge o (w i))
  have hbound (i) : (∫ x, ‖F i x‖ ∂normalizedVolume g) ≤ twoFormHeatWeight hRic t i.1 := by
    calc
      _ ≤ ∫ x, ‖(w i).val x‖ ^ 2 ∂normalizedVolume g := by
        apply integral_mono (hFi i).norm
          (((smoothTwoForm_norm_continuous (w i)).pow 2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
        intro x
        change ‖inner ℝ ((w i).val x) (twoFormHodge ((w i).val x))‖ ≤ ‖(w i).val x‖ ^ 2
        exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans_eq (by rw [twoFormHodge.norm_map, pow_two])
      _ = _ := (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).trans
        (twoFormHeatWeight_half_sq hRic t i.1)
  have hFs := Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg (F i x)))
    hbound (twoFormHeat_weight_summable (o := o) hRic t ht)
  simp_rw [twoFormHeatKernel_signed_diagonal]
  change (∫ x, ∑' i, F i x ∂normalizedVolume g) = _
  rw [← integral_tsum_of_summable_integral_norm hFi hFs]
  exact tsum_congr (fun i => twoFormHeatSection_signed_integral hRic t ht i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruction of the actual one-form heat operator by differentiated
scalar and two-form heat potentials. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_23_r3780e6_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
def oneFormHeatReconstructed (t : ℝ≥0) (ht : 0 < t) : OneFormL2 o →L[ℝ] OneFormL2 o :=
  (scalarH1Differential d).comp ((scalarHeatH1Lift d t ht).comp (oneFormScalarPotential hRic d)) +
    (twoFormH1Codifferential hRic).comp ((twoFormHeatLift hRic t ht).comp (oneFormTwoFormPotential hRic d))

theorem oneFormHeatReconstructed_exact (t : ℝ≥0) (ht : 0 < t)
    (i : OneFormExactEigenIndex g o d) :
    oneFormHeatReconstructed hRic d t ht (oneFormExactEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i.val • oneFormExactEigenvector g o d i := by
  change scalarH1Differential d (scalarHeatH1Lift d t ht (oneFormScalarPotential hRic d _)) +
    twoFormH1Codifferential hRic (twoFormHeatLift hRic t ht (oneFormTwoFormPotential hRic d _)) = _
  rw [oneFormScalarPotential_exact, oneFormTwoFormPotential_exact, map_zero, map_zero, add_zero,
    map_smul, scalarHeatH1Lift_eigen, map_smul, map_smul, scalarH1Differential_smooth]
  change _ = _ • ((Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • _)
  rw [smul_comm]
  rfl

theorem oneFormHeatReconstructed_coexact (t : ℝ≥0) (ht : 0 < t)
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormHeatReconstructed hRic d t ht (oneFormCoexactEigenvector hRic i) =
      twoFormHeatWeight hRic t i.1 • oneFormCoexactEigenvector hRic i := by
  change scalarH1Differential d (scalarHeatH1Lift d t ht (oneFormScalarPotential hRic d _)) +
    twoFormH1Codifferential hRic (twoFormHeatLift hRic t ht (oneFormTwoFormPotential hRic d _)) = _
  rw [oneFormScalarPotential_coexact, oneFormTwoFormPotential_coexact, map_zero, map_zero, zero_add,
    map_smul, twoFormHeatLift_coexactLift, map_smul, map_smul]
  have hc := twoFormH1Codifferential_smooth hRic (oneFormCoexactLift hRic i : SmoothH1TwoForm o)
  rw [hc]
  change (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • (twoFormHeatWeight hRic t i.1 •
      smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField (oneFormCoexactLift hRic i))) = _
  rw [oneFormCoexactLift_codifferential, smul_smul, smul_smul]
  congr 1
  have hn : Real.sqrt (i.1.val⁻¹ - 1) ≠ 0 :=
    (Real.sqrt_pos.mpr (oneFormCoexactEigenvector_rate_pos hRic i)).ne'
  calc
    _ = twoFormHeatWeight hRic t i.1 * ((Real.sqrt (i.1.val⁻¹ - 1))⁻¹ * Real.sqrt (i.1.val⁻¹ - 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, mul_one]

theorem oneFormHeat_reconstructed (t : ℝ≥0) (ht : 0 < t) :
    oneFormHeatReconstructed hRic d t ht = oneFormHeat hRic d t := by
  apply ContinuousLinearMap.ext
  intro f
  apply sub_eq_zero.mp
  have he (i : OneFormEigenIndex hRic d) :
      (oneFormHeatReconstructed hRic d t ht - oneFormHeat hRic d t) (oneFormEigenvector hRic d i) ∈
        (⊥ : Submodule ℝ (OneFormL2 o)) := by
    rw [Submodule.mem_bot]
    change oneFormHeatReconstructed hRic d t ht (oneFormEigenvector hRic d i) -
      oneFormHeat hRic d t (oneFormEigenvector hRic d i) = (0 : OneFormL2 o)
    rw [oneFormHeat_eigenvector]
    rcases i with i | i
    · change oneFormHeatReconstructed hRic d t ht (oneFormExactEigenvector g o d i) -
        scalarBaseHeatWeight g o d t i.val • oneFormExactEigenvector g o d i = 0
      rw [oneFormHeatReconstructed_exact, sub_self]
    · change oneFormHeatReconstructed hRic d t ht (oneFormCoexactEigenvector hRic i) -
        twoFormHeatWeight hRic t i.1 • oneFormCoexactEigenvector hRic i = 0
      rw [oneFormHeatReconstructed_coexact, sub_self]
  exact continuousLinearMap_mem_closed_of_total (oneFormEigenvector hRic d)
    (oneFormEigenvector_total hRic d) (oneFormHeatReconstructed hRic d t ht - oneFormHeat hRic d t)
    ⊥ isClosed_singleton he f

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat trace consists of its positive modes and one constant mode. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

include hRic in
theorem scalarHeatTrace_split (t : ℝ≥0) (ht : 0 < t) :
    scalarHeatSpectralTrace d t = oneFormExactHeatTrace d t + 1 := by
  classical
  have hs := scalarHeat_weight_summable g o d t ht
  have he := hs.tsum_subtype_add_tsum_subtype_compl
    {i : ScalarBaseEigenIndex g o d | 0 < scalarBaseHeatRate g o d i}
  have hz : (∑' i : {i : ScalarBaseEigenIndex g o d |
      i ∈ {i | 0 < scalarBaseHeatRate g o d i}ᶜ}, scalarBaseHeatWeight g o d t i.val) = 1 := by
    rw [tsum_subtype]
    have hi : {i : ScalarBaseEigenIndex g o d | i ∈ {i | 0 < scalarBaseHeatRate g o d i}ᶜ}.indicator
        (scalarBaseHeatWeight g o d t) =
        (fun i => if i.1.val = 1 then (1 : ℝ) else 0) := by
      funext i
      by_cases h : i.1.val = 1
      · have hr := (scalarBaseHeatRate_eq_zero g o d i).mpr h
        simp [Set.indicator, hr, scalarBaseHeatWeight, h]
      · have hr : 0 < scalarBaseHeatRate g o d i :=
          lt_of_le_of_ne (scalarBaseHeatRate_nonneg g o d i)
            (Ne.symm (fun he => h ((scalarBaseHeatRate_eq_zero g o d i).mp he)))
        simp [Set.indicator, hr, h]
    rw [hi, scalarHeat_zero_weight_sum d t ht, scalarBase_fixed_finrank hRic d]
    norm_num
  change oneFormExactHeatTrace d t + _ = scalarHeatSpectralTrace d t at he
  have hz' : (∑' i : ↑{i : ScalarBaseEigenIndex g o d | 0 < scalarBaseHeatRate g o d i}ᶜ,
      scalarBaseHeatWeight g o d t i.val) = 1 := hz
  rw [hz'] at he
  exact he.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time Hodge-signed heat trace equals the harmonic signature.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_signed_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1 *
      inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i))) := by
  apply (twoFormHeat_weight_summable (o := o) hRic t ht).of_norm_bounded
  intro i
  have hw : 0 ≤ twoFormHeatWeight hRic t i.1 := (Real.exp_pos _).le
  rw [norm_mul, Real.norm_of_nonneg hw]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (twoFormEigenvector hRic i)
    (twoFormL2Hodge (twoFormEigenvector hRic i))
  rw [twoFormL2Hodge_norm, (twoFormEigenvector_orthonormal hRic).1 i, one_mul] at hb
  exact (mul_le_mul_of_nonneg_left hb hw).trans_eq (mul_one _)

theorem twoFormHeat_spectral_signed_trace (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    (∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 *
      inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i))) =
    LinearMap.trace ℝ (Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1)
      (twoFormEigenspaceHodge hRic 1) := by
  classical
  have he : (∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 *
      inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i))) =
      ∑' μ : TwoFormSpectralValue (o := o) hRic, twoFormHeatWeight hRic t μ *
        LinearMap.trace ℝ (TwoFormSpectralSpace hRic μ) (twoFormEigenspaceHodge hRic μ.val) := by
    rw [(twoFormHeat_signed_summable (o := o) hRic t ht).tsum_sigma]
    apply tsum_congr
    intro μ
    rw [tsum_fintype]
    change (∑ j, twoFormHeatWeight hRic t μ * inner ℝ
      (twoFormEigenvector hRic ⟨μ,j⟩) (twoFormL2Hodge (twoFormEigenvector hRic ⟨μ,j⟩))) = _
    rw [← Finset.mul_sum, ← twoFormEigenspaceHodge_trace_basis]
  rw [he]
  by_cases h1 : Module.End.HasEigenvalue (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1
  · let μ₁ : TwoFormSpectralValue (o := o) hRic := ⟨1, h1⟩
    rw [tsum_eq_single μ₁]
    · have hw : twoFormHeatWeight hRic t μ₁ = 1 := by simp [twoFormHeatWeight, twoFormHeatRate, μ₁]
      rw [hw, one_mul]
      rfl
    · intro μ hμ
      have hne : μ.val ≠ 1 := fun hv => hμ (Subtype.ext hv)
      rw [twoFormEigenspaceHodge_trace_zero hRic μ hne, mul_zero]
  · have hbot : Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 = ⊥ :=
      not_ne_iff.mp h1
    have hsub : Subsingleton (Module.End.eigenspace
        (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1) := by
      rw [hbot]
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    have hzero : twoFormEigenspaceHodge (o := o) hRic 1 = 0 := by
      have := hsub
      exact Subsingleton.elim _ _
    rw [hzero, map_zero]
    calc
      _ = ∑' _μ : TwoFormSpectralValue (o := o) hRic, (0 : ℝ) := by
        apply tsum_congr
        intro μ
        have hne : μ.val ≠ 1 := by
          intro hv
          exact h1 (hv ▸ μ.property)
        rw [twoFormEigenspaceHodge_trace_zero hRic μ hne, mul_zero]
      _ = 0 := tsum_zero

theorem twoFormHeatKernel_signature_trace (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t ht x x)
      ∂normalizedVolume g) =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) := by
  rw [twoFormHeatKernel_signed_integral hRic t ht, twoFormHeat_spectral_signed_trace hRic t ht,
    twoFormHarmonicEigenspace_trace hRic]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed spectral diagonal as the Gram sum of its six columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff Manifold _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatFrameColumn_inner (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l m : Fin 6) :
    inner ℝ (twoFormHeatFrameColumn (o := o) hRic t ht e l)
      (twoFormHeatFrameColumn (o := o) hRic t ht e m) =
      ∑' i, twoFormHeatFrameCoefficient (o := o) hRic t e l i * twoFormHeatFrameCoefficient (o := o) hRic t e m i := by
  rw [← (twoFormEigenbasis (o := o) hRic).tsum_inner_mul_inner]
  apply tsum_congr
  intro i
  rw [twoFormEigenbasis_apply,
    real_inner_comm (twoFormHeatFrameColumn (o := o) hRic t ht e m),
    twoFormHeatFrameColumn_eigen, twoFormHeatFrameColumn_eigen]

theorem twoFormHeatFrameCoefficient_product_summable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l m : Fin 6) :
    Summable (fun i => twoFormHeatFrameCoefficient (o := o) hRic t e l i *
      twoFormHeatFrameCoefficient (o := o) hRic t e m i) := by
  have h := (twoFormEigenbasis (o := o) hRic).summable_inner_mul_inner
    (twoFormHeatFrameColumn (o := o) hRic t ht e l) (twoFormHeatFrameColumn (o := o) hRic t ht e m)
  simpa only [twoFormEigenbasis_apply,
    real_inner_comm (twoFormHeatFrameColumn (o := o) hRic t ht e m), twoFormHeatFrameColumn_eigen] using h

theorem twoFormHeatKernel_signed_columns (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic (t + t) (add_pos ht ht) e.base e.base) =
      ∑ l, ∑ m, twoFormHodgeMatrix l m *
        inner ℝ (twoFormHeatFrameColumn (o := o) hRic t ht e l) (twoFormHeatFrameColumn (o := o) hRic t ht e m) := by
  rw [twoFormHeatKernel_signed_diagonal]
  have htime : (t + t) / 2 = t := by ring
  simp only [htime, twoFormHeatFrameColumn_inner (o := o)]
  have hs (l m : Fin 6) := (twoFormHeatFrameCoefficient_product_summable (o := o) hRic t ht e l m).mul_left
    (twoFormHodgeMatrix l m)
  simp_rw [← tsum_mul_left]
  have hsum (l : Fin 6) : (∑ m, ∑' i,
      twoFormHodgeMatrix l m * (twoFormHeatFrameCoefficient (o := o) hRic t e l i *
        twoFormHeatFrameCoefficient (o := o) hRic t e m i)) =
      ∑' i, ∑ m, twoFormHodgeMatrix l m * (twoFormHeatFrameCoefficient (o := o) hRic t e l i *
        twoFormHeatFrameCoefficient (o := o) hRic t e m i) :=
    (Summable.tsum_finsetSum (fun m _ => hs l m)).symm
  simp_rw [hsum]
  rw [← Summable.tsum_finsetSum (fun l _ => summable_sum (fun m _ => hs l m))]
  apply tsum_congr
  intro i
  have hp := twoFormFrameValue_inner (o := o)
    (twoFormHeatSection (o := o) hRic t ht (twoFormEigenvector (o := o) hRic i)).val
    (fun x => twoFormHodge ((twoFormHeatSection (o := o) hRic t ht (twoFormEigenvector (o := o) hRic i)).val x)) e
  rw [twoFormFrameValue_hodge o _ e he, twoFormHodge_inner_coordinates] at hp
  rw [← hp]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [twoFormHeatFrameCoefficient_eq hRic t ht, twoFormHeatFrameCoefficient_eq hRic t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form heat trace is twice its coexact trace plus the harmonic dimension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

theorem twoFormHeat_grouped_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ)) := by
  have hs := (twoFormHeat_weight_summable (o := o) hRic t ht).sigma
  apply hs.congr
  intro μ
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem oneFormCoexactHeat_grouped_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ)) := by
  have hs := ((twoFormHeat_weight_summable (o := o) hRic t ht).comp_injective
    (i := oneFormCoexactToTwoFormIndex (o := o) hRic)
      (oneFormCoexactToTwoFormIndex_injective hRic)).sigma
  apply hs.congr
  intro μ
  change (∑' j : Fin (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ)),
    twoFormHeatWeight hRic t μ) = _
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem twoFormHeatTrace_split (t : ℝ≥0) (ht : 0 < t) :
    twoFormHeatSpectralTrace (o := o) hRic t =
      2 * oneFormCoexactHeatTrace (o := o) hRic t +
        (Module.finrank ℝ (smoothHarmonicTwoForms (o := o)) : ℝ) := by
  classical
  have hg := twoFormHeat_grouped_summable (o := o) hRic t ht
  have hc := oneFormCoexactHeat_grouped_summable (o := o) hRic t ht
  have hz : Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      if μ.val = 1 then (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) else 0) := by
    apply (hg.sub (hc.mul_left 2)).congr
    intro μ
    rw [twoForm_heat_multiplicity_term hRic t μ]
    ring
  rw [twoFormHeatTrace_grouped hRic t ht, oneFormCoexactHeatTrace_grouped hRic t ht]
  calc
    _ = ∑' μ : TwoFormSpectralValue (o := o) hRic,
        (2 * (twoFormHeatWeight hRic t μ *
          (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ)) +
            if μ.val = 1 then (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) else 0) :=
      tsum_congr (twoForm_heat_multiplicity_term hRic t)
    _ = _ := by
      rw [(hc.mul_left 2).tsum_add hz, tsum_mul_left,
        tsum_eigenvalue_finrank (twoFormShiftedResolvent (o := o) hRic).toLinearMap,
        ← (smoothHarmonicResolventEquiv (o := o) hRic).finrank_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual de Rham heat supertrace equals the Euler index at positive time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_5
theorem hodgeHeat_supertrace (t : ℝ≥0) (ht : 0 < t) :
    2 * scalarHeatSpectralTrace d t - 2 * oneFormHeatTrace hRic d t +
      twoFormHeatSpectralTrace (o := o) hRic t = (hodgeComplexEuler g o : ℝ) := by
  rw [scalarHeatTrace_split hRic d t ht, oneFormHeatTrace_split hRic d t ht,
    twoFormHeatTrace_split hRic t ht, hodgeComplexEuler_hodge hRic]
  have hd := (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq
  rw [Module.finrank_prod] at hd
  rw [← hd]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every positive-time output of the actual one-form heat semigroup is smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_24_r3780e6_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
theorem oneFormHeat_smooth_representative (t : ℝ≥0) (ht : 0 < t) (f : OneFormL2 o) :
    ∃ u : smoothCovariantFields M 1, smoothOneFormL2Linear (o := o) u = oneFormHeat hRic d t f := by
  obtain ⟨a, ha⟩ := scalarBaseHeat_smooth_representative g o d t ht (oneFormScalarPotential hRic d f)
  let b := twoFormHeatSection hRic t ht (oneFormTwoFormPotential hRic d f)
  have hb := twoFormHeatSection_L2 hRic t ht (oneFormTwoFormPotential hRic d f)
  refine ⟨smoothScalarDifferential g a + smoothTwoFormCodifferentialField b, ?_⟩
  rw [← oneFormHeat_reconstructed hRic d t ht]
  change smoothOneFormL2Linear (o := o) (_ + _) =
    scalarH1Differential d (scalarHeatH1Lift d t ht (oneFormScalarPotential hRic d f)) +
      twoFormH1Codifferential hRic (twoFormHeatLift hRic t ht (oneFormTwoFormPotential hRic d f))
  rw [map_add, scalarHeatH1Lift_smooth d t ht _ a ha,
    twoFormHeatLift_smooth hRic t ht _ b hb.symm,
    scalarH1Differential_smooth]
  have hc := twoFormH1Codifferential_smooth hRic (b : SmoothH1TwoForm o)
  rw [hc]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded continuous evaluation of actual positive-time one-form heat. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
  (t : ℝ≥0) (ht : 0 < t)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_25
def oneFormHeatC0Value (f : OneFormL2 o) : OneFormC0 g :=
  ⟨smoothOneFormEuclideanValue (g := g) (oneFormHeat_smooth_representative hRic d t ht f).choose,
    Submodule.le_topologicalClosure _ ⟨(oneFormHeat_smooth_representative hRic d t ht f).choose, rfl⟩⟩

theorem oneFormHeatC0Value_L2 (f : OneFormL2 o) :
    oneFormC0ToFrameLp (o := o) (oneFormHeatC0Value hRic d t ht f) =
      oneFormFrameL2 (oneFormHeat hRic d t f) := by
  change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
    (smoothOneFormEuclideanValue (g := g) _) = _
  rw [← oneFormFrameL2_smooth]
  exact congrArg oneFormFrameL2 (oneFormHeat_smooth_representative hRic d t ht f).choose_spec

def oneFormHeatC0Linear : OneFormL2 o →ₗ[ℝ] OneFormC0 g where
  toFun := oneFormHeatC0Value hRic d t ht
  map_add' f v := by
    apply oneFormC0ToFrameLp_injective (o := o)
    rw [map_add, oneFormHeatC0Value_L2, oneFormHeatC0Value_L2, oneFormHeatC0Value_L2,
      map_add, map_add]
  map_smul' r f := by
    apply oneFormC0ToFrameLp_injective (o := o)
    rw [map_smul, oneFormHeatC0Value_L2, oneFormHeatC0Value_L2, map_smul, map_smul]
    rfl

theorem oneFormHeatC0_graph_closed : IsClosed ((oneFormHeatC0Linear hRic d t ht).graph :
    Set (OneFormL2 o × OneFormC0 g)) := by
  have he : ((oneFormHeatC0Linear hRic d t ht).graph : Set (OneFormL2 o × OneFormC0 g)) =
      {p | oneFormC0ToFrameLp (o := o) p.2 = oneFormFrameL2 (oneFormHeat hRic d t p.1)} := by
    ext p
    change p.2 = oneFormHeatC0Value hRic d t ht p.1 ↔
      oneFormC0ToFrameLp (o := o) p.2 = oneFormFrameL2 (oneFormHeat hRic d t p.1)
    constructor
    · intro hp
      rw [hp]
      exact oneFormHeatC0Value_L2 hRic d t ht p.1
    · intro hp
      apply oneFormC0ToFrameLp_injective (o := o)
      exact hp.trans (oneFormHeatC0Value_L2 hRic d t ht p.1).symm
  rw [he]
  exact isClosed_eq (oneFormC0ToFrameLp.continuous.comp continuous_snd)
    (oneFormFrameL2.continuous.comp ((oneFormHeat hRic d t).continuous.comp continuous_fst))

theorem oneFormHeatC0_continuous : Continuous (oneFormHeatC0Linear hRic d t ht) := by
  exact @LinearMap.continuous_of_isClosed_graph ℝ _ (OneFormL2 o) _ _ _
    (OneFormC0 g) _ _ _ (oneFormHeatC0Linear hRic d t ht)
    (oneFormHeatC0_graph_closed hRic d t ht)

def oneFormHeatToC0 : OneFormL2 o →L[ℝ] OneFormC0 g where
  toLinearMap := oneFormHeatC0Linear hRic d t ht
  cont := oneFormHeatC0_continuous hRic d t ht

def oneFormHeatToContinuous : OneFormL2 o →L[ℝ] C(FrameBundle g, FourSpace) :=
  (oneFormContinuousSubspace g).subtypeL.comp (oneFormHeatToC0 hRic d t ht)

theorem oneFormHeatToContinuous_smooth (f : OneFormL2 o) (u : smoothCovariantFields M 1)
    (hu : smoothOneFormL2Linear (o := o) u = oneFormHeat hRic d t f) :
    oneFormHeatToContinuous hRic d t ht f = smoothOneFormEuclideanValue (g := g) u := by
  have he := (oneFormHeat_smooth_representative hRic d t ht f).choose_spec
  have hs := smoothOneFormL2Linear_injective (he.trans hu.symm)
  change smoothOneFormEuclideanValue (g := g) _ = _
  rw [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Genuine L2 Riesz columns for one-form heat evaluation in an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_26_r3780e6_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
def oneFormHeatEvaluation (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) :
    OneFormL2 o →L[ℝ] ℝ :=
  (EuclideanSpace.proj l).comp ((ContinuousMap.evalCLM ℝ e).comp (oneFormHeatToContinuous hRic d t ht))

def oneFormHeatFrameColumn (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) : OneFormL2 o :=
  (InnerProductSpace.toDual ℝ (OneFormL2 o)).symm (oneFormHeatEvaluation hRic d t ht e l)

theorem oneFormHeatFrameColumn_pairing (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) (f : OneFormL2 o) :
    inner ℝ (oneFormHeatFrameColumn hRic d t ht e l) f = oneFormHeatToContinuous hRic d t ht f e l :=
  InnerProductSpace.toDual_symm_apply

theorem oneFormHeatContinuous_eigen (t : ℝ≥0) (ht : 0 < t) (i : OneFormEigenIndex hRic d) :
    oneFormHeatToContinuous hRic d t ht (oneFormEigenvector hRic d i) =
      oneFormHeatWeight hRic d t i • smoothOneFormEuclideanValue (g := g) (oneFormEigenSection hRic d i) := by
  have hu : smoothOneFormL2Linear (o := o) (oneFormHeatWeight hRic d t i • oneFormEigenSection hRic d i) =
      oneFormHeat hRic d t (oneFormEigenvector hRic d i) := by
    rw [map_smul, oneFormEigenSection_L2, oneFormHeat_eigenvector]
  have he := oneFormHeatToContinuous_smooth hRic d t ht _ _ hu
  rw [he]
  exact (smoothOneFormContinuousLinear (g := g)).map_smul _ _

theorem oneFormHeatFrameColumn_eigen (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    inner ℝ (oneFormHeatFrameColumn hRic d t ht e l) (oneFormEigenvector hRic d i) =
      oneFormHeatWeight hRic d t i * covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l] := by
  rw [oneFormHeatFrameColumn_pairing, oneFormHeatContinuous_eigen]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form diagonal heat density and its frame-column realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_27_r3780e6_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
omit [PreconnectedSpace M] in
instance oneFormEigenIndex_countable : Countable (OneFormEigenIndex hRic d) := by
  apply Set.countable_univ_iff.mp
  have h := (oneFormHeat_weight_summable hRic d 1 zero_lt_one).countable_support
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  simp only [Set.mem_univ, Function.mem_support, oneFormHeatWeight, ne_eq,
    Real.exp_ne_zero, not_false_eq_true]

theorem oneFormHeatFrameColumn_norm_sq (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) :
    ‖oneFormHeatFrameColumn hRic d t ht e l‖ ^ 2 =
      ∑' i, (oneFormHeatWeight hRic d t i *
        covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l]) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (oneFormEigenbasis hRic d).tsum_inner_mul_inner]
  apply tsum_congr
  intro i
  simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  rw [real_inner_comm (oneFormHeatFrameColumn hRic d t ht e l), oneFormHeatFrameColumn_eigen]
  ring

theorem oneFormHeatFrameCoefficient_sq_summable (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) :
    Summable (fun i => (oneFormHeatWeight hRic d t i *
      covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l]) ^ 2) := by
  have h := (oneFormEigenbasis hRic d).summable_inner_mul_inner
    (oneFormHeatFrameColumn hRic d t ht e l) (oneFormHeatFrameColumn hRic d t ht e l)
  apply h.congr
  intro i
  simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  rw [real_inner_comm (oneFormHeatFrameColumn hRic d t ht e l), oneFormHeatFrameColumn_eigen]
  ring

theorem oneFormHeatDiagonal_summable (t : ℝ≥0) (ht : 0 < t) (x : M) :
    Summable (fun i => oneFormHeatWeight hRic d t i *
      covariantFieldNormSq g (oneFormEigenSection hRic d i).val x) := by
  have hs := (hasSum_sum (s := Finset.univ) (fun l _ =>
    (oneFormHeatFrameCoefficient_sq_summable hRic d (t / 2) (half_pos ht)
      (frameAt g x) l).hasSum)).summable
  apply hs.congr
  intro i
  have hn : covariantFieldNormSq g (oneFormEigenSection hRic d i).val x =
      frameTensorSquareNorm (covariantFieldFramed g (oneFormEigenSection hRic d i).val (frameAt g x)) :=
    covariantFieldNormSq_eq_frame _ (frameAt g x)
  rw [hn, oneForm_squareNorm,
    ← oneFormHeatWeight_half_sq hRic d t i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem oneFormHeatDiagonal_columns (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) :
    oneFormHeatDiagonal hRic d t e.base =
      ∑ l : Fin 4, ‖oneFormHeatFrameColumn hRic d (t / 2) (half_pos ht) e l‖ ^ 2 := by
  simp_rw [oneFormHeatFrameColumn_norm_sq]
  rw [← Summable.tsum_finsetSum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 4))) =>
    oneFormHeatFrameCoefficient_sq_summable hRic d (t / 2) (half_pos ht) e l)]
  apply tsum_congr
  intro i
  rw [covariantFieldNormSq_eq_frame _ e, oneForm_squareNorm,
    ← oneFormHeatWeight_half_sq hRic d t i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration of the genuine one-form diagonal recovers the spectral heat trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_3
theorem oneFormHeatDiagonal_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (oneFormHeatDiagonal hRic d t) (normalizedVolume g) := by
  have hi (i : OneFormEigenIndex hRic d) : Integrable
      (fun x => oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x) (normalizedVolume g) :=
    (((oneFormEigenSection hRic d i).property.continuous_normSq (g := g)).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖oneFormHeatWeight hRic d t i *
      covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ ∂normalizedVolume g) := by
    apply (oneFormHeat_weight_summable hRic d t ht).congr
    intro i
    have hn (x : M) : ‖oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ =
        oneFormHeatWeight hRic d t i *
          covariantFieldNormSq g (oneFormEigenSection hRic d i).val x :=
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (oneFormEigenSection_norm_nonneg hRic d i x))
    simp_rw [hn]
    rw [integral_const_mul, oneFormEigenSection_norm_integral, mul_one]
  exact scalar_integrable_series hi hs (fun x => (oneFormHeatDiagonal_summable hRic d t ht x).hasSum)

omit [PreconnectedSpace M] in
theorem oneFormHeatDiagonal_integral (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, oneFormHeatDiagonal hRic d t x ∂normalizedVolume g) = oneFormHeatTrace hRic d t := by
  have hi (i : OneFormEigenIndex hRic d) : Integrable
      (fun x => oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x) (normalizedVolume g) :=
    (((oneFormEigenSection hRic d i).property.continuous_normSq (g := g)).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖oneFormHeatWeight hRic d t i *
      covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ ∂normalizedVolume g) := by
    apply (oneFormHeat_weight_summable hRic d t ht).congr
    intro i
    have hn (x : M) : ‖oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ =
        oneFormHeatWeight hRic d t i *
          covariantFieldNormSq g (oneFormEigenSection hRic d i).val x :=
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (oneFormEigenSection_norm_nonneg hRic d i x))
    simp_rw [hn]
    rw [integral_const_mul, oneFormEigenSection_norm_integral, mul_one]
  unfold oneFormHeatDiagonal oneFormHeatTrace
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro i
  rw [integral_const_mul, oneFormEigenSection_norm_integral, mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-time notation for the genuine one-form heat diagonal and columns. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}
variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeatRealColumn (t : ℝ) (e : FrameBundle g) (l : Fin 4) : OneFormL2 o :=
  if ht : 0 < t then oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) e l else 0

theorem oneFormHeatRealColumn_pos (t : ℝ) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) :
    oneFormHeatRealColumn hRic d t e l =
      oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) e l :=
  dite_eq_left ht

def oneFormHeatRealDiagonal (t : ℝ) (x : M) : ℝ :=
  if 0 < t then oneFormHeatDiagonal hRic d t.toNNReal x else 0

theorem oneFormHeatRealDiagonal_columns (t : ℝ) (ht : 0 < t) (e : FrameBundle g) :
    oneFormHeatRealDiagonal hRic d (t + t) e.base =
      ∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2 := by
  have hhalf : (t + t).toNNReal / 2 = t.toNNReal := by
    rw [Real.toNNReal_add ht.le ht.le]
    exact add_self_div_two t.toNNReal
  simp only [oneFormHeatRealDiagonal, ite_eq_left (add_pos ht ht),
    oneFormHeatDiagonal_columns hRic d _ (Real.toNNReal_pos.mpr (add_pos ht ht)) e,
    hhalf, oneFormHeatRealColumn_pos hRic d t ht e]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The de Rham heat density has the Euler index as its integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_4
omit [PreconnectedSpace M] in
theorem scalarHeatDiagonal_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (scalarHeatDiagonal g o d t ht) (normalizedVolume g) := by
  have hc := (scalarHeatKernel_continuous g o d t ht).comp (continuous_id.prodMk continuous_id)
  change Continuous (fun x : M => scalarHeatKernel g o d t ht x x) at hc
  simp_rw [scalarHeatKernel_diagonal] at hc
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [PreconnectedSpace M] in
theorem twoFormHeatDiagonal_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (fun x => twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x))
      (normalizedVolume g) := by
  let F := fun (i : TwoFormEigenIndex (o := o) hRic) (x : M) =>
    ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ ^ 2
  have hi (i : TwoFormEigenIndex (o := o) hRic) : Integrable (F i) (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖F i x‖ ∂normalizedVolume g) := by
    apply (twoFormHeat_weight_square_summable (o := o) hRic (t / 2) (half_pos ht)).congr
    intro i
    simp only [F, Real.norm_eq_abs, abs_sq]
    exact (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).symm
  apply scalar_integrable_series hi hs
  intro x
  rw [twoFormHeatKernel_diagonal_trace]
  exact (twoFormHeatSection_pointwise_square_summable hRic (t / 2) (half_pos ht) x).hasSum

def hodgeHeatDensity (t : ℝ≥0) (ht : 0 < t) (x : M) : ℝ :=
  2 * scalarHeatDiagonal g o d t ht x - 2 * oneFormHeatDiagonal hRic d t x +
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x)

theorem hodgeHeatDensity_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (hodgeHeatDensity hRic d t ht) (normalizedVolume g) :=
  (((scalarHeatDiagonal_integrable d t ht).const_mul 2).sub
    ((oneFormHeatDiagonal_integrable hRic d t ht).const_mul 2)).add
      (twoFormHeatDiagonal_integrable hRic t ht)

theorem hodgeHeatDensity_integral (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, hodgeHeatDensity hRic d t ht x ∂normalizedVolume g) =
      (hodgeComplexEuler g o : ℝ) := by
  have h0 := (scalarHeatDiagonal_integrable d t ht).const_mul 2
  have h1 := (oneFormHeatDiagonal_integrable hRic d t ht).const_mul 2
  have h2 := twoFormHeatDiagonal_integrable (o := o) hRic t ht
  have he : (∫ x, hodgeHeatDensity hRic d t ht x ∂normalizedVolume g) =
      ((∫ x, 2 * scalarHeatDiagonal g o d t ht x ∂normalizedVolume g) -
        ∫ x, 2 * oneFormHeatDiagonal hRic d t x ∂normalizedVolume g) +
        ∫ x, twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x) ∂normalizedVolume g := by
    exact (integral_add (h0.sub h1) h2).trans
      (congrArg (· + ∫ x, twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x)
        ∂normalizedVolume g) (integral_sub h0 h1))
  rw [he, integral_const_mul, integral_const_mul, scalarHeatDiagonal_integral g o d t ht,
    oneFormHeatDiagonal_integral hRic d t ht, twoFormHeatKernel_trace_integral hRic t ht]
  exact hodgeHeat_supertrace hRic d t ht

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual compact scalar parametrix satisfies the forced heat ODE
in every eigenmode. Its forcing is its genuine time-minus-Laplacian residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [SecondCountableTopology M]
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarEvolution_probability
theorem HeatScalarChartData.eigen_evolution (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    HasDerivAt (fun s => inner ℝ (P.column s) (scalarBaseEigenvector g o d i))
      (inner ℝ (P.residual t) (scalarBaseEigenvector g o d i) -
        scalarBaseHeatRate g o d i * inner ℝ (P.column t) (scalarBaseEigenvector g o d i)) t := by
  let f : C(M, ℝ) := ⟨(scalarBaseEigenfunction g o d i).val,
    (scalarBaseEigenfunction g o d i).property.continuous⟩
  have hf : ContinuousMap.toLp 2 (normalizedVolume g) ℝ f = scalarBaseEigenvector g o d i :=
    (scalarBaseEigenfunction_L2 g o d i).symm
  have h := P.column_weak_deriv t ht f
  rw [hf] at h
  have hL := scalarFiniteLaplacian_eigen g o d (P.function t) (P.function_regular t) i
  change inner ℝ (P.laplacianColumn t) (scalarBaseEigenvector g o d i) =
    -scalarBaseHeatRate g o d i * inner ℝ (P.column t) (scalarBaseEigenvector g o d i) at hL
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change inner ℝ (P.timeColumn t - P.laplacianColumn t) (scalarBaseEigenvector g o d i) -
    scalarBaseHeatRate g o d i * inner ℝ (P.column t) (scalarBaseEigenvector g o d i) = _
  rw [inner_sub_left, hL]
  ring

theorem HeatScalarChartData.normalized_eigen_evolution (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    HasDerivAt (fun s => inner ℝ (P.normalizedColumn s) (scalarBaseEigenvector g o d i))
      (inner ℝ (P.normalizedResidual t) (scalarBaseEigenvector g o d i) -
        scalarBaseHeatRate g o d i *
          inner ℝ (P.normalizedColumn t) (scalarBaseEigenvector g o d i)) t := by
  have h := (P.eigen_evolution d t ht i).const_mul ((normalizedChartFactor g).toReal)⁻¹
  simpa only [HeatScalarChartData.normalizedColumn, HeatScalarChartData.normalizedResidual,
    real_inner_smul_left, mul_sub, mul_left_comm] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine scalar spectral heat column equals the constructed
normal parametrix minus its actual Bochner forcing convolution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem HeatScalarChartData.normalized_eigen_integral (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (i : ScalarBaseEigenIndex g o d) :
    inner ℝ (P.normalizedColumn t) (scalarBaseEigenvector g o d i) =
      Real.exp (-(i.1.val⁻¹ - 1) * t) * (scalarBaseEigenfunction g o d i).val e.base +
        ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
          inner ℝ (P.normalizedResidualZero s) (scalarBaseEigenvector g o d i) := by
  apply heat_forced_scalar_formula _ _ _ _ t ht.1
  · exact ((P.normalizedResidualZero_continuous ha hb hd B hB).mono
      (Icc_subset_Icc le_rfl ht.2)).inner continuousOn_const
  · exact P.normalized_initial_eigen d i
  · intro s hs
    rw [P.normalizedResidualZero_eq s hs]
    exact P.normalized_eigen_evolution d s hs i

theorem HeatScalarChartData.spectral_comparison (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    P.normalizedColumn t = scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base +
      scalarHeatConvolution g o d P.normalizedResidualZero t := by
  apply scalar_eq_of_eigen_pairing d
  intro i
  rw [inner_add_left, scalarHeatColumn_eigen,
    scalarHeatConvolution_eigen g o d _ t ht.1.le
      ((P.normalizedResidualZero_continuous ha hb hd B hB).mono
        (Icc_subset_Icc le_rfl ht.2))]
  unfold scalarBaseHeatWeight scalarBaseHeatRate
  rw [Real.coe_toNNReal t ht.1.le]
  rw [show -t * (i.1.val⁻¹ - 1) = -(i.1.val⁻¹ - 1) * t by ring]
  exact P.normalized_eigen_integral d ha hb hd B hB t ht i

theorem HeatScalarChartData.spectral_error_bound (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖P.normalizedColumn t -
      scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base‖ ≤
        (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t ^ 2 / 2 := by
  rw [P.spectral_comparison d ha hb hd B hB t ht, add_sub_cancel_left]
  exact scalarHeatConvolution_norm_le g o d _ t ht.1.le _ (fun s hs =>
    P.normalizedResidualZero_bound B hB s ⟨hs.1, hs.2.trans ht.2⟩)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact comparison with the genuine spectral heat column and the
quadratic L2 error bound, using only proved geometric residual estimates. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem oneForm_eq_of_eigen_pairing (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f h : OneFormL2 o)
    (hp : ∀ i, inner ℝ f (oneFormEigenvector hRic d i) = inner ℝ h (oneFormEigenvector hRic d i)) :
    f = h := by
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext i
  change (oneFormEigenbasis hRic d).repr f i = (oneFormEigenbasis hRic d).repr h i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  simpa only [real_inner_comm] using hp i

theorem HeatNormalParametrixData.one_spectral_comparison
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) :
    P.oneNormalizedColumn E t l =
      oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l +
        oneFormHeatConvolution hRic d (fun s => P.oneNormalizedResidualZero E s l) t := by
  apply oneForm_eq_of_eigen_pairing hRic d
  intro i
  rw [inner_add_left, oneFormHeatFrameColumn_eigen,
    oneFormHeatConvolution_eigen hRic d _ t ht.1.le
      ((P.oneNormalizedResidualZero_continuous E B hB l).mono (Icc_subset_Icc le_rfl ht.2))]
  unfold oneFormHeatWeight
  rw [Real.coe_toNNReal t ht.1.le]
  rw [show -t * oneFormHeatRate hRic d i = -oneFormHeatRate hRic d i * t by ring]
  exact P.one_normalized_eigen_integral E hpair hRic d he B hB t ht l i

theorem HeatNormalParametrixData.one_spectral_error_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) :
    ‖P.oneNormalizedColumn E t l -
      oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤
        (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t ^ 2 / 2 := by
  rw [P.one_spectral_comparison E hpair hRic d he B hB t ht l, add_sub_cancel_left]
  exact oneFormHeatConvolution_norm_le hRic d _ t ht.1.le _ (fun s hs =>
    P.oneNormalizedResidualZero_bound E B hB s ⟨hs.1, hs.2.trans ht.2⟩ l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact comparison of the actual local parametrix with the global spectral
heat column, followed by the quadratic L2 error bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.spectral_comparison
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6) :
    P.normalizedColumn E t l =
      twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l +
        twoFormHeatConvolution hRic (fun s => P.normalizedResidualZero E s l) t := by
  apply twoForm_eq_of_eigen_pairing hRic
  intro i
  rw [inner_add_left, twoFormHeatFrameColumn_eigen,
    twoFormHeatConvolution_eigen hRic _ t ht.1.le
      ((P.normalizedResidualZero_continuous E B hB l).mono (Icc_subset_Icc le_rfl ht.2))]
  unfold twoFormHeatFrameCoefficient twoFormHeatWeight twoFormHeatRate
  rw [Real.coe_toNNReal t ht.1.le]
  rw [show -t * (i.1.val⁻¹ - 1) = -(i.1.val⁻¹ - 1) * t by ring]
  exact P.normalized_eigen_integral E hRic he hgen B hB t ht l i

theorem HeatNormalParametrixData.spectral_error_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6) :
    ‖P.normalizedColumn E t l -
      twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤
        (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t ^ 2 / 2 := by
  rw [P.spectral_comparison E hRic he hgen B hB t ht l, add_sub_cancel_left]
  exact twoFormHeatConvolution_norm_le hRic _ t ht.1.le _ (fun s hs =>
    P.normalizedResidualZero_bound E B hB s ⟨hs.1, hs.2.trans ht.2⟩ l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar heat diagonal differs by a quantity tending to zero
from the explicit normal-coordinate squared-Gaussian integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem HeatScalarChartData.column_square_error_tendsto (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t) :
    Tendsto (fun t => ‖P.normalizedColumn t‖ ^ 2 -
      ‖scalarHeatRealColumn g o d t e.base‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hc⟩ := P.normalizedColumn_growth
  apply heat_norm_square_error_tendsto _ _ C (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2)
    1 zero_lt_one hc
  intro t ht
  rw [scalarHeatRealColumn_pos g o d t ht.1]
  exact (P.spectral_error_bound d ha hb hd B hB t ht).trans_eq (by ring)

theorem HeatScalarChartData.trace_gaussian_error_tendsto (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t) :
    Tendsto (fun t => scalarHeatRealDiagonal g o d (t + t) e.base -
      ((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, fourHeatGaussian t x ^ 2 *
          (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  have h := (P.column_square_error_tendsto d ha hb hd B hB).neg
  simp only [neg_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [scalarHeatRealDiagonal_columns g o d t ht e.base,
    P.normalizedColumn_gaussian_integral, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform norm growth and quadratic spectral error for the actual
common family of compact normal parametrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatActualUniformSpectral (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ e' ∈ U,
        ∃ N : HeatCommonNormalMember g o e.base E r e',
          frameCoordinateState g e.base e' ∈ closedBall (frameCoordinateState g e.base e) 1 ∧
          (∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
            ‖(N.parametrixData hr).normalizedColumn N.extension t l‖ ≤ C / t) ∧
          (e' ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6),
            ‖(N.parametrixData hr).normalizedColumn N.extension t l -
              twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e' l‖ ≤ D * t ^ 2) := by
  obtain ⟨E, r, hr, U₀, hU₀, he₀, B, hB, hN⟩ := exists_heatActualUniformParametrix g o hRic e
  let p := frameCoordinateState g e.base e
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p 1} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e (mem_chart_source FourSpace e.base)).preimage_mem_nhds
      (ball_mem_nhds _ zero_lt_one)
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hcoord)
  obtain ⟨C, hC, hc⟩ := heatUniformColumn_growth (g := g) (o := o) (c := e.base)
    E r hr (closedBall p 1) (isCompact_closedBall _ _)
  refine ⟨E, r, hr, U, hU, heU, C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2,
    by positivity, ?_⟩
  intro e' he'
  obtain ⟨hUe, hqe⟩ := hsub he'
  obtain ⟨N, hgen, hres⟩ := hN e' hUe
  refine ⟨N, ball_subset_closedBall hqe, hc e' N (ball_subset_closedBall hqe), ?_⟩
  intro hepos t ht l
  have hs : e'.base ∈ (chartAt FourSpace e.base).source := by
    simpa only [frameExponential_zero] using N.exponential_source 0 (mem_ball_self hr)
  exact ((N.parametrixData hr).spectral_error_bound N.extension hRic hs hgen B
    (hres hepos) t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual diagonal heat trace differs by a vanishing quantity from
the four squared L2 norms of the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneColumn_square_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (he : e.base ∈ (chartAt FourSpace c).source)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (l : Fin 4) :
    Tendsto (fun t => ‖P.oneNormalizedColumn E t l‖ ^ 2 -
      ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hc⟩ := P.oneNormalizedColumn_growth E l
  apply heat_norm_square_error_tendsto _ _ C (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2)
    1 zero_lt_one hc
  intro t ht
  rw [oneFormHeatRealColumn_pos hRic d t ht.1]
  exact (P.one_spectral_error_bound E hpair hRic d he B hB t ht l).trans_eq (by ring)

theorem HeatNormalParametrixData.oneTrace_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (he : e.base ∈ (chartAt FourSpace c).source)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t) :
    Tendsto (fun t => oneFormHeatRealDiagonal hRic d (t + t) e.base -
      ∑ l : Fin 4, ‖P.oneNormalizedColumn E t l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ l : Fin 4,
      (‖P.oneNormalizedColumn E t l‖ ^ 2 - ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun l _ => P.oneColumn_square_error_tendsto E hRic d he hpair B hB l)
  have hn : Tendsto (fun t => -(∑ l : Fin 4,
      (‖P.oneNormalizedColumn E t l‖ ^ 2 - ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [neg_zero] using hsum.neg
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [oneFormHeatRealDiagonal_columns hRic d t ht e, Finset.sum_sub_distrib, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual diagonal heat trace differs by a vanishing quantity from
the six squared L2 norms of the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_square_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (l : Fin 6) :
    Tendsto (fun t => ‖P.normalizedColumn E t l‖ ^ 2 -
      ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hc⟩ := P.normalizedColumn_growth E l
  apply heat_norm_square_error_tendsto _ _ C (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2)
    1 zero_lt_one hc
  intro t ht
  rw [twoFormHeatRealColumn_pos hRic t ht.1]
  exact (P.spectral_error_bound E hRic he hgen B hB t ht l).trans_eq (by ring)

theorem HeatNormalParametrixData.trace_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealTrace (o := o) hRic (t + t) e.base -
      ∑ l : Fin 6, ‖P.normalizedColumn E t l‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ l : Fin 6,
      (‖P.normalizedColumn E t l‖ ^ 2 - ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
      (fun l _ => P.column_square_error_tendsto E hRic he hgen B hB l)
  have hn : Tendsto (fun t => -(∑ l : Fin 6,
      (‖P.normalizedColumn E t l‖ ^ 2 - ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [neg_zero] using hsum.neg
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [twoFormHeatRealTrace_columns hRic t ht e, Finset.sum_sub_distrib, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common actual one-form columns have uniform quadratic spectral error. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformOneSpectral (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K →
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l‖ ≤ C / t) ∧
      (e ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4),
        ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l -
          oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤ D * t ^ 2) := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hχb (x : FourSpace) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
    exact (heatNormalChartBump r hr).le_one
  obtain ⟨B, hB, hb⟩ := heatUniformOneCutoffResidual F r K hK χ
    (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport
    hχs hχb (r / 4) (by positivity)
    (fun x hx => (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx)) hRic
  obtain ⟨C, hC, hc⟩ := heatUniformOneColumn_growth (g := g) (o := o) (c := c) F r hr K hK
  refine ⟨C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * (4 * B) / 2, by positivity, ?_⟩
  intro e N hq
  refine ⟨hc e N hq, ?_⟩
  intro he t ht l
  let P := N.normal.parametrixData hr
  have hres (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (k : Fin 4) :
      ‖P.oneResidual N.one s k‖ ≤ (4 * B) * s := by
    exact (P.oneResidual_norm_le N.one B hB s hs.1 (hb e N hq he s hs) k).trans_eq (by ring)
  have hec : e.base ∈ (chartAt FourSpace c).source := by
    simpa only [frameExponential_zero] using N.normal.exponential_source 0 (mem_ball_self hr)
  exact (P.one_spectral_error_bound N.one (N.parametrixData_one_pairing hr hRic)
    hRic d hec (4 * B) hres t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-two spectral error for the same common Euler family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformTwoSpectral (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K →
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖(N.normal.parametrixData hr).normalizedColumn N.normal.extension t l‖ ≤ C / t) ∧
      (e ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6),
        ‖(N.normal.parametrixData hr).normalizedColumn N.normal.extension t l -
          twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht.1) e l‖ ≤ D * t ^ 2) := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hχb (x : FourSpace) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
    exact (heatNormalChartBump r hr).le_one
  obtain ⟨B, hB, hb⟩ := heatUniformCutoffResidual F.base r K hK χ
    (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport
    hχs hχb (r / 4) (by positivity)
    (fun x hx => (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx)) hRic
  obtain ⟨C, hC, hc⟩ := heatUniformColumn_growth (g := g) (o := o) (c := c) F.base r hr K hK
  refine ⟨C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * (6 * B) / 2, by positivity, ?_⟩
  intro e N hq
  refine ⟨hc e N.normal hq, ?_⟩
  intro he t ht l
  let P := N.normal.parametrixData hr
  have hres (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (k : Fin 6) :
      ‖P.residual N.normal.extension s k‖ ≤ (6 * B) * s := by
    exact P.residual_norm_le N.normal.extension s hs.1 B hB (hb e N.normal hq he s hs) k
  have hec : e.base ∈ (chartAt FourSpace c).source := by
    simpa only [frameExponential_zero] using N.normal.exponential_source 0 (mem_ball_self hr)
  exact (P.spectral_error_bound N.normal.extension hRic hec
    (N.normal.parametrixData_generator hr hRic) (6 * B) hres t ht l).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral diagonal is approximated by an explicit normal
Gaussian integral with the correct probability-volume normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem HeatNormalParametrixData.oneTrace_gaussian_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (he : e.base ∈ (chartAt FourSpace c).source)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t) :
    Tendsto (fun t => oneFormHeatRealDiagonal hRic d (t + t) e.base -
      ((normalizedChartFactor g).toReal)⁻¹ * ∑ l : Fin 4,
        ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
          ‖heatNormalOnePolynomialColumn E P.cutoff t l x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have h := P.oneTrace_error_tendsto E hRic d he hpair B hB
  simpa only [P.oneNormalizedColumn_gaussian_integral E, Finset.mul_sum] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral diagonal is approximated by an explicit normal
Gaussian integral with the correct probability-volume normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.trace_gaussian_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealTrace (o := o) hRic (t + t) e.base -
      ((normalizedChartFactor g).toReal)⁻¹ * ∑ l : Fin 6,
        ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
          ‖heatNormalPolynomialColumn E P.cutoff t l x‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have h := P.trace_error_tendsto E hRic he hgen B hB
  simpa only [P.normalizedColumn_gaussian_integral E, Finset.mul_sum] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar members have uniform quadratic spectral error. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarUniform_probability
theorem heatUniformScalarSpectral (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ C ≥ (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K →
      (∀ t ∈ Ioc (0 : ℝ) 1, ‖(N.scalarData hr).normalizedColumn t‖ ≤ C / t) ∧
      (e ∈ o.positive → ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1),
        ‖(N.scalarData hr).normalizedColumn t -
          scalarHeatColumn g o d t.toNNReal (Real.toNNReal_pos.mpr ht.1) e.base‖ ≤ D * t ^ 2) := by
  obtain ⟨B, hB, hb⟩ := heatUniformScalarCutoffResidual F r hr K hK hRic
  obtain ⟨C, hC, hc⟩ := heatUniformScalarNormalizedColumn_growth (g := g) (o := o) (c := c) F r hr K hK
  let L := ‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖
  refine ⟨C, hC, ‖((normalizedChartFactor g).toReal)⁻¹‖ * (L * B) / 2, by dsimp [L]; positivity, ?_⟩
  intro e N hq
  refine ⟨hc e N hq, ?_⟩
  intro he t ht
  let P := N.scalarData hr
  obtain ⟨ha, hbb, hd⟩ := N.scalarData_actual hr
  have hres (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : ‖P.residual s‖ ≤ (L * B) * s := by
    exact (P.residual_norm_le ha hbb hd s (B * s) (mul_nonneg hB hs.1.le)
      (hb e N hq he s hs)).trans_eq (by dsimp [L]; ring)
  exact (P.spectral_error_bound d ha hbb hd (L * B) hres t ht).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed spectral diagonal inherits the actual local curvature limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatRealSignedTrace (hRic : RicciThree g) (t : ℝ) (x : M) : ℝ :=
  if ht : 0 < t then
    twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t.toNNReal (Real.toNNReal_pos.mpr ht) x x)
  else 0

theorem twoFormHeatRealSignedTrace_columns (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormHeatRealSignedTrace (o := o) hRic (t + t) e.base =
      ∑ l, ∑ m, twoFormHodgeMatrix l m * inner ℝ
        (twoFormHeatRealColumn (o := o) hRic t e l) (twoFormHeatRealColumn (o := o) hRic t e m) := by
  simpa only [twoFormHeatRealSignedTrace, dite_eq_left (add_pos ht ht),
    twoFormHeatRealColumn, dite_eq_left ht, Real.toNNReal_add ht.le ht.le] using
    twoFormHeatKernel_signed_columns hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e he

variable {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_inner_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (l m : Fin 6) :
    Tendsto (fun t => inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) -
      inner ℝ (twoFormHeatRealColumn (o := o) hRic t e l)
        (twoFormHeatRealColumn (o := o) hRic t e m)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C₁, _, hc₁⟩ := P.normalizedColumn_growth E l
  obtain ⟨C₂, _, hc₂⟩ := P.normalizedColumn_growth E m
  apply heat_inner_error_tendsto _ _ _ _ C₁ C₂
    (‖((normalizedChartFactor g).toReal)⁻¹‖ * B / 2) 1 zero_lt_one hc₁ hc₂
  · intro t ht
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact (P.spectral_error_bound E hRic he hgen B hB t ht l).trans_eq (by ring)
  · intro t ht
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact (P.spectral_error_bound E hRic he hgen B hB t ht m).trans_eq (by ring)

theorem HeatNormalParametrixData.signed_trace_error_tendsto
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source) (hepos : e ∈ o.positive)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic (t + t) e.base -
      ∑ l, ∑ m, twoFormHodgeMatrix l m *
        inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m)) (𝓝[>] 0) (𝓝 0) := by
  have hs := tendsto_finsetSum Finset.univ (fun l _ =>
    tendsto_finsetSum Finset.univ (fun m _ =>
      (P.column_inner_error_tendsto E hRic he hgen B hB l m).const_mul (twoFormHodgeMatrix l m)))
  simp only [mul_zero, Finset.sum_const_zero] at hs
  have hn := hs.neg
  simp only [neg_zero] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [twoFormHeatRealSignedTrace_columns hRic t ht e hepos]
  simp only [mul_sub, Finset.sum_sub_distrib, neg_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral Hodge-signed diagonal has the local signature
curvature density as its small-time limit, with normalized-volume factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
  {c : M} {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}

theorem HeatNormalParametrixData.signed_trace_limit
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (hepos : (⟨c, f⟩ : FrameBundle g) ∈ o.positive)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic (t + t) c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  have hnorm := (E.signed_gaussian_limit P.cutoff P.cutoff_regular P.cutoff_compact
    P.cutoff_zero hRic).const_mul ((normalizedChartFactor g).toReal)⁻¹
  have hn : Tendsto (fun t => ∑ l, ∑ m, twoFormHodgeMatrix l m *
      inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m)) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
    simpa only [P.signedColumn_integral E] using hnorm
  have h := (P.signed_trace_error_tendsto E hRic (mem_chart_source FourSpace c) hepos hgen B hB).add hn
  simpa only [sub_add_cancel, zero_add] using h

theorem HeatNormalParametrixData.signed_trace_limit_unscaled
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (hepos : (⟨c, f⟩ : FrameBundle g) ∈ o.positive)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic t c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  have h := (P.signed_trace_limit E hRic hepos hgen B hB).comp fourHeatGaussian_half_tendsto
  have ht (t : ℝ) : t / 2 + t / 2 = t := by ring
  simpa only [Function.comp_def, ht] using h

theorem twoFormHeat_signature_pointwise_limit (hRic : RicciThree g) (c : M) :
    Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic t c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, o.frame c⟩))) := by
  obtain ⟨D⟩ := exists_heatNormalFrameData g o c ⟨c, o.frame c⟩ (mem_chart_source FourSpace c)
  obtain ⟨E⟩ := exists_heatNormalBundleExtension D
  obtain ⟨P, hgen, B, _, hB⟩ := exists_heatNormalGlobalResidual E
    (mem_chart_source FourSpace c) hRic (o.frame_positive c)
  exact P.signed_trace_limit_unscaled E hRic (o.frame_positive c) hgen B hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform bound for the genuine signed heat diagonal near each frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatSignedUniformLocal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ B ≥ (0 : ℝ),
      ∀ e' ∈ U, e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) e'.base‖ ≤ B := by
  obtain ⟨E, r, hr, U, hU, heU, C, hC, D, hD, hN⟩ :=
    exists_heatActualUniformSpectral g o hRic e
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball 0 r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformSignedIntegral_bound (g := g) (o := o) (c := e.base)
    E r hr χ (heatNormalChartBump r hr).contDiff
      (heatNormalChartBump r hr).hasCompactSupport hχs
      (closedBall (frameCoordinateState g e.base e) 1) (isCompact_closedBall _ _)
  let S : ℝ := ∑ l : Fin 6, ∑ m : Fin 6, ‖twoFormHodgeMatrix l m‖
  let A : ℝ := S * (2 * C * D + D ^ 2)
  let V : ℝ := ‖((normalizedChartFactor g).toReal)⁻¹‖ * B
  refine ⟨U, hU, heU, A + V, by dsimp [A, S, V]; positivity, ?_⟩
  intro e' he' hepos t ht
  obtain ⟨N, hq, hnorm, herr⟩ := hN e' he'
  let P := N.parametrixData hr
  let X : ℝ := ∑ l, ∑ m, twoFormHodgeMatrix l m *
    inner ℝ (P.normalizedColumn N.extension t l) (P.normalizedColumn N.extension t m)
  have hX : ‖X‖ ≤ V := by
    dsimp only [X]
    rw [P.signedColumn_integral, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [P, N.parametrixData_cutoff] using hb e' N hq t ht
  have herror : ‖X - twoFormHeatRealSignedTrace (o := o) hRic (t + t) e'.base‖ ≤ A := by
    rw [twoFormHeatRealSignedTrace_columns hRic t ht.1 e' hepos]
    apply heat_signed_gram_error_uniform _ _ _ C D t hC hD ht (hnorm t ht)
    intro l
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact herr hepos t ht l
  calc
    _ ≤ ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) e'.base - X‖ + ‖X‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ A + V := by rw [norm_sub_rev]; exact add_le_add herror hX

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual de Rham spectral heat density has the local Euler curvature limit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def hodgeHeatRealDensity (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ) (x : M) : ℝ :=
  2 * scalarHeatRealDiagonal g o d t x - 2 * oneFormHeatRealDiagonal hRic d t x +
    twoFormHeatRealTrace (o := o) hRic t x

omit [PreconnectedSpace M] in
theorem hodgeHeatRealDensity_pos (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ) (ht : 0 < t) (x : M) :
    hodgeHeatRealDensity hRic d t x =
      hodgeHeatDensity hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) x := by
  simp only [hodgeHeatRealDensity, scalarHeatRealDiagonal, oneFormHeatRealDiagonal,
    twoFormHeatRealTrace, dite_eq_left ht, ite_eq_left ht, hodgeHeatDensity]

variable {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

theorem HeatEulerChartData.euler_trace_limit (P : HeatEulerChartData D)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (ha : ∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.scalar.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B₀ : ℝ) (hB₀ : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.scalar.residual t‖ ≤ B₀ * t)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.normal.oneColumn P.bundle.oneCompanion t l)
        (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
      inner ℝ (P.normal.oneOperatorColumn P.bundle.oneCompanion t l) (smoothOneFormL2Linear v))
    (B₁ : ℝ) (hB₁ : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖P.normal.oneResidual P.bundle.oneCompanion t l‖ ≤ B₁ * t)
    (hgen : ∀ t l, ∃ hf : P.normal.column P.bundle t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.normal.column P.bundle t l, hf⟩ =
        P.normal.operatorColumn P.bundle t l)
    (B₂ : ℝ) (hB₂ : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖P.normal.residual P.bundle t l‖ ≤ B₂ * t) :
    Tendsto (fun t => hodgeHeatRealDensity hRic d (t + t) e.base) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureEulerDensity (twoFormMetricCurvatureTensor g e))) := by
  have h₀ := P.scalar.trace_gaussian_error_tendsto d ha hb hd B₀ hB₀
  have h₁ := P.normal.oneTrace_gaussian_error_tendsto P.bundle.oneCompanion hRic d he hpair B₁ hB₁
  have h₂ := P.normal.trace_gaussian_error_tendsto P.bundle hRic he hgen B₂ hB₂
  have herr := ((h₀.const_mul 2).sub (h₁.const_mul 2)).add h₂
  have hgauss := (P.bundle.euler_gaussian_limit P.normal.cutoff
    P.normal.cutoff_regular.continuous P.normal.cutoff_compact P.normal.cutoff_zero hRic he).const_mul
      ((normalizedChartFactor g).toReal)⁻¹
  convert herr.add hgauss using 1
  · funext t
    rw [← P.euler_integral t]
    unfold hodgeHeatRealDensity
    ring
  · simp only [mul_zero, sub_self, zero_add]

theorem hodgeHeat_euler_pointwise_limit (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M) :
    Tendsto (fun t => hodgeHeatRealDensity hRic d t c) (𝓝[>] 0)
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        curvatureEulerDensity (twoFormMetricCurvatureTensor g ⟨c, o.frame c⟩))) := by
  obtain ⟨D⟩ := exists_heatNormalFrameData g o c ⟨c, o.frame c⟩ (mem_chart_source FourSpace c)
  obtain ⟨P, ha, hb, hd, ⟨B₀, _, hB₀⟩, hp, ⟨B₁, _, hB₁⟩, hg, ⟨B₂, _, hB₂⟩⟩ :=
    exists_heatEulerCommonChart D (mem_chart_source FourSpace c) hRic (o.frame_positive c)
  have h := (P.euler_trace_limit hRic d (mem_chart_source FourSpace c)
    ha hb hd B₀ hB₀ hp B₁ hB₁ hg B₂ hB₂).comp fourHeatGaussian_half_tendsto
  have ht (t : ℝ) : t / 2 + t / 2 = t := by ring
  simpa only [Function.comp_def, ht] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness turns the actual local signed heat estimates into a
single bound on the closed manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatSignedUniformBase (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (c : M) :
    ∃ V : Set M, IsOpen V ∧ c ∈ V ∧ ∃ B ≥ (0 : ℝ),
      ∀ x ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) x‖ ≤ B := by
  obtain ⟨S, hS, hpos⟩ := exists_positive_localGramSection g o c
  let σ := localGramSection g c S hS
  obtain ⟨U, hU, hcU, B, hB, hb⟩ := exists_heatSignedUniformLocal g o hRic (σ c)
  have hpre : ∀ᶠ x in 𝓝 c, σ x ∈ U :=
    (continuousAt_localGramSection g c S hS).preimage_mem_nhds (hU.mem_nhds hcU)
  obtain ⟨V, hVsub, hV, hcV⟩ := mem_nhds_iff.mp (Filter.inter_mem hpre hpos)
  refine ⟨V, hV, hcV, B, hB, ?_⟩
  intro x hx t ht
  have h := hb (σ x) (hVsub hx).1 (hVsub hx).2 t ht
  simpa only [σ, localGramSection_base] using h

theorem exists_heatSignedUniformGlobal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ x : M, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖twoFormHeatRealSignedTrace (o := o) hRic (t + t) x‖ ≤ B := by
  classical
  choose U hU hmem B hB hb using exists_heatSignedUniformBase g o hRic
  have hcover : (univ : Set M) ⊆ ⋃ i, U i := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨∑ i ∈ s, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro x t ht
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact (hb i x hxi t ht).trans
    (Finset.single_le_sum (fun j _ => hB j) hi)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence identifies the actual harmonic signature with
its curvature integral, keeping the chart-volume normalization explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatRealSignedTrace_pos (hRic : RicciThree g) (t : ℝ) (ht : 0 < t) (x : M) :
    twoFormHeatRealSignedTrace (o := o) hRic t x =
      twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t.toNNReal
        (Real.toNNReal_pos.mpr ht) x x) := by
  unfold twoFormHeatRealSignedTrace
  exact dite_eq_left ht

theorem twoFormHeatRealSignedTrace_nonpos (hRic : RicciThree g) (t : ℝ) (ht : ¬ 0 < t) (x : M) :
    twoFormHeatRealSignedTrace (o := o) hRic t x = 0 := by
  unfold twoFormHeatRealSignedTrace
  exact dite_eq_right ht

theorem twoFormHeatRealSignedTrace_measurable (hRic : RicciThree g) (t : ℝ) :
    Measurable (twoFormHeatRealSignedTrace (o := o) hRic t) := by
  change Measurable (fun x => twoFormHeatRealSignedTrace (o := o) hRic t x)
  by_cases ht : 0 < t
  · simp_rw [twoFormHeatRealSignedTrace_pos hRic t ht]
    simp_rw [twoFormHeatKernel_signed_diagonal]
    apply Measurable.tsum
    intro i
    exact (smoothTwoForm_pairing_continuous _
      (smoothTwoFormHodge o (twoFormHeatSection hRic (t.toNNReal / 2)
        (half_pos (Real.toNNReal_pos.mpr ht)) (twoFormEigenvector hRic i)))).measurable
  · simpa only [twoFormHeatRealSignedTrace_nonpos hRic t ht] using
      (measurable_const : Measurable (fun _ : M => (0 : ℝ)))

theorem twoFormHeat_signature_integral_limit (hRic : RicciThree g) :
    Tendsto (fun t => ∫ x, twoFormHeatRealSignedTrace (o := o) hRic t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, orientedSignatureDensity g o x ∂normalizedVolume g)) := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨B, _hB, hb⟩ := exists_heatSignedUniformGlobal g o hRic
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht, ht1.le⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂normalizedVolume g,
      ‖twoFormHeatRealSignedTrace (o := o) hRic t x‖ ≤ B := by
    filter_upwards [hsmall] with t ht
    refine Eventually.of_forall fun x => ?_
    have h := hb x (t / 2) ⟨half_pos ht.1, by linarith [ht.2]⟩
    simpa only [show t / 2 + t / 2 = t by ring] using h
  have hp : ∀ x : M, Tendsto (fun t => twoFormHeatRealSignedTrace (o := o) hRic t x)
      (𝓝[>] 0) (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * orientedSignatureDensity g o x)) :=
    fun x => twoFormHeat_signature_pointwise_limit hRic x
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := normalizedVolume g) (l := 𝓝[>] (0 : ℝ))
    (F := fun t x => twoFormHeatRealSignedTrace (o := o) hRic t x)
    (f := fun x => ((normalizedChartFactor g).toReal)⁻¹ * orientedSignatureDensity g o x)
    (fun _ : M => B)
    (Eventually.of_forall fun t => (twoFormHeatRealSignedTrace_measurable hRic t).aestronglyMeasurable)
    hbound (integrable_const B) (Eventually.of_forall hp)
  simpa only [integral_const_mul] using hlim

theorem harmonicSignature_eq_normalized_curvature_integral (hRic : RicciThree g) :
    (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) =
      ((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, orientedSignatureDensity g o x ∂normalizedVolume g := by
  have hconst : Tendsto
      (fun t => ∫ x, twoFormHeatRealSignedTrace (o := o) hRic t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp_rw [twoFormHeatRealSignedTrace_pos hRic t ht]
    exact (twoFormHeatKernel_signature_trace hRic t.toNNReal (Real.toNNReal_pos.mpr ht)).symm
  exact tendsto_nhds_unique hconst (twoFormHeat_signature_integral_limit hRic)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The proved signature integral in the original metric-volume convention.
The numerical Hausdorff normalization is displayed, not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem deRhamSignature_eq_curvature_integral (hRic : RicciThree g) :
    (deRhamSignature (o := o) hRic : ℝ) = riemannianChartFactor.toReal⁻¹ *
      ∫ x, orientedSignatureDensity g o x ∂volumeMeasure g := by
  rw [deRhamSignature_hodge]
  push_cast
  rw [harmonicSignature_eq_normalized_curvature_integral hRic,
    volumeMeasure_integral_eq_total_mul (actual_finitePositiveVolume g),
    normalizedChartFactor_inv_toReal]
  ring

theorem deRhamSignature_curvature_counts (hRic : RicciThree g) :
    riemannianChartFactor.toReal * (deRhamSignature (o := o) hRic : ℝ) =
      (4 / 3 : ℝ) * volumeRatio g *
        ((∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) -
          ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g) := by
  rw [deRhamSignature_eq_curvature_integral hRic, ← mul_assoc,
    mul_inv_cancel₀ riemannianChartFactor_toReal_pos.ne', one_mul]
  exact integral_orientedSignatureDensity o hRic (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common bound for the actual Euler heat density on a compact frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformEulerDensity_bound (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (_N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖hodgeHeatRealDensity hRic d (t + t) e.base‖ ≤ B := by
  obtain ⟨C₀, hC₀, D₀, hD₀, h₀⟩ := heatUniformScalarSpectral F r hr K hK hRic d
  obtain ⟨C₁, hC₁, D₁, hD₁, h₁⟩ := heatUniformOneSpectral F r hr K hK hRic d
  obtain ⟨C₂, hC₂, D₂, hD₂, h₂⟩ := heatUniformTwoSpectral F r hr K hK hRic
  obtain ⟨B, hB, hb⟩ := heatUniformEulerColumnTrace_bound (g := g) (o := o) (c := c) F r hr K hK hRic
  let A₀ := 2 * C₀ * D₀ + D₀ ^ 2
  let A₁ := 2 * C₁ * D₁ + D₁ ^ 2
  let A₂ := 2 * C₂ * D₂ + D₂ ^ 2
  refine ⟨2 * A₀ + 8 * A₁ + 6 * A₂ + B, by dsimp [A₀, A₁, A₂]; positivity, ?_⟩
  intro e N hq he t ht
  let P := N.normal.parametrixData hr
  let P₀ := N.scalarData hr
  have hs₀ := h₀ e N hq
  have hs₁ := h₁ e N hq
  have hs₂ := h₂ e N hq
  have he₀ : ‖‖P₀.normalizedColumn t‖ ^ 2 - ‖scalarHeatRealColumn g o d t e.base‖ ^ 2‖ ≤ A₀ := by
    apply heat_norm_square_error_uniform _ _ C₀ D₀ t hC₀ hD₀ ht (hs₀.1 t ht)
    rw [scalarHeatRealColumn_pos g o d t ht.1]
    exact hs₀.2 he t ht
  have he₁ : ‖(∑ l : Fin 4, ‖P.oneNormalizedColumn N.one t l‖ ^ 2) -
      (∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2)‖ ≤ 4 * A₁ := by
    apply (heat_sum_norm_square_error_uniform _ _ C₁ D₁ t hC₁ hD₁ ht (hs₁.1 t ht) ?_).trans_eq
      (by simp only [Fintype.card_fin]; rfl)
    intro l
    rw [oneFormHeatRealColumn_pos hRic d t ht.1]
    exact hs₁.2 he t ht l
  have he₂ : ‖(∑ l : Fin 6, ‖P.normalizedColumn N.normal.extension t l‖ ^ 2) -
      (∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)‖ ≤ 6 * A₂ := by
    apply (heat_sum_norm_square_error_uniform _ _ C₂ D₂ t hC₂ hD₂ ht (hs₂.1 t ht) ?_).trans_eq
      (by simp only [Fintype.card_fin]; rfl)
    intro l
    rw [twoFormHeatRealColumn_pos hRic t ht.1]
    exact hs₂.2 he t ht l
  have herr : ‖N.eulerColumnTrace hr t - hodgeHeatRealDensity hRic d (t + t) e.base‖ ≤
      2 * A₀ + 8 * A₁ + 6 * A₂ := by
    have hid : N.eulerColumnTrace hr t - hodgeHeatRealDensity hRic d (t + t) e.base =
        2 * (‖P₀.normalizedColumn t‖ ^ 2 - ‖scalarHeatRealColumn g o d t e.base‖ ^ 2) -
        2 * ((∑ l : Fin 4, ‖P.oneNormalizedColumn N.one t l‖ ^ 2) -
          (∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2)) +
        ((∑ l : Fin 6, ‖P.normalizedColumn N.normal.extension t l‖ ^ 2) -
          (∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)) := by
      unfold HeatCommonEulerMember.eulerColumnTrace hodgeHeatRealDensity
      rw [scalarHeatRealDiagonal_columns g o d t ht.1,
        oneFormHeatRealDiagonal_columns hRic d t ht.1 e, twoFormHeatRealTrace_columns hRic t ht.1 e]
      ring
    rw [hid]
    calc
      _ ≤ ‖2 * (‖P₀.normalizedColumn t‖ ^ 2 - ‖scalarHeatRealColumn g o d t e.base‖ ^ 2)‖ +
          ‖2 * ((∑ l : Fin 4, ‖P.oneNormalizedColumn N.one t l‖ ^ 2) -
            (∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2))‖ +
          ‖(∑ l : Fin 6, ‖P.normalizedColumn N.normal.extension t l‖ ^ 2) -
            (∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ 2 * A₀ + 2 * (4 * A₁) + 6 * A₂ := by
        simp only [norm_mul, Real.norm_ofNat]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left he₀ (by norm_num))
          (mul_le_mul_of_nonneg_left he₁ (by norm_num))) he₂
      _ = _ := by ring
  calc
    _ ≤ ‖hodgeHeatRealDensity hRic d (t + t) e.base - N.eulerColumnTrace hr t‖ +
        ‖N.eulerColumnTrace hr t‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by rw [norm_sub_rev]; exact add_le_add herr (hb e N hq t ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness supplies a single bound for the actual Euler heat density. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]

theorem exists_heatEulerUniformLocal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (e : FrameBundle g) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ B ≥ (0 : ℝ),
      ∀ e' ∈ U, e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖hodgeHeatRealDensity hRic d (t + t) e'.base‖ ≤ B := by
  obtain ⟨F, r, hr, U, hU, heU, hN⟩ := exists_heatUniformEulerFamily g o e
  obtain ⟨B, hB, hb⟩ := heatUniformEulerDensity_bound (g := g) (o := o) (c := e.base)
    F r hr (closedBall (frameCoordinateState g e.base e) (r / 2))
      (isCompact_closedBall _ _) hRic d
  refine ⟨U, hU, heU, B, hB, ?_⟩
  intro e' he' hepos t ht
  obtain ⟨hq, ⟨N⟩⟩ := hN e' he'
  exact hb e' N (ball_subset_closedBall hq) hepos t ht

theorem exists_heatEulerUniformBase (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M) :
    ∃ V : Set M, IsOpen V ∧ c ∈ V ∧ ∃ B ≥ (0 : ℝ),
      ∀ x ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1, ‖hodgeHeatRealDensity hRic d (t + t) x‖ ≤ B := by
  obtain ⟨S, hS, hpos⟩ := exists_positive_localGramSection g o c
  let σ := localGramSection g c S hS
  obtain ⟨U, hU, hcU, B, hB, hb⟩ := exists_heatEulerUniformLocal g o hRic d (σ c)
  have hpre : ∀ᶠ x in 𝓝 c, σ x ∈ U :=
    (continuousAt_localGramSection g c S hS).preimage_mem_nhds (hU.mem_nhds hcU)
  obtain ⟨V, hVsub, hV, hcV⟩ := mem_nhds_iff.mp (Filter.inter_mem hpre hpos)
  refine ⟨V, hV, hcV, B, hB, ?_⟩
  intro x hx t ht
  have h := hb (σ x) (hVsub hx).1 (hVsub hx).2 t ht
  simpa only [σ, localGramSection_base] using h

theorem exists_heatEulerUniformGlobal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ B ≥ (0 : ℝ), ∀ x : M, ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖hodgeHeatRealDensity hRic d (t + t) x‖ ≤ B := by
  classical
  choose U hU hmem B hB hb using exists_heatEulerUniformBase g o hRic d
  have hcover : (univ : Set M) ⊆ ⋃ i, U i := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨∑ i ∈ s, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro x t ht
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact (hb i x hxi t ht).trans (Finset.single_le_sum (fun j _ => hB j) hi)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Euler heat supertrace converges to its curvature integral.
The numerical chart-volume normalization remains explicit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem hodgeHeat_euler_integral_limit (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Tendsto (fun t => ∫ x, hodgeHeatRealDensity hRic d t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((normalizedChartFactor g).toReal)⁻¹ *
        ∫ x, orientedEulerDensity g o x ∂normalizedVolume g)) := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨B, _hB, hb⟩ := exists_heatEulerUniformGlobal g o hRic d
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht, ht1.le⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ x ∂normalizedVolume g,
      ‖hodgeHeatRealDensity hRic d t x‖ ≤ B := by
    filter_upwards [hsmall] with t ht
    refine Eventually.of_forall fun x => ?_
    have h := hb x (t / 2) ⟨half_pos ht.1, by linarith [ht.2]⟩
    simpa only [show t / 2 + t / 2 = t by ring] using h
  have hp : ∀ x : M, Tendsto (fun t => hodgeHeatRealDensity hRic d t x)
      (𝓝[>] 0) (𝓝 (((normalizedChartFactor g).toReal)⁻¹ * orientedEulerDensity g o x)) :=
    fun x => hodgeHeat_euler_pointwise_limit hRic d x
  have hmeas : ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (hodgeHeatRealDensity hRic d t) (normalizedVolume g) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have heq : hodgeHeatRealDensity hRic d t =
        hodgeHeatDensity hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) := by
      funext x
      exact hodgeHeatRealDensity_pos hRic d t ht x
    rw [heq]
    exact (hodgeHeatDensity_integrable hRic d t.toNNReal (Real.toNNReal_pos.mpr ht)).aestronglyMeasurable
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := normalizedVolume g) (l := 𝓝[>] (0 : ℝ))
    (F := fun t x => hodgeHeatRealDensity hRic d t x)
    (f := fun x => ((normalizedChartFactor g).toReal)⁻¹ * orientedEulerDensity g o x)
    (fun _ : M => B) hmeas hbound (integrable_const B) (Eventually.of_forall hp)
  simpa only [integral_const_mul] using hlim

theorem hodgeComplexEuler_eq_normalized_curvature_integral (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    (hodgeComplexEuler g o : ℝ) = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, orientedEulerDensity g o x ∂normalizedVolume g := by
  have hconst : Tendsto
      (fun t => ∫ x, hodgeHeatRealDensity hRic d t x ∂normalizedVolume g)
      (𝓝[>] (0 : ℝ)) (𝓝 (hodgeComplexEuler g o : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp_rw [hodgeHeatRealDensity_pos hRic d t ht]
    exact (hodgeHeatDensity_integral hRic d t.toNNReal (Real.toNNReal_pos.mpr ht)).symm
  exact tendsto_nhds_unique hconst (hodgeHeat_euler_integral_limit hRic d)

theorem hodgeComplexEuler_eq_curvature_integral (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    (hodgeComplexEuler g o : ℝ) = riemannianChartFactor.toReal⁻¹ *
      ∫ x, orientedEulerDensity g o x ∂volumeMeasure g := by
  rw [hodgeComplexEuler_eq_normalized_curvature_integral hRic d,
    volumeMeasure_integral_eq_total_mul (actual_finitePositiveVolume g),
    normalizedChartFactor_inv_toReal]
  ring

theorem hodgeComplexEuler_curvature_counts (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    riemannianChartFactor.toReal * (hodgeComplexEuler g o : ℝ) =
      2 * volumeRatio g * (1 + (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) +
        ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g) := by
  rw [hodgeComplexEuler_eq_curvature_integral hRic d, ← mul_assoc,
    mul_inv_cancel₀ riemannianChartFactor_toReal_pos.ne', one_mul]
  exact integral_orientedEulerDensity o hRic (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual harmonic dimension determines the volume and Weyl energy
in the nonzero half-flat branch. Sectional pinching bounds that dimension. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_volume_energy_counts (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    volumeRatio g / riemannianChartFactor.toReal =
        1 - (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) / 4 ∧
      (volumeRatio g / riemannianChartFactor.toReal) *
        (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) =
        3 * (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) / 4 := by
  have he := hodgeComplexEuler_curvature_counts hRic (canonicalParallelMetricData g o hRic)
  have hs := deRhamSignature_curvature_counts (o := o) hRic
  rw [hodgeComplexEuler_hodge hRic, halfFlat_negative_harmonic_dimension_zero hRic hminus] at he
  rw [deRhamSignature_hodge hRic, halfFlat_negative_harmonic_dimension_zero hRic hminus] at hs
  have hm : ∀ x, minusNorm o x = 0 := fun x => (minusNorm_eq_zero_iff o x).mpr (hminus x)
  simp only [hm, zero_pow (by decide : 2 ≠ 0), integral_zero] at he hs
  push_cast at he hs
  constructor
  · apply (div_eq_iff riemannianChartFactor_toReal_pos.ne').mpr
    nlinarith only [he, hs]
  · field_simp [riemannianChartFactor_toReal_pos.ne']
    nlinarith only [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one half-flat branch attains equality in the Weyl gap;
the actual Weyl norm is consequently identically one. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_plusNorm_eq_one_of_energy_one (hRic : RicciThree g)
    (henergy : (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) = 1) :
    ∀ x, plusNorm o x = 1 := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let : Measure.IsOpenPosMeasure (normalizedVolume g) := normalizedVolume_isOpenPosMeasure g
  exact weyl_gap_equality_constant (normalizedVolume g)
    ⟨plusNorm o, continuous_plusNorm g o⟩ (plusNorm_nonneg o) henergy
    (actual_weyl_gap_limiting_inequality hRic)

variable [SecondCountableTopology M]

theorem halfFlat_dimension_one_energy (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    (∫ x, plusNorm o x ^ 2 ∂normalizedVolume g) = 1 := by
  obtain ⟨hv,he⟩ := halfFlat_volume_energy_counts hRic hminus
  rw [hdim] at hv he
  norm_num at hv he
  rw [hv] at he
  linarith

theorem halfFlat_dimension_one_norm (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ∀ x, plusNorm o x = 1 :=
  actual_plusNorm_eq_one_of_energy_one hRic (halfFlat_dimension_one_energy hRic hminus hdim)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A parallel two-form has constant norm on the actual compact connected
manifold. This uses the existing global geodesics, not a holonomy premise. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable [PreconnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem parallel_twoForm_norm_constant (hRic : RicciThree g) (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, ‖u.val x‖ = c := by
  let x : M := Classical.arbitrary M
  let e : FrameBundle g := ⟨x,o.frame x⟩
  refine ⟨‖u.val x‖, norm_nonneg _, fun y => ?_⟩
  obtain ⟨v,hv⟩ := frameExponential_surjective g o hRic e (o.frame_positive x) y
  rw [← hv]
  exact parallel_twoForm_norm_on_exponential u hz e (o.frame_positive x) v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one half-flat branch has an actual global parallel
self-dual two-form of norm sqrt(2), constructed from its harmonic space. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.unitFormHarmonicAddGroup
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.unitFormPositiveAddGroup
theorem halfFlat_dimension_one_parallel_unit_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ∃ w : smoothTwoForms o,
      (∀ x, twoFormHodge (w.val x) = w.val x) ∧
      (∀ x, ‖w.val x‖ ^ 2 = 2) ∧
      ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0 := by
  obtain ⟨u,hu⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)
    (M := smoothHarmonicPositive (o := o) hRic)).mp (by rw [hdim]; norm_num)
  have hn := halfFlat_dimension_one_norm hRic hminus hdim
  have he := halfFlat_positive_harmonic_covariantEnergy_zero hRic hminus hn u
  have hz := smoothTwoForm_allFrames_covariant_zero u.val.val he
  obtain ⟨c,hc,hconst⟩ := parallel_twoForm_norm_constant hRic u.val.val hz
  have hcpos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := le_antisymm (le_of_not_gt h) hc
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact norm_eq_zero.mp (hc0 ▸ hconst x)
  let r := Real.sqrt 2 / c
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr (by norm_num)) hcpos
  refine ⟨r • u.val.val, ?_, ?_, ?_⟩
  · intro x
    change twoFormHodge (r • u.val.val.val x) = r • u.val.val.val x
    rw [map_smul]
    congr 1
    exact congrArg (fun v : smoothHarmonicTwoForms (o := o) => v.val.val x)
      (smoothHarmonicPositive_star hRic u)
  · intro x
    change ‖r • u.val.val.val x‖ ^ 2 = 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hconst]
    dsimp only [r]
    rw [div_mul_cancel₀ _ hcpos.ne', Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · intro e
    change twoFormFramedCovariantDerivative o (r • u.val.val.val) e = 0
    rw [twoFormFramedCovariantDerivative_smul, hz, smul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact minimizing-domain radial mass in the complex-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}
variable (hRic : RicciThree g) (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
  (hnorm : ∀ x, plusNorm o x = 1)
  (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
  (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
  (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)

include hRic hminus hnorm w hstar hw hz

variable [SecondCountableTopology M]

theorem complex_volume_le_cut_mass (e : FrameBundle g) (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q : Directions,
        complexRadialMass (actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))) ∂sphereMeasure) := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he, polarAngularMass_eq] at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply lintegral_congr
  intro q
  exact (complex_actual_cut_mass hRic hminus hnorm w hstar hw hz _
    (frameRotate_oriented_positive o e he (directionOrientedMatrix q))).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual index formula fixes the volume in the dimension-one case. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem complex_normalized_totalVolume (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    totalVolume g / riemannianChartFactor.toReal = 2 * Real.pi ^ 2 := by
  have h := (halfFlat_volume_energy_counts hRic hminus).1
  rw [hdim] at h
  norm_num at h
  unfold volumeRatio at h
  rw [div_right_comm] at h
  have he := (div_eq_iff (by positivity : (8 * Real.pi ^ 2 / 3 : ℝ) ≠ 0)).mp h
  calc
    _ = (3 / 4 : ℝ) * (8 * Real.pi ^ 2 / 3) := he
    _ = _ := by ring

theorem complex_volumeMeasure (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    volumeMeasure g Set.univ = riemannianChartFactor * ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have h := (div_eq_iff riemannianChartFactor_toReal_pos.ne').mp
    (complex_normalized_totalVolume hRic hminus hdim)
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  calc
    volumeMeasure g Set.univ = ENNReal.ofReal (totalVolume g) :=
      (ENNReal.ofReal_toReal (ne_of_lt (actual_finitePositiveVolume g).finite)).symm
    _ = ENNReal.ofReal ((2 * Real.pi ^ 2) * riemannianChartFactor.toReal) := congrArg _ h
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hk, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full radial mass forces the actual cut time to equal the complex
conjugate radius in every direction. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem complex_cut_time_all_directions (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) :
    actualCutTime g (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) =
      complexJacobiRadius := by
  obtain ⟨w,hs,hn,hp⟩ := halfFlat_dimension_one_parallel_unit_form hRic hminus hdim
  have hnorm := halfFlat_dimension_one_norm hRic hminus hdim
  let : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
  let : Measure.IsOpenPosMeasure sphereMeasure := sphereMeasure_openPos
  let R := fun q : Directions => e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := fun q : Directions => complexRadialMass (actualCutTime g (R q))
  have hRpos (q : Directions) : R q ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hcut (q : Directions) : actualCutTime g (R q) ≤ complexJacobiRadius :=
    parallel_form_cut_le_radius hRic hminus hnorm w hs hn hp _ (hRpos q)
  have hle (q : Directions) : F q ≤ 1 := complexRadialMass_le_one _ (hcut q)
  have hupper : (∫⁻ q, F q ∂sphereMeasure) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _q : Directions, (1 : ℝ≥0∞) ∂sphereMeasure := lintegral_mono hle
      _ = 1 := by simp
  have hlower : 1 ≤ ∫⁻ q, F q ∂sphereMeasure := by
    have h := complex_volume_le_cut_mass hRic hminus hnorm w hs hn hp e he
    rw [complex_volumeMeasure hRic hminus hdim] at h
    have hk := ENNReal.toReal_pos_iff.mp riemannianChartFactor_toReal_pos
    have hc := (ENNReal.mul_le_mul_iff_right hk.1.ne' hk.2.ne).mp h
    have hc' : ENNReal.ofReal (2 * Real.pi ^ 2) * 1 ≤
        ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q, F q ∂sphereMeasure := by
      simpa only [mul_one] using hc
    exact (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (2 * Real.pi ^ 2) ≠ 0)
      ENNReal.ofReal_ne_top).mp hc'
  have hInt : (∫⁻ q, F q ∂sphereMeasure) = 1 := le_antisymm hupper hlower
  have hae : F =ᵐ[sphereMeasure] (fun _ => 1) := by
    exact ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hle) (hInt ▸ ENNReal.one_ne_top)
      aemeasurable_const (by first | (simp [hInt]; done) | simpa using hInt.ge)
  have haec : ∀ᵐ q : Directions ∂sphereMeasure,
      complexJacobiRadius ≤ actualCutTime g (R q) := by
    filter_upwards [hae] with q hq
    by_contra hnot
    exact (complexRadialMass_lt_one _
      ⟨(actualCutTime_pos g o hRic (R q) (hRpos q)).le,lt_of_not_ge hnot⟩).ne hq
  have hR : Continuous R := (continuous_frameRotate g).comp
    (continuous_const.prodMk (continuous_orientedToOrthogonal.comp continuous_directionOrientedMatrix))
  have hclosed : IsClosed {q : Directions | complexJacobiRadius ≤ actualCutTime g (R q)} :=
    ((actualCutTime_upperSemicontinuous g).isClosed_preimage complexJacobiRadius).preimage hR
  have hdense := Measure.dense_of_ae haec
  have hall : {q : Directions | complexJacobiRadius ≤ actualCutTime g (R q)} = univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  apply le_antisymm (hcut q)
  have hq : q ∈ {q : Directions | complexJacobiRadius ≤ actualCutTime g (R q)} := by
    rw [hall]
    exact mem_univ q
  exact hq

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual exponential is minimizing and injective inside the complex conjugate ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_minimizing (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ complexJacobiRadius) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero]
    exact (metricDistance_eq_zero_iff g _ _).mpr rfl
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hm : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
    apply (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg _)).mpr
    rw [complex_cut_time_all_directions hRic hminus hdim e he q]
    exact hv
  rwa [hrad] at hm

theorem complex_direction_injective (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) complexJacobiRadius)
    (hqp : frameExponential g o e (t • q.val) = frameExponential g o e (t • p.val)) : q = p := by
  let s := (complexJacobiRadius - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith [ht.2]
  have hsum : t + s < complexJacobiRadius := by dsimp [s]; linarith [ht.2]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := parallelFrameFlowMap g 0 (-s) f
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf (-s)
  have hbase : F.base = frameExponential g o e ((-s) • q.val) :=
    (frameExponential_direction_ray g o e he q (-s)).symm
  have hend : frameExponential g o F ((t + s) • coordinateVector 0) =
      frameExponential g o e (t • p.val) := by
    rw [frameExponential_shift_first g o f hf (t + s) (-s),
      show t + s + -s = t by ring]
    exact (frameExponential_direction_ray g o e he q t).symm.trans hqp
  have hnorm : ‖(t + s) • (coordinateVector 0 : FourSpace)‖ = t + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos ht.1 hs)]
    simp [coordinateVector]
  have hmin := frameExponential_complex_minimizing hRic hminus hdim F hF
    ((t + s) • coordinateVector 0) (by rw [hnorm]; exact hsum.le)
  rw [hbase, hend, hnorm] at hmin
  have hd := (metricDistance_eq_iff g _ _ (add_pos ht.1 hs).le).mp hmin
  rw [add_comm t s] at hd
  exact Subtype.ext (frameExponential_no_minimizing_corner g o e q.val p.val
    q.property p.property s t hs ht.1 hd)


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual closed complex-conjugate ball covers the manifold. Its
interior and boundary are distinguished by the actual distance from the center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualMinimizingTangentDomain_complex (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    actualMinimizingTangentDomain g o e = Metric.closedBall 0 complexJacobiRadius := by
  ext v
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hv
    by_cases hz : v = 0
    · simpa only [hz, norm_zero] using complexJacobiRadius_pos.le
    let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    have hq : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
    have hcut := (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖
      (norm_nonneg _)).mp (hq.symm ▸ hv)
    rwa [complex_cut_time_all_directions hRic hminus hdim e he q] at hcut
  · exact frameExponential_complex_minimizing hRic hminus hdim e he v

theorem frameExponential_complex_closedBall_image (hRic : RicciThree g)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    frameExponential g o e '' Metric.closedBall 0 complexJacobiRadius = univ := by
  rw [← actualMinimizingTangentDomain_complex hRic hminus hdim e he]
  exact actualMinimizingTangentDomain_image g o hRic e he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual globally defined projective map covers the manifold and
preserves all radial distances at the Ricci-three scale. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_radial (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) (q : Directions) :
    metricDistance g e.base (actualComplexProjectiveMap g o e (complexProjectivePolar t q)) = t := by
  have hn : ‖t • q.val‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,q.property,mul_one]
  rw [actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
    w hstar hw hz e he hstd t ht q,
    frameExponential_complex_minimizing hRic hminus hdim e he _ (by rw [hn]; exact ht.2),hn]

theorem actualComplexProjectiveMap_surjective (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm) :
    Function.Surjective (actualComplexProjectiveMap g o e) := by
  intro x
  have hx : x ∈ frameExponential g o e '' Metric.closedBall 0 complexJacobiRadius := by
    rw [frameExponential_complex_closedBall_image hRic hminus hdim e he]
    trivial
  obtain ⟨v,hv,hx⟩ := hx
  have hvr : ‖v‖ ≤ complexJacobiRadius := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  by_cases h0 : v = 0
  · refine ⟨complexProjectivePolar 0 firstDirection,?_⟩
    rw [actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
      w hstar hw hz e he hstd 0 ⟨le_rfl,complexJacobiRadius_pos.le⟩ firstDirection,zero_smul]
    simpa only [h0] using hx
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0),one_smul]
  refine ⟨complexProjectivePolar ‖v‖ q,?_⟩
  rw [actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
    w hstar hw hz e he hstd ‖v‖ ⟨norm_nonneg _,hvr⟩ q,hq]
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity of the genuine projective map, including its boundary fibers. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_continuous (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm) :
    Continuous (actualComplexProjectiveMap g o e) := by
  apply complexPolarProjection_isQuotientMap.continuous_iff.mpr
  have heq : actualComplexProjectiveMap g o e ∘ complexPolarProjection =
      fun p : ComplexPolarDomain => frameExponential g o e (p.1.val • p.2.val) := by
    funext p
    exact actualComplexProjectiveMap_polar hRic hminus
      (halfFlat_dimension_one_norm hRic hminus hdim) w hstar hw hz e he hstd
      p.1.val p.1.property p.2
  rw [heq]
  exact (frameExponential_continuous g o e).comp
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact radial distance and uniqueness of the actual projective map
away from the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_fiber_eq_of_radial_lt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (p q : ComplexProjective2)
    (heq : actualComplexProjectiveMap g o e p = actualComplexProjectiveMap g o e q)
    (hlt : metricDistance g e.base (actualComplexProjectiveMap g o e p) < complexJacobiRadius) :
    p = q := by
  obtain ⟨t,ht,u,hp⟩ := complexProjectivePolar_surjective p
  obtain ⟨s,hs,v,hq⟩ := complexProjectivePolar_surjective q
  have hpt := actualComplexProjectiveMap_radial hRic hminus hdim w hstar hw hz e he hstd t ht u
  have hqs := actualComplexProjectiveMap_radial hRic hminus hdim w hstar hw hz e he hstd s hs v
  rw [hp] at hpt
  rw [hq] at hqs
  have hts : t = s := hpt.symm.trans ((congrArg (metricDistance g e.base) heq).trans hqs)
  rw [← hts] at hs hq
  have htR : t < complexJacobiRadius := hpt ▸ hlt
  by_cases ht0 : t = 0
  · rw [← hp,← hq,ht0,complexProjectivePolar_zero,complexProjectivePolar_zero]
  have heq' : frameExponential g o e (t • u.val) = frameExponential g o e (t • v.val) := by
    rw [← actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
      w hstar hw hz e he hstd t ht u,
      ← actualComplexProjectiveMap_polar hRic hminus (halfFlat_dimension_one_norm hRic hminus hdim)
      w hstar hw hz e he hstd t hs v,hp,hq]
    exact heq
  have huv := complex_direction_injective hRic hminus hdim e he u v t
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),htR⟩ heq'
  rw [← hp,← hq,huv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine projective map in the ordinary affine chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_affine (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (z : EuclideanSpace ℂ (Fin 2)) :
    actualComplexProjectiveMap g o e (complexAffinePoint z) =
      frameExponential g o e (complexAffineLog z) := by
  obtain ⟨q,hq,hlog⟩ := complexAffinePoint_polar_log z
  rw [← hq,actualComplexProjectiveMap_polar hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) w hstar hw hz e he hstd
    (complexAffineRadius z) ⟨(complexAffineRadius_mem z).1,(complexAffineRadius_mem z).2.le⟩ q,hlog]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity everywhere and C1 regularity in regular homogeneous affine coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_unit_continuous (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) :
    Continuous (fun u : UnitSphere CP2Vector =>
      actualComplexProjectiveMap g o e (complexSphereProjection u)) :=
  (actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd).comp
    complexSphereProjection_continuous

theorem actualComplexProjectiveMap_lift_contMDiffAt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {u : ℝ → UnitSphere CP2Vector} {s : ℝ}
    (hu : ContDiffAt ℝ 1 (fun r => (u r).val) s)
    (hhead : (u s).val 0 ≠ 0) (htail : complexVectorAffine (u s).val ≠ 0) :
    ContMDiffAt 𝓘(ℝ, ℝ) I4 1
      (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) s := by
  let z : ℝ → EuclideanSpace ℂ (Fin 2) := fun r => complexVectorAffine (u r).val
  let α : ℝ → FourSpace := fun r => complexAffineLog (z r)
  have hdz : ContDiffAt ℝ 1 z s := by
    exact ContDiffAt.comp (f := fun r => (u r).val) (g := complexVectorAffine) s
      (complexVectorAffine_contDiffAt hhead) hu
  have hdα : ContDiffAt ℝ 1 α s := by
    exact ContDiffAt.comp (f := z) (g := complexAffineLog) s
      (complexAffineLog_contDiffAt htail) hdz
  have hhead' : ∀ᶠ r in 𝓝 s, (u r).val 0 ≠ 0 :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 0).continuousAt.comp
      hu.continuousAt).eventually_ne hhead
  have hγ : (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) =ᶠ[𝓝 s]
      (fun r => frameExponential g o e (α r)) := by
    filter_upwards [hhead'] with r hr
    rw [complexSphereProjection_affine (u r) hr]
    exact actualComplexProjectiveMap_affine hRic hminus hdim W hstar hw hz e he hstd _
  have hcmp : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 (fun r => frameExponential g o e (α r)) s :=
    (frameExponential_contMDiff g o e).contMDiffAt.comp s hdα.contMDiffAt
  exact hcmp.congr_of_eventuallyEq hγ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine projective map has the expected speed in every regular affine lift. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_lift_speed (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {u : ℝ → UnitSphere CP2Vector} {u' : CP2Vector} {s : ℝ}
    (hdu : HasDerivAt (fun r => (u r).val) u' s)
    (hhead : (u s).val 0 ≠ 0) (htail : complexVectorAffine (u s).val ≠ 0) :
    Real.sqrt 2 * ‖complexHorizontalPart (u s).val u'‖ =
      metricTangentNorm g (actualComplexProjectiveMap g o e (complexSphereProjection (u s)))
        (mfderiv 𝓘(ℝ, ℝ) I4
          (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) s 1) := by
  let z : ℝ → EuclideanSpace ℂ (Fin 2) := fun r => complexVectorAffine (u r).val
  let α : ℝ → FourSpace := fun r => complexAffineLog (z r)
  have hdz : DifferentiableAt ℝ z s := by
    exact DifferentiableAt.comp (f := fun r => (u r).val) (g := complexVectorAffine) s
      (complexVectorAffine_differentiableAt hhead) hdu.differentiableAt
  have hdα : DifferentiableAt ℝ α s := by
    exact DifferentiableAt.comp (f := z) (g := complexAffineLog) s
      (complexAffineLog_differentiableAt htail) hdz
  have hα0 : α s ≠ 0 := complexAffineLog_ne_zero htail
  let q : Directions := ⟨‖α s‖⁻¹ • α s,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hα0)]⟩
  have hrad : α s = ‖α s‖ • q.val := by
    change α s = ‖α s‖ • (‖α s‖⁻¹ • α s)
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hα0),one_smul]
  have hreg : ∀ᶠ r in 𝓝 s, (u r).val 0 ≠ 0 ∧ z r ≠ 0 := by
    have hh := ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) 0).continuousAt.comp
      hdu.continuousAt).eventually_ne hhead
    have ht := hdz.continuousAt.eventually_ne htail
    exact hh.and ht
  have hγ : (fun r => actualComplexProjectiveMap g o e (complexSphereProjection (u r))) =ᶠ[𝓝 s]
      (fun r => frameExponential g o e (α r)) := by
    filter_upwards [hreg] with r hr
    rw [complexSphereProjection_affine (u r) hr.1]
    exact actualComplexProjectiveMap_affine hRic hminus hdim W hstar hw hz e he hstd _
  have halign : ∀ᶠ r in 𝓝 s, ∃ a : ℂ, complexNormalLift (α r) = a • (u r).val := by
    filter_upwards [hreg] with r hr
    have hp : complexNormalPoint (α r) = complexSphereProjection (u r) :=
      (complexNormalPoint_affineLog hr.2).trans
        (complexAffinePoint_vector (u r).val hr.1 (unitSphere_ne_zero (u r)))
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
    exact ⟨a,ha.symm⟩
  have hdlift := complexNormalLift_hasDerivAt hdα.hasDerivAt (norm_pos_iff.mpr hα0) q hrad
  have hinv := complexHorizontalPart_curve_invariant (fun r => (u r).property)
    (fun r => complexNormalLift_norm (α r)) halign hdu hdlift
  have hs := frameExponential_complex_curve_speed hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) W hstar hw hz e he hstd hdα
    (norm_pos_iff.mpr hα0) q hrad
  rw [hdlift.deriv,← complexHorizontalPart_norm_sq _ _ (complexNormalLift_norm (α s)),
    Real.sqrt_sq (norm_nonneg _)] at hs
  rw [hinv] at hs
  exact hs.trans (metric_curve_speed_congr hγ).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A projective section is continuous wherever the actual fiber is a singleton. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_section_continuousAt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (x : M) (hR : metricDistance g e.base x < complexJacobiRadius) :
    ContinuousAt S x := by
  let : CompactSpace ComplexProjective2 := complexProjective_compactSpace
  have hF := actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd
  have huniq (p : ComplexProjective2) (hp : actualComplexProjectiveMap g o e p = x) : p = S x :=
    actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
      p (S x) (hp.trans (hS x).symm) (by rwa [hp])
  change Tendsto S (𝓝 x) (𝓝 (S x))
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V,hVU,hV,hsV⟩ := mem_nhds_iff.mp hU
  have hclosed : IsClosed (actualComplexProjectiveMap g o e '' Vᶜ) :=
    hF.isClosedMap _ hV.isClosed_compl
  have hx : x ∈ (actualComplexProjectiveMap g o e '' Vᶜ)ᶜ := by
    rintro ⟨p,hp,hpx⟩
    exact hp ((huniq p hpx) ▸ hsV)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
  apply hVU
  by_contra hsy
  exact hy ⟨S y,hsy,hS y⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Density and the actual chart distance estimate give singleton fibers at the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjectiveMap_interior_distance_lt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {P : ComplexProjective2} (hP : P ∈ complexProjectiveInterior) :
    metricDistance g e.base (actualComplexProjectiveMap g o e P) < complexJacobiRadius := by
  obtain ⟨t,ht,q,rfl⟩ := hP
  rw [actualComplexProjectiveMap_radial hRic hminus hdim W hstar hw hz e he hstd t ⟨ht.1,ht.2.le⟩ q]
  exact ht.2

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


