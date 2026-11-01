-- Prove2me | Definitions.Def_OAIQ091C019
-- name    : OAIQ091C019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:56:34.786952+00:00
-- url     : https://prove2.me/theorems/8b6aa34d-efa1-4ed8-825f-1c39cbc3bd2e
-- title:
--   Definitions bundle OAIQ091C019 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 458 declarations of OpenAI's Lean: 121 definitions, 3 inductive types or structures, 13 instances and 321 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatCommonEulerMember.eulerColumnTrace`, `OAI.PositiveEinsteinFour.Geometry.HeatCommonEulerMember.scalarData`, `OAI.PositiveEinsteinFour.Geometry.HeatCommonNormalMember.parametrixData`, `OAI.PositiveEinsteinFour.Geometry.HeatEulerFiber`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilyOneCoefficients.amplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilyOneCoefficients.eulerAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilyOneCoefficients.eulerPolynomial`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilySmoothCoefficients.amplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilySmoothCoefficients.scalarAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerFirstAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerFirstSource`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.firstSource`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.oneCompanion`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalExtension.scalarAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalExtension.scalarCutoff`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalExtension.scalarParametrix`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalOneExtension.amplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalOneExtension.firstSource`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.column`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.normalizedColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneNormalizedColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.column`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.function`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.normalizedColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.polynomial`, `OAI.PositiveEinsteinFour.Geometry.OneFormL2`, `OAI.PositiveEinsteinFour.Geometry.SmoothL2OneForm`, `OAI.PositiveEinsteinFour.Geometry.canonicalParallelMetricData`, `OAI.PositiveEinsteinFour.Geometry.fourHeatEikonalDefect`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneCoefficient`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOnePolynomial`, `OAI.PositiveEinsteinFour.Geometry.fourHeatRadialAverageDerivative`, `OAI.PositiveEinsteinFour.Geometry.frameUnitRadialState`, `OAI.PositiveEinsteinFour.Geometry.geodesicFramePosition`, `OAI.PositiveEinsteinFour.Geometry.geodesicFrameVelocity`, `OAI.PositiveEinsteinFour.Geometry.geodesicNormalPosition`, `OAI.PositiveEinsteinFour.Geometry.halfSmoothBump` and 84 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels06.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C038` and `OAIQ091C018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C023`, `OAIQ091C024`, `OAIQ091C025` and `OAIQ091C026`; the proof of `OAI_PositiveEinsteinFour_Quadratic_coupling_matrix_nonneg`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C038
import Definitions.Def_OAIQ091C018

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The kinetic flow at zero momentum. Its stationary solution and
linearization provide the local inverse-function input for exponential
coordinates at the zero tangent vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]


theorem kineticHamiltonianField_zero_directional (g : SmoothMetric M) (c : M)
    (x dx dp : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c)) (x, 0) (dx, dp) =
      (WithLp.toLp 2 ((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp dp), 0) := by
  let γ : ℝ → CotangentCoordinates := fun s => (x + s • dx, s • dp)
  have hx' : HasDerivAt (fun s : ℝ => x + s • dx) dx 0 := by
    simpa only [Pi.add_apply, id_eq, one_smul, zero_add] using! (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const dx)
  have hp' : HasDerivAt (fun s : ℝ => s • dp) dp 0 := by
    simpa only [id_eq, one_smul] using! (hasDerivAt_id (0 : ℝ)).smul_const dp
  have hγ : HasDerivAt γ (dx, dp) 0 := hx'.prodMk hp'
  have hγ0 : γ 0 = (x, 0) := by simp [γ]
  have hdet := (metricInChart_posDef g c x hx).det_pos.ne'
  have hP (i : Fin 4) : HasDerivAt (fun s : ℝ => (s • dp) i) (dp i) 0 :=
    (show FourSpace →L[ℝ] ℝ from EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 hp'
  have hG (i j : Fin 4) :
      HasDerivAt (fun s : ℝ => (metricInChart g c (x + s • dx))⁻¹ i j)
        (fderiv ℝ (fun z => (metricInChart g c z)⁻¹ i j) x dx) 0 := by
    have hd : HasFDerivAt (fun z => (metricInChart g c z)⁻¹ i j)
        (fderiv ℝ (fun z => (metricInChart g c z)⁻¹ i j) x) (x + (0 : ℝ) • dx) := by
      simpa using ((metricInChart_inv_contDiffAt g c x hx hdet i j).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
    simpa only [Function.comp_def, zero_smul, add_zero] using hd.comp_hasDerivAt 0 hx'
  have hΓ (i j k : Fin 4) :
      HasDerivAt (fun s : ℝ => connectionMatrix g c i (x + s • dx) j k)
        (fderiv ℝ (fun z => connectionMatrix g c i z j k) x dx) 0 := by
    have hd : HasFDerivAt (fun z => connectionMatrix g c i z j k)
        (fderiv ℝ (fun z => connectionMatrix g c i z j k) x) (x + (0 : ℝ) • dx) := by
      simpa only [zero_smul, add_zero, connectionMatrix] using!
        ((christoffel_contDiffAt g c x hx hdet j i k).differentiableAt
          (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
    simpa only [Function.comp_def, zero_smul, add_zero] using hd.comp_hasDerivAt 0 hx'
  have hv (i : Fin 4) : HasDerivAt
      (fun s : ℝ => ((metricInChart g c (x + s • dx))⁻¹ *ᵥ WithLp.ofLp (s • dp)) i)
      (((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp dp) i) 0 := by
    have hd := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hG i j).mul (hP j))
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, zero_smul, add_zero, WithLp.ofLp_zero, Pi.zero_apply,
      mul_zero, zero_add] using hd
  have hf (i : Fin 4) : HasDerivAt
      (fun s : ℝ => WithLp.ofLp (s • dp) ⬝ᵥ
        (connectionMatrix g c i (x + s • dx) *ᵥ
          ((metricInChart g c (x + s • dx))⁻¹ *ᵥ WithLp.ofLp (s • dp)))) 0 0 := by
    have hd := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hP j).mul (HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) =>
        (hΓ i j k).mul (hv k))))
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, zero_smul, add_zero, WithLp.ofLp_zero, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_mul, zero_add] using hd
  have hvel := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt 0
    (hasDerivAt_pi.mpr hv)
  have hforce := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt 0
    (hasDerivAt_pi.mpr hf)
  have hpair : HasDerivAt (fun s : ℝ =>
      (WithLp.toLp 2 ((metricInChart g c (γ s).1)⁻¹ *ᵥ WithLp.ofLp (γ s).2),
        WithLp.toLp 2 (fun r => WithLp.ofLp (γ s).2 ⬝ᵥ
          (connectionMatrix g c r (γ s).1 *ᵥ
            ((metricInChart g c (γ s).1)⁻¹ *ᵥ WithLp.ofLp (γ s).2)))))
      (WithLp.toLp 2 ((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp dp), 0) 0 := by
    convert hvel.prodMk hforce using 1 <;> rfl
  have he : ∀ᶠ s in 𝓝 (0 : ℝ), (γ s).1 ∈ (chartAt FourSpace c).target := by
    have := hx'.continuousAt.preimage_mem_nhds ((chartAt FourSpace c).open_target.mem_nhds
      (show x + (0 : ℝ) • dx ∈ (chartAt FourSpace c).target by simpa using hx))
    exact this
  have hactual := hpair.congr_of_eventuallyEq (he.mono fun s hs =>
    kineticHamiltonianField_coordinates g c (γ s) hs)
  have hd := ((kineticHamiltonianField_contDiffAt g c (x, 0) hx).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hD : HasFDerivAt (cotangentHamiltonianField (kineticHamiltonian g c))
      (fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c)) (x, 0)) (γ 0) := by
    simpa only [hγ0] using hd
  have hd' := hD.comp_hasDerivAt 0 hγ
  exact hd'.unique hactual

/-- At zero momentum the derivative of the kinetic Hamiltonian vector field
is the nilpotent position-from-momentum map. -/
theorem kineticHamiltonianField_hasFDerivAt_zero (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    HasFDerivAt (cotangentHamiltonianField (kineticHamiltonian g c))
      (kineticZeroDifferential g c x) (x, 0) := by
  have he : fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c)) (x, 0) =
      kineticZeroDifferential g c x := by
    apply ContinuousLinearMap.ext
    intro u
    change _ = (WithLp.toLp 2 ((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp u.2), 0)
    exact kineticHamiltonianField_zero_directional g c x u.1 u.2 hx
  rw [← he]
  exact ((kineticHamiltonianField_contDiffAt g c (x, 0) hx).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hilbert completion of actual smooth two-form sections with their
intrinsic L2 pairing. The inclusion of pointwise smooth sections is an
injective linear isometry with dense range. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

/- The L2 topology of the completion differs from the pointwise topology
on the smooth function submodule. -/

def smoothTwoFormToL2 : SmoothL2TwoForm o →ₗᵢ[ℝ] TwoFormL2 o :=
  UniformSpace.Completion.toComplₗᵢ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Raising the momentum in the actual kinetic Hamiltonian gives the
ordinary tangent-coordinate geodesic field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def kineticVelocityCoordinates (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) : FourSpace × FourSpace :=
  (p.1, WithLp.toLp 2 ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2))

def kineticVelocityRate (g : SmoothMetric M) (c : M)
    (p dp : CotangentCoordinates) : FourSpace × FourSpace :=
  (dp.1, WithLp.toLp 2
    ((∑ r, dp.1 r • matrixPartial (fun x => (metricInChart g c x)⁻¹) r p.1) *ᵥ
        WithLp.ofLp p.2 + (metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp dp.2))

theorem kineticVelocityCoordinates_contDiffAt (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (kineticVelocityCoordinates g c) p := by
  have hH (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => (metricInChart g c q.1)⁻¹ i j) p :=
    (metricInChart_inv_contDiffAt g c p.1 hp
      (metricInChart_posDef g c p.1 hp).det_pos.ne' i j).comp p contDiffAt_fst
  apply contDiffAt_fst.prodMk
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℝ ∞ (fun q : CotangentCoordinates =>
    ∑ j, (metricInChart g c q.1)⁻¹ i j * q.2 j) p
  apply ContDiffAt.sum
  intro j _
  have hq : ContDiffAt ℝ ∞ (fun q : CotangentCoordinates => q.2 j) p := by fun_prop
  exact (hH i j).mul hq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal components of an actual first variation satisfy the actual
matrix Jacobi equation in a parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def geodesicFramePosition (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (Z : ℝ → FourSpace × FourSpace) :
    ℝ → JacobiCoordinateVector :=
  inverseFrameComponents (fun s => frameChartMatrix g c (e s))
    (fun s => WithLp.ofLp (Z s).1)

def geodesicFrameVelocity (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (γ Z : ℝ → FourSpace × FourSpace) :
    ℝ → JacobiCoordinateVector :=
  inverseFrameComponents (fun s => frameChartMatrix g c (e s))
    (geodesicVariationCovariantDerivative g c γ Z)

def geodesicNormalPosition (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (Z : ℝ → FourSpace × FourSpace)
    (s : ℝ) : Fin 3 → ℝ := fun i => geodesicFramePosition g c e Z s i.succ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Higher finite regularity of the kinetic flow at initial time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem KineticLocalFlow.contDiffAt_initial {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p)
    (hp : p.1 ∈ (chartAt FourSpace c).target) (n : ℕ) :
    ContDiffAt ℝ n F.map (p, 0) := by
  apply FlowCalculus.local_flow_contDiffAt_finite n CotangentCoordinates
    (cotangentHamiltonianField (kineticHamiltonian g c)) F.map p
  · exact (kineticHamiltonianField_contDiffAt g c p hp).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · apply contDiffAt_zero.mpr
    refine ⟨ball p F.radius ×ˢ Ioo (-F.time) F.time, ?_, F.continuous_map⟩
    apply (isOpen_ball.prod isOpen_Ioo).mem_nhds
    exact ⟨mem_ball_self F.radius_pos, by constructor <;> linarith [F.time_pos]⟩
  · filter_upwards [ball_mem_nhds p F.radius_pos] with q hq
    exact F.initial q hq
  · have hU : ball p F.radius ×ˢ Ioo (-F.time) F.time ∈ 𝓝 (p, (0 : ℝ)) :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds
        ⟨mem_ball_self F.radius_pos, by constructor <;> linarith [F.time_pos]⟩
    filter_upwards [hU] with z hz
    exact F.time_derivative z.1 hz.1 z.2 hz.2

theorem KineticLocalFlow.exists_pos_contDiffAt_slice {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p)
    (hp : p.1 ∈ (chartAt FourSpace c).target) (n : ℕ) :
    ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ContDiffAt ℝ n (fun z => F.map (z, t)) p := by
  have hn := (F.contDiffAt_initial hp n).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have htend : Tendsto (fun t : ℝ => (p, t)) (𝓝 0) (𝓝 (p, 0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hn)
  let t := min F.time δ / 2
  have ht0 : 0 < t := half_pos (lt_min F.time_pos hδ)
  have htT : t < F.time := (half_lt_self (lt_min F.time_pos hδ)).trans_le (min_le_left _ _)
  have htδ : t < δ := (half_lt_self (lt_min F.time_pos hδ)).trans_le (min_le_right _ _)
  refine ⟨t, ht0, ⟨by linarith [F.time_pos], htT⟩, ?_⟩
  have hFt : ContDiffAt ℝ n F.map (p, t) :=
    hnear (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht0] using htδ)
  exact hFt.comp p (contDiffAt_id.prodMk contDiffAt_const)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual first variation at a stationary zero-momentum geodesic.
This identifies the derivative used in the local exponential map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem kineticZeroDifferential_apply (g : SmoothMetric M) (c : M) (x : FourSpace)
    (u : CotangentCoordinates) :
    kineticZeroDifferential g c x u =
      (WithLp.toLp 2 ((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp u.2), 0) := rfl

theorem kineticZeroDifferential_square (g : SmoothMetric M) (c : M) (x : FourSpace)
    (u : CotangentCoordinates) :
    kineticZeroDifferential g c x (kineticZeroDifferential g c x u) = 0 := by
  rw [kineticZeroDifferential_apply, kineticZeroDifferential_apply]
  simp

/-- The first variation is exactly the shear `id + t D`, where `D² = 0`. -/
theorem KineticLocalFlow.zero_momentum_variation (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (F : KineticLocalFlow g c (x, 0)) (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    F.variation ((x, 0), t) = ContinuousLinearMap.id ℝ CotangentCoordinates +
      t • kineticZeroDifferential g c x := by
  apply ContinuousLinearMap.ext
  intro u
  let D := kineticZeroDifferential g c x
  have hD := kineticHamiltonianField_hasFDerivAt_zero g c x hx
  have hq : (x, (0 : FourSpace)) ∈ Metric.ball (x, 0) F.radius :=
    Metric.mem_ball_self F.radius_pos
  have hactual (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      HasDerivAt (fun r => F.variation ((x, 0), r) u)
        (D (F.variation ((x, 0), s) u)) s := by
    have hd := (F.variation_derivative (x, 0) hq s hs).clm_apply
      (hasDerivAt_const s u)
    rw [F.zero_momentum_fixed g c x hx s hs, hD.fderiv] at hd
    simpa only [D, ContinuousLinearMap.comp_apply, map_zero, add_zero] using hd
  have hmodel (s : ℝ) : HasDerivAt (fun r : ℝ => u + r • D u)
      (D (u + s • D u)) s := by
    have he : D (u + s • D u) = D u := by
      simp only [map_add, map_smul, D, kineticZeroDifferential_square, smul_zero, add_zero]
    rw [he]
    simpa only [id_eq, one_smul, zero_add] using!
      (hasDerivAt_const s u).add ((hasDerivAt_id s).smul_const (D u))
  have hz : (0 : ℝ) ∈ Ioo (-F.time) F.time :=
    ⟨by linarith [F.time_pos], F.time_pos⟩
  have heq := Jacobi.linear_curve_eqOn_interval (fun _ => D) ‖D‖₊
    (fun _ => le_rfl) hactual (fun s _ => hmodel s) hz
    (by simp [F.initial_variation (x, 0) hq])
  exact heq ht


/-- The same endpoint derivative is strict, as required by the inverse
function theorem. It follows directly from the constructed joint flow. -/
theorem KineticLocalFlow.zero_momentum_endpoint_strictDerivative (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (F : KineticLocalFlow g c (x, 0)) (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    HasStrictFDerivAt (fun p : FourSpace => (F.map ((x, p), t)).1)
      (t • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) ((metricInChart g c x)⁻¹)) 0 := by
  have hq : (x, (0 : FourSpace)) ∈ Metric.ball (x, 0) F.radius :=
    Metric.mem_ball_self F.radius_pos
  have harg : HasStrictFDerivAt (fun p : FourSpace => ((x, p), t))
      (((0 : FourSpace →L[ℝ] FourSpace).prod (ContinuousLinearMap.id ℝ FourSpace)).prod
        (0 : FourSpace →L[ℝ] ℝ)) 0 :=
    ((hasStrictFDerivAt_const x 0).prodMk (hasStrictFDerivAt_id 0)).prodMk
      (hasStrictFDerivAt_const t 0)
  have h := (ContinuousLinearMap.fst ℝ FourSpace FourSpace).hasStrictFDerivAt.comp 0
    ((F.joint_derivative (x, 0) hq t ht).comp 0 harg)
  rw [F.zero_momentum_variation g c x hx t ht] at h
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  apply ContinuousLinearMap.ext
  intro u
  simp [ContinuousLinearMap.comp_apply, kineticZeroDifferential]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite curvature contraction in the two-form Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormTensor_pairing (a b : TwoFormFour) :
    frameTensorPairing (twoFormTensor a) (twoFormTensor b) = 2 * inner ℝ a b := by
  rw [frameTensorPairing, twoFormCurvature_sum_two_indices]
  change (∑ i, ∑ j, twoFormMatrix a i j * twoFormMatrix b i j) = 2 * ∑ i, b i * a i
  simp [Fin.sum_univ_succ, twoFormMatrix]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric's actual four-tensor in moving orthonormal frames, with
its chart realization and uniform bound on a closed manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def twoFormMetricCurvatureTensor (g : SmoothMetric M) (e : FrameBundle g) :
    CovariantCoordinates 4 :=
  frameTensor e.frame.matrix (curvatureCoordinates g e.base (chartAt FourSpace e.base e.base))

theorem twoFormMetricCurvatureTensor_skew (g : SmoothMetric M) (e : FrameBundle g)
    (i j k l : Fin 4) :
    twoFormMetricCurvatureTensor g e ![j,i,k,l] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
  change frameTensor e.frame.matrix _ ![j,i,k,l] = -frameTensor e.frame.matrix _ ![i,j,k,l]
  rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
  exact frame_algebraic_firstSkew e.frame i j k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth approximation preserving the actual alternating tensor type
and compact support. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heat_alternating_smooth_approx
    (F : FourSpace → CovariantCoordinates 2) (hF : Continuous F)
    (ha : ∀ z i j, F z ![j,i] = -F z ![i,j]) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : FourSpace → CovariantCoordinates 2, ContDiff ℝ ∞ H ∧
      (∀ z i j, H z ![j,i] = -H z ![i,j]) ∧
      tsupport H ⊆ tsupport F ∧ ∀ z a, |H z a - F z a| < ε := by
  let E : CovariantCoordinates 2 →L[ℝ] TwoFormFour :=
    (twoFormExtractLinear.comp twoTensorMatrixLinear).toContinuousLinearMap
  let T : TwoFormFour →L[ℝ] CovariantCoordinates 2 :=
    twoFormTensorLinear.toContinuousLinearMap
  have hEF : Continuous (fun z => E (F z)) := E.continuous.comp hF
  obtain ⟨v, hv, hvd, hvs⟩ := hEF.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => ε / (‖T‖ + 1)) continuous_const (fun _ => div_pos hε (by positivity))
  refine ⟨fun z => T (v z), T.contDiff.comp hv, ?_, ?_, ?_⟩
  · intro z i j
    exact congrArg (fun A : Mat4 => A i j) (twoFormMatrix_skew (v z))
  · apply closure_mono
    intro z hz
    have hvz : v z ≠ 0 := by
      intro h
      apply hz
      change T (v z) = 0
      rw [h, map_zero]
    have hEz := hvs hvz
    intro h
    apply hEz
    change E (F z) = 0
    rw [h, map_zero]
  · intro z a
    have he : T (E (F z)) = F z := twoFormTensor_extract (F z) (ha z)
    have hd : ‖v z - E (F z)‖ < ε / (‖T‖ + 1) := by
      simpa only [dist_eq_norm] using hvd z
    have hn : ‖T (v z) - F z‖ < ε := by
      rw [← he, ← map_sub]
      have h1 := T.le_opNorm (v z - E (F z))
      have h2 := (mul_lt_mul_of_pos_left hd (show 0 < ‖T‖ + 1 by positivity))
      have h3 : (‖T‖ + 1) * (ε / (‖T‖ + 1)) = ε := mul_div_cancel₀ ε (by positivity)
      rw [h3] at h2
      nlinarith [norm_nonneg (v z - E (F z))]
    exact (show |T (v z) a - F z a| ≤ ‖T (v z) - F z‖ from
      (norm_le_pi_norm (T (v z) - F z) a)).trans_lt hn

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported chart tensor, transported into the centered
tangent coordinates and then into any other chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem chartInverseMatrix_det_ne_zero (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : (chartInverseMatrix c z).det ≠ 0 := by
  have h := chartTransitionMatrix_det_ne_zero g c ((chartAt FourSpace c).symm z) z hz
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rwa [chartTransitionMatrix_to_center c z hz] at h

def twoFormChartTensor (c : M) (F : FourSpace → CovariantCoordinates 2) (x : M) :
    CovariantCoordinates 2 := by
  classical
  exact if x ∈ (chartAt FourSpace c).source then
    frameTensor (chartInverseMatrix c (chartAt FourSpace c x))⁻¹ (F (chartAt FourSpace c x))
  else 0

def twoFormChartFamily (c : M) (F : FourSpace → CovariantCoordinates 2)
    (d : M) (z : FourSpace) : CovariantCoordinates 2 :=
  frameTensor (chartInverseMatrix d z) (twoFormChartTensor c F ((chartAt FourSpace d).symm z))

theorem twoFormChartFamily_transition (c : M) (F : FourSpace → CovariantCoordinates 2)
    (d e : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target)
    (hx : (chartAt FourSpace d).symm z ∈ (chartAt FourSpace e).source) :
    twoFormChartFamily c F d z = frameTensor (chartTransitionMatrix d e z)
      (twoFormChartFamily c F e (chartTransition d e z)) := by
  have he : (chartAt FourSpace e).symm (chartTransition d e z) =
      (chartAt FourSpace d).symm z := (chartAt FourSpace e).left_inv hx
  unfold twoFormChartFamily
  rw [he, ← frameTensor_mul, chartInverseMatrix_transition d e z hz hx]

theorem twoFormChartFamily_eq (g : SmoothMetric M) (c : M) (F : FourSpace → CovariantCoordinates 2)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target)
    (hx : (chartAt FourSpace d).symm z ∈ (chartAt FourSpace c).source) :
    twoFormChartFamily c F d z =
      frameTensor (chartTransitionMatrix d c z) (F (chartTransition d c z)) := by
  unfold twoFormChartFamily twoFormChartTensor
  rw [ite_eq_left hx, ← frameTensor_mul]
  change frameTensor ((chartInverseMatrix c (chartTransition d c z))⁻¹ * chartInverseMatrix d z)
    (F (chartTransition d c z)) = _
  have hi : (chartInverseMatrix c (chartTransition d c z))⁻¹ *
      chartInverseMatrix c (chartTransition d c z) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (chartInverseMatrix_det_ne_zero g c _ ((chartAt FourSpace c).map_source hx)))
  rw [← chartInverseMatrix_transition d c z hz hx, ← Matrix.mul_assoc, hi,
    Matrix.one_mul]

omit [IsManifold I4 ∞ M] in
theorem twoFormChartFamily_skew (c : M) (F : FourSpace → CovariantCoordinates 2)
    (hF : ∀ z i j, F z ![j,i] = -F z ![i,j])
    (d : M) (z : FourSpace) (i j : Fin 4) :
    twoFormChartFamily c F d z ![j,i] = -twoFormChartFamily c F d z ![i,j] := by
  apply twoTensor_frame_skew
  intro a b
  unfold twoFormChartTensor
  split_ifs
  · exact twoTensor_frame_skew _ _ (hF _) a b
  · simp

omit [IsManifold I4 ∞ M] in
theorem twoFormChartTensor_zero_off (c : M) (F : FourSpace → CovariantCoordinates 2)
    {K : Set FourSpace} (hF : tsupport F ⊆ K) (x : M)
    (hx : x ∉ (chartAt FourSpace c).symm '' K) : twoFormChartTensor c F x = 0 := by
  unfold twoFormChartTensor
  split_ifs with hxs
  · have hz : chartAt FourSpace c x ∉ K := by
      intro hK
      exact hx ⟨chartAt FourSpace c x, hK, (chartAt FourSpace c).left_inv hxs⟩
    have hzero : F (chartAt FourSpace c x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (hF h))
    rw [hzero, frameTensor_zero_two]
  · rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! In Ric = 3g the local graded traces of the Weitzenböck potential
have vanishing degree-zero/degree-one terms and the required curvature norm
in degree two. No heat-kernel or characteristic-number assertion is made. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_twoFormCurvatureMatrix_trace (hRic : RicciThree g) (e : FrameBundle g) :
    (twoFormCurvatureMatrix (twoFormMetricCurvatureTensor g e)).trace = 6 := by
  have hl (i j k l : Fin 4) : twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have ht := twoFormCurvatureMatrix_trace_contraction (twoFormMetricCurvatureTensor g e)
    (twoFormMetricCurvatureTensor_skew g e) hl
  have hr (j : Fin 4) : (∑ i : Fin 4, twoFormMetricCurvatureTensor g e ![i,j,j,i]) = 3 := by
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    simpa [AlgebraicCurvature.ricci] using
      frame_algebraic_ricciThree e.frame hRic j j
  rw [Finset.sum_comm] at ht
  simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at ht
  norm_num at ht
  linarith only [ht]

theorem actual_twoFormPotential_trace (hRic : RicciThree g) (e : FrameBundle g) :
    (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace = 24 := by
  rw [twoFormPotentialMatrix_trace, actual_twoFormCurvatureMatrix_trace hRic]
  norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported chart tensor, transported into the centered
tangent coordinates and then into any other chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def oneFormChartTensor (c : M) (F : FourSpace → CovariantCoordinates 1) (x : M) :
    CovariantCoordinates 1 := by
  classical
  exact if x ∈ (chartAt FourSpace c).source then
    frameTensor (chartInverseMatrix c (chartAt FourSpace c x))⁻¹ (F (chartAt FourSpace c x))
  else 0

def oneFormChartFamily (c : M) (F : FourSpace → CovariantCoordinates 1)
    (d : M) (z : FourSpace) : CovariantCoordinates 1 :=
  frameTensor (chartInverseMatrix d z) (oneFormChartTensor c F ((chartAt FourSpace d).symm z))

theorem oneFormChartFamily_eq (g : SmoothMetric M) (c : M) (F : FourSpace → CovariantCoordinates 1)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target)
    (hx : (chartAt FourSpace d).symm z ∈ (chartAt FourSpace c).source) :
    oneFormChartFamily c F d z =
      frameTensor (chartTransitionMatrix d c z) (F (chartTransition d c z)) := by
  unfold oneFormChartFamily oneFormChartTensor
  rw [ite_eq_left hx, ← frameTensor_mul]
  change frameTensor ((chartInverseMatrix c (chartTransition d c z))⁻¹ * chartInverseMatrix d z)
    (F (chartTransition d c z)) = _
  have hi : (chartInverseMatrix c (chartTransition d c z))⁻¹ *
      chartInverseMatrix c (chartTransition d c z) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (chartInverseMatrix_det_ne_zero g c _ ((chartAt FourSpace c).map_source hx)))
  rw [← chartInverseMatrix_transition d c z hz hx, ← Matrix.mul_assoc, hi,
    Matrix.one_mul]

omit [IsManifold I4 ∞ M] in
theorem oneFormChartTensor_zero_off (c : M) (F : FourSpace → CovariantCoordinates 1)
    {K : Set FourSpace} (hF : tsupport F ⊆ K) (x : M)
    (hx : x ∉ (chartAt FourSpace c).symm '' K) : oneFormChartTensor c F x = 0 := by
  unfold oneFormChartTensor
  split_ifs with hxs
  · have hz : chartAt FourSpace c x ∉ K := by
      intro hK
      exact hx ⟨chartAt FourSpace c x, hK, (chartAt FourSpace c).left_inv hxs⟩
    have hzero : F (chartAt FourSpace c x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (hF h))
    rw [hzero, frameTensor_zero_one]
  · rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported alternating chart tensors give actual global smooth
two-forms. The support hypothesis is used only across the chart boundary. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormChartFamily_self (g : SmoothMetric M) (c : M)
    (F : FourSpace → CovariantCoordinates 2) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : twoFormChartFamily c F c z = F z := by
  unfold twoFormChartFamily twoFormChartTensor
  rw [ite_eq_left ((chartAt FourSpace c).map_target hz), (chartAt FourSpace c).right_inv hz,
    ← frameTensor_mul, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (chartInverseMatrix_det_ne_zero g c z hz)), frameTensor_one]

theorem twoFormChartFamily_smooth [T2Space M] (g : SmoothMetric M)
    (c : M) (F : FourSpace → CovariantCoordinates 2)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target)
    (a : Fin 2 → Fin 4) : ContDiffAt ℝ ∞ (fun w => twoFormChartFamily c F d w a) z := by
  classical
  by_cases hx : (chartAt FourSpace d).symm z ∈ (chartAt FourSpace c).source
  · have h : ContDiffAt ℝ ∞ (fun w => frameTensor (chartTransitionMatrix d c w)
        (F (chartTransition d c w)) a) z := by
      change ContDiffAt ℝ ∞ (fun w => ∑ b, (∏ k, chartTransitionMatrix d c w (b k) (a k)) *
        F (chartTransition d c w) b) z
      apply ContDiffAt.sum
      intro b _
      have hb : ContDiffAt ℝ ∞ (fun w => F w b) (chartTransition d c z) :=
        ((contDiffOn_pi.mp hF) b).contDiffAt
          ((chartAt FourSpace c).open_target.mem_nhds ((chartAt FourSpace c).map_source hx))
      exact (contDiffAt_prod (fun k _ =>
        chartTransitionMatrix_contDiffAt d c z hz hx (b k) (a k))).mul
        (hb.comp z (chartTransition_contDiffAt d c z hz hx))
    apply h.congr_of_eventuallyEq
    filter_upwards [chart_overlap_eventually d c z hz hx] with w hw
    exact congrFun (twoFormChartFamily_eq g c F d w hw.1 hw.2) a
  · let L := (chartAt FourSpace c).symm '' K
    have hL : IsCompact L :=
      hK.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hKt)
    have hLs : L ⊆ (chartAt FourSpace c).source := by
      rintro _ ⟨w, hw, rfl⟩
      exact (chartAt FourSpace c).map_target (hKt hw)
    have hxL : (chartAt FourSpace d).symm z ∉ L := fun h => hx (hLs h)
    have he : ∀ᶠ w in 𝓝 z, (chartAt FourSpace d).symm w ∉ L :=
      ((chartAt FourSpace d).continuousAt_symm hz).eventually
        (hL.isClosed.isOpen_compl.mem_nhds hxL)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with w hw
    change frameTensor (chartInverseMatrix d w)
      (twoFormChartTensor c F ((chartAt FourSpace d).symm w)) a = 0
    rw [twoFormChartTensor_zero_off c F hFs _ hw, frameTensor_zero_two]
    rfl

def twoFormChartTest [T2Space M] (o : FrameOrientation g) (c : M)
    (F : FourSpace → CovariantCoordinates 2)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    (hFa : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K) : smoothTwoForms o :=
  ⟨twoFormFromCoordinates o (twoFormChartFamily c F),
    twoFormFromCoordinates_smooth _ (fun d z _ => twoFormChartFamily_skew c F hFa d z)
      (fun d e z hz hx => twoFormChartFamily_transition c F d e z hz hx)
      (twoFormChartFamily_smooth g c F hF hK hKt hFs)⟩

theorem twoFormChartTest_coordinates [T2Space M] (c : M)
    (F : FourSpace → CovariantCoordinates 2)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    (hFa : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCoordinates o (twoFormChartTest o c F hF hFa hK hKt hFs) c z = F z := by
  change twoFormCoordinates o (twoFormFromCoordinates o (twoFormChartFamily c F)) c z = _
  rw [twoFormFromCoordinates_coordinates _
    (fun d w _ => twoFormChartFamily_skew c F hFa d w)
    (fun d e w hw hx => twoFormChartFamily_transition c F d e w hw hx) c z hz,
    twoFormChartFamily_self g c F z hz]

theorem twoFormChartTest_zero_off [T2Space M] (c : M)
    (F : FourSpace → CovariantCoordinates 2)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    (hFa : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
    (x : M) (hx : x ∉ (chartAt FourSpace c).symm '' K) :
    (twoFormChartTest o c F hF hFa hK hKt hFs).val x = 0 := by
  change twoFormExtract (twoTensorMatrixLinear (frameTensor (o.frame x).matrix
    (frameTensor (chartInverseMatrix x (chartAt FourSpace x x))
      (twoFormChartTensor c F ((chartAt FourSpace x).symm (chartAt FourSpace x x)))))) = 0
  rw [(chartAt FourSpace x).left_inv (mem_chart_source FourSpace x),
    twoFormChartTensor_zero_off c F hFs x hx, frameTensor_zero_two, frameTensor_zero_two]
  change twoFormExtractLinear (twoTensorMatrixLinear 0) = 0
  rw [map_zero, map_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported alternating chart tensors give actual global smooth
two-forms. The support hypothesis is used only across the chart boundary. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem oneFormChartFamily_self (g : SmoothMetric M) (c : M)
    (F : FourSpace → CovariantCoordinates 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : oneFormChartFamily c F c z = F z := by
  unfold oneFormChartFamily oneFormChartTensor
  rw [ite_eq_left ((chartAt FourSpace c).map_target hz), (chartAt FourSpace c).right_inv hz,
    ← frameTensor_mul, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (chartInverseMatrix_det_ne_zero g c z hz)), frameTensor_one]

theorem oneFormChartFamily_smooth [T2Space M] (g : SmoothMetric M)
    (c : M) (F : FourSpace → CovariantCoordinates 1)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
    (d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace d).target)
    (a : Fin 1 → Fin 4) : ContDiffAt ℝ ∞ (fun w => oneFormChartFamily c F d w a) z := by
  classical
  by_cases hx : (chartAt FourSpace d).symm z ∈ (chartAt FourSpace c).source
  · have h : ContDiffAt ℝ ∞ (fun w => frameTensor (chartTransitionMatrix d c w)
        (F (chartTransition d c w)) a) z := by
      change ContDiffAt ℝ ∞ (fun w => ∑ b, (∏ k, chartTransitionMatrix d c w (b k) (a k)) *
        F (chartTransition d c w) b) z
      apply ContDiffAt.sum
      intro b _
      have hb : ContDiffAt ℝ ∞ (fun w => F w b) (chartTransition d c z) :=
        ((contDiffOn_pi.mp hF) b).contDiffAt
          ((chartAt FourSpace c).open_target.mem_nhds ((chartAt FourSpace c).map_source hx))
      exact (contDiffAt_prod (fun k _ =>
        chartTransitionMatrix_contDiffAt d c z hz hx (b k) (a k))).mul
        (hb.comp z (chartTransition_contDiffAt d c z hz hx))
    apply h.congr_of_eventuallyEq
    filter_upwards [chart_overlap_eventually d c z hz hx] with w hw
    exact congrFun (oneFormChartFamily_eq g c F d w hw.1 hw.2) a
  · let L := (chartAt FourSpace c).symm '' K
    have hL : IsCompact L :=
      hK.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hKt)
    have hLs : L ⊆ (chartAt FourSpace c).source := by
      rintro _ ⟨w, hw, rfl⟩
      exact (chartAt FourSpace c).map_target (hKt hw)
    have hxL : (chartAt FourSpace d).symm z ∉ L := fun h => hx (hLs h)
    have he : ∀ᶠ w in 𝓝 z, (chartAt FourSpace d).symm w ∉ L :=
      ((chartAt FourSpace d).continuousAt_symm hz).eventually
        (hL.isClosed.isOpen_compl.mem_nhds hxL)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with w hw
    change frameTensor (chartInverseMatrix d w)
      (oneFormChartTensor c F ((chartAt FourSpace d).symm w)) a = 0
    rw [oneFormChartTensor_zero_off c F hFs _ hw, frameTensor_zero_one]
    rfl

def oneFormChartTest [T2Space M] (g : SmoothMetric M) (c : M)
    (F : FourSpace → CovariantCoordinates 1)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) : smoothCovariantFields M 1 :=
  ⟨oneFormChartTensor c F, oneFormChartFamily_smooth g c F hF hK hKt hFs⟩

theorem oneFormChartTest_coordinates [T2Space M] (c : M)
    (F : FourSpace → CovariantCoordinates 1)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantFieldCoordinates (oneFormChartTest g c F hF hK hKt hFs).val c z = F z :=
  oneFormChartFamily_self g c F z hz

theorem oneFormChartTest_zero_off [T2Space M] (c : M)
    (F : FourSpace → CovariantCoordinates 1)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (x : M) (hx : x ∉ (chartAt FourSpace c).symm '' K) :
    (oneFormChartTest g c F hF hK hKt hFs).val x = 0 :=
  oneFormChartTensor_zero_off c F hFs x hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing of the intrinsic L2 norm detects the zero smooth one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormNormZeroProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem oneForm_norm_integral (u : smoothCovariantFields M 1) :
    (∫ x, covariantFieldNormSq g u.val x ∂normalizedVolume g) =
      ∫ e, ∑ j, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o := by
  have hi := (u.property.continuous_normSq (g := g)).integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [covariantFieldNormSq_eq_frame u.val e, oneForm_squareNorm]

theorem oneForm_eq_zero_of_norm_integral (u : smoothCovariantFields M 1)
    (hu : (∫ x, covariantFieldNormSq g u.val x ∂normalizedVolume g) = 0) : u = 0 := by
  let _ := normalizedVolume_isOpenPosMeasure g
  have hc := u.property.continuous_normSq (g := g)
  have hi := hc.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  have hn (x : M) : 0 ≤ covariantFieldNormSq g u.val x := by
    unfold covariantFieldNormSq
    rw [oneForm_squareNorm]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp hu
  have he : covariantFieldNormSq g u.val = 0 := Measure.eq_of_ae_eq hae hc continuous_const
  apply Subtype.ext
  funext x
  change u.val x = 0
  let E := (frameAt g x).frame.matrix
  have hb : (frameAt g x).base = x := rfl
  have hs : frameTensorSquareNorm (frameTensor E (u.val x)) = 0 := by
    have h := congrFun he x
    simpa only [covariantFieldNormSq, covariantFieldFramed_eq, hb, Pi.zero_apply] using h
  have hzero : frameTensor E (u.val x) = 0 := by
    unfold frameTensorSquareNorm frameTensorPairing at hs
    funext a
    change frameTensor E (u.val x) a = 0
    have hle := Finset.single_le_sum
      (fun b _ => mul_self_nonneg (frameTensor E (u.val x) b)) (Finset.mem_univ a)
    rw [hs] at hle
    nlinarith only [hle]
  have hback := congrArg (frameTensor E⁻¹) hzero
  rw [← frameTensor_mul, Matrix.mul_nonsing_inv E
    (isUnit_iff_ne_zero.mpr (frameAt g x).frame.det_ne_zero), frameTensor_one] at hback
  apply hback.trans
  funext a
  simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The infinitesimal orthogonal action on two-forms and its ordinary
and Hodge-signed quadratic traces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormInfinitesimalMatrix (a : TwoFormFour) : TwoFormMatrix :=
  !![0, a 3, a 4, -a 1, -a 2, 0;
     -a 3, 0, a 5, a 0, 0, -a 2;
     -a 4, -a 5, 0, 0, a 0, a 1;
     a 1, -a 0, 0, 0, a 5, -a 4;
     a 2, 0, -a 0, -a 5, 0, a 3;
     0, a 2, -a 1, a 4, -a 3, 0]

theorem twoFormInfinitesimalMatrix_square_trace (a : TwoFormFour) :
    (twoFormInfinitesimalMatrix a * twoFormInfinitesimalMatrix a).trace = -4 * ‖a‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  simp [twoFormInfinitesimalMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

theorem twoFormMatrix_square_trace (a : TwoFormFour) :
    (twoFormMatrix a * twoFormMatrix a).trace = -2 * ‖a‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  simp [twoFormMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

theorem twoFormInfinitesimalMatrix_euler_trace (a : TwoFormFour) :
    (twoFormInfinitesimalMatrix a * twoFormInfinitesimalMatrix a).trace -
      2 * (twoFormMatrix a * twoFormMatrix a).trace = 0 := by
  rw [twoFormInfinitesimalMatrix_square_trace, twoFormMatrix_square_trace]
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The derivative of the actual radial exponential at the zero vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- Raising the lowered initial vector cancels the metric. -/
theorem raise_frameMomentumMap (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      ((metricInChart g c (chartAt FourSpace c e.base))⁻¹)).comp (frameMomentumMap g c e) =
      (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap := by
  let G := metricInChart g c (chartAt FourSpace c e.base)
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.mpr
    (metricInChart_posDef g c _ ((chartAt FourSpace c).map_source he)).det_pos.ne'
  have hG : (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G⁻¹).comp
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G) =
      ContinuousLinearMap.id ℝ FourSpace := by
    change (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G⁻¹) *
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G) = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
  rw [frameMomentumMap, ← ContinuousLinearMap.comp_assoc]
  rw [hG, ContinuousLinearMap.id_comp]

theorem frameExponential_chart_strictDerivative_rescaled (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (F : KineticLocalFlow g c (chartAt FourSpace c e.base, 0))
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) (ht0 : 0 < t) :
    HasStrictFDerivAt (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t • (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap) 0 := by
  let P := frameMomentumMap g c e
  have hF : HasStrictFDerivAt (fun p : FourSpace => (F.map ((chartAt FourSpace c e.base, p), t)).1)
      (t • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        ((metricInChart g c (chartAt FourSpace c e.base))⁻¹)) (P 0) := by
    simpa only [map_zero] using F.zero_momentum_endpoint_strictDerivative g c _
      ((chartAt FourSpace c).map_source he) t ht
  have hh := hF.comp 0 P.hasStrictFDerivAt
  have hD : (t • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      ((metricInChart g c (chartAt FourSpace c e.base))⁻¹)).comp P =
      t • (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap := by
    rw [ContinuousLinearMap.smul_comp, raise_frameMomentumMap g c e he]
  rw [hD] at hh
  exact hh.congr_of_eventuallyEq (Filter.EventuallyEq.symm
    (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0))

/-- The actual radial exponential has at zero exactly the initial frame map
in any fixed chart. -/
theorem frameExponential_chart_strictDerivative_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    HasStrictFDerivAt (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v))
      ((chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  let t := F.time / 2
  have ht0 : 0 < t := half_pos F.time_pos
  have ht : t ∈ Ioo (-F.time) F.time := by dsimp [t]; constructor <;> linarith [F.time_pos]
  let Q := (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap
  have hd := frameExponential_chart_strictDerivative_rescaled g o c e he F t ht ht0
  have hs : HasStrictFDerivAt (fun v : FourSpace => t⁻¹ • v)
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).hasStrictFDerivAt
  have hd' : HasStrictFDerivAt (fun v : FourSpace =>
      chartAt FourSpace c (frameExponential g o e (t • v))) (t • Q) (t⁻¹ • (0 : FourSpace)) := by
    simpa only [smul_zero] using hd
  have h := hd'.comp 0 hs
  have hf : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  have hD : (t • Q).comp (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) = Q := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
  change HasStrictFDerivAt (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v))))
    ((t • Q).comp (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace)) 0 at h
  rw [hf, hD] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine local normal-coordinate chart for the constructed radial
exponential, obtained from its actual derivative at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem chartForwardOperator_center (x : M) :
    chartForwardOperator x x = ContinuousLinearMap.id ℝ FourSpace := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun K : TangentSpace I4 x →L[ℝ]
      TangentSpace I4 (extChartAt I4 x x) => K (show TangentSpace I4 x from v))
    (mfderiv_extChartAt_self (I := I4) (x := x))
  simp only [I4, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Technical measure reductions for the actual radial flow. Local image
identities on a compact slab give every time on that slab; a countable
exhaustion then gives the ambient measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- Preservation on the countable family of slabs determines preservation
of the whole radial measure, without a finiteness hypothesis. -/
theorem unitTangentRadial_preserves_of_slabs (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (t : ℝ)
    (hslabs : ∀ n, MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (exhaustingRadialSlab g n)) (μ.restrict (exhaustingRadialSlab g n))) :
    MeasurePreserving (unitTangentRadialFlow g o t) μ μ := by
  have hf := (unitTangentRadialFlow_continuous g o t).measurable
  refine ⟨hf, Measure.ext_of_iUnion_eq_univ (iUnion_exhaustingRadialSlab g) ?_⟩
  intro n
  change (Measure.map (unitTangentRadialFlow g o t) μ).restrict
      (radialSlab g (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) =
    μ.restrict (radialSlab g (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))
  rw [Measure.restrict_map hf (isClosed_radialSlab g _ _).measurableSet,
    unitTangentRadialFlow_preimage_slab]
  exact (hslabs n).map_eq

/-- Final technical reduction: uniform small-time local image identities
on each compact slab suffice for ambient radial preservation at every time. -/
theorem unitTangentRadial_preserves_of_slab_local_images
    (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g))
    (hlocal : ∀ n, ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε,
      ∀ p ∈ exhaustingRadialSlab g n,
        ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
          Measure.map (unitTangentRadialFlow g o t) (μ.restrict U) =
            μ.restrict (unitTangentRadialFlow g o t '' U)) (t : ℝ) :
    MeasurePreserving (unitTangentRadialFlow g o t) μ μ := by
  apply unitTangentRadial_preserves_of_slabs g o μ t
  intro n
  obtain ⟨ε, hε, hnear⟩ := hlocal n
  apply radialSlab_preserves_of_near_zero g o μ _ _ ε hε ?_ t
  intro s hs
  exact radialSlab_preserves_of_local_image g o μ _ _ s (hnear s hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Preservation of the canonical frame measure by the actual complete
parallel-frame flows. Local Hamiltonian preservation is glued on compact
radius slabs; the radial measure is then disintegrated on energy shells. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem unitTangentRadialFlow_measurePreserving (g : SmoothMetric M)
    (o : FrameOrientation g) (t : ℝ) :
    MeasurePreserving (unitTangentRadialFlow g o t)
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)) := by
  apply unitTangentRadial_preserves_of_slab_local_images g o _ ?_ t
  intro n
  have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨ε, hε, hlocal⟩ := radialSlab_uniform_hamiltonian_time g o
    (b := (n : ℝ) + 1) ha
  refine ⟨ε, hε, fun s hs p hp => ?_⟩
  obtain ⟨C, hpC, hεC⟩ := hlocal p hp
  have hsC : s ∈ Ioo (-C.flow.time) C.flow.time := by
    constructor <;> linarith [hs.1, hs.2]
  exact ⟨C.domain, C.open_domain, hpC, C.map_radialMeasure g o s hsC⟩

/-- The actual parallel-frame flow preserves base Riemannian volume times
orthonormal-fiber Haar probability, in every distinguished frame direction. -/
theorem parallelFrameFlowMap_measurePreserving (g : SmoothMetric M)
    (o : FrameOrientation g) (k : Fin 4) (t : ℝ) :
    MeasurePreserving (parallelFrameFlowMap g k t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) :=
  allFrameFlows_preserve_of_radial g o (unitTangentRadialFlow_measurePreserving g o) k t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Canonical parallel calculus: flow existence, differentiability and
measure preservation follow from the metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def canonicalParallelMetricData (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : ParallelMetricData g (canonicalFrameMeasure g o) :=
  actualParallelMetricData g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every finite derivative of the actual exponential exists near its zero
vector. The kinetic representation is evaluated at a sufficiently small
positive time and then rescaled, so no global smooth-flow input is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_chart_contDiffAt_zero_order (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (n : ℕ) :
    ContDiffAt ℝ n (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  obtain ⟨t, ht0, ht, hFt⟩ := F.exists_pos_contDiffAt_slice
    ((chartAt FourSpace c).map_source he) n
  have hinit : ContDiffAt ℝ n
      (fun v : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  have hF : ContDiffAt ℝ n (fun z => F.map (z, t))
      (chartAt FourSpace c e.base, frameMomentumMap g c e 0) := by
    simpa only [map_zero] using hFt
  have hlocal : ContDiffAt ℝ n
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v))) 0 := by
    have hcompose : ContDiffAt ℝ n (fun v : FourSpace =>
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)) 0 :=
      ContDiffAt.comp (f := fun v : FourSpace =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v))
        (g := fun z : CotangentCoordinates => F.map (z, t)) 0 hF hinit
    exact hcompose.fst.congr_of_eventuallyEq
      (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0)
  have hscale : ContDiffAt ℝ n (fun v : FourSpace => t⁻¹ • v) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff.contDiffAt
  have hlocal' : ContDiffAt ℝ n
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t⁻¹ • (0 : FourSpace)) := by simpa only [smul_zero] using hlocal
  have h := hlocal'.comp 0 hscale
  have heq : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  change ContDiffAt ℝ n (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v)))) 0 at h
  rwa [heq] at h

theorem frameExponential_chart_smoothAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ContDiffAt ℝ ∞ (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 :=
  contDiffAt_infty.mpr (frameExponential_chart_contDiffAt_zero_order g o c e he)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual derivative of the complete radial flow, expressed in a
parallel orthonormal frame along its unit-speed geodesic. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def frameUnitRadialState {g : SmoothMetric M} (e : FrameBundle g) :
    PositiveRadius × UnitTangentBundle g := (⟨1, show (0 : ℝ) < 1 from zero_lt_one⟩, unitTangentOfFrame e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual exterior derivative along parallel frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormExterior_covariant (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (e : FrameBundle g) (i j k : Fin 4) :
    twoFormFramedCovariantDerivative o (smoothOneFormExterior (o := o) u).val e ![i,j,k] =
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e
        ![i,j,k] -
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e
        ![i,k,j] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hD : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
  have hsub := (hD.parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k]).sub
    (hD.parallel_derivative γ 0 i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![k,j])
  have heq : (fun t => covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![j,k] -
      covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![k,j]) =
      fun t => twoFormFramedValue o (smoothOneFormExterior (o := o) u).val (γ t) ![j,k] := by
    funext t
    exact (smoothOneFormExterior_framed u (γ t) j k).symm
  change HasDerivAt (fun t =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![j,k] -
      covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![k,j]) _ 0 at hsub
  rw [heq] at hsub
  have hd := (smoothOneFormExterior (o := o) u).property.framedValue_parallel_derivative
    γ 0 i (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k]
  have h := hd.unique hsub
  rw [hzero] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic L2 pairing of actual smooth one-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormPairingCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def smoothOneFormL2Pairing (u v : smoothCovariantFields M 1) : ℝ :=
  ∫ e, ∑ i, covariantFieldFramed g u.val e ![i] * covariantFieldFramed g v.val e ![i]
    ∂canonicalFrameMeasure g o

theorem smoothOneForm_pairing_integrable (u v : smoothCovariantFields M 1) :
    Integrable (fun e => ∑ i, covariantFieldFramed g u.val e ![i] *
      covariantFieldFramed g v.val e ![i]) (canonicalFrameMeasure g o) := by
  apply integrable_finsetSum
  intro i _
  exact (((continuous_apply _).comp u.property.continuous_framed).mul
    ((continuous_apply _).comp v.property.continuous_framed)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem smoothOneFormL2Pairing_comm (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) u v = smoothOneFormL2Pairing (o := o) v u := by
  unfold smoothOneFormL2Pairing
  apply integral_congr_ae
  filter_upwards [] with e
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem smoothOneFormL2Pairing_add (u v w : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (u + v) w =
      smoothOneFormL2Pairing (o := o) u w + smoothOneFormL2Pairing (o := o) v w := by
  unfold smoothOneFormL2Pairing
  simp only [Submodule.coe_add, covariantFieldFramed_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  exact integral_add (smoothOneForm_pairing_integrable u w) (smoothOneForm_pairing_integrable v w)

theorem smoothOneFormL2Pairing_smul (r : ℝ) (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (r • u) v = r * smoothOneFormL2Pairing (o := o) u v := by
  unfold smoothOneFormL2Pairing
  simp only [Submodule.coe_smul, covariantFieldFramed_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum, integral_const_mul]

theorem smoothOneFormL2Pairing_self (u : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) u u =
      ∫ x, covariantFieldNormSq g u.val x ∂normalizedVolume g := by
  rw [oneForm_norm_integral (o := o)]
  simp only [smoothOneFormL2Pairing, pow_two]

theorem smoothOneFormL2Pairing_nonneg (u : smoothCovariantFields M 1) :
    0 ≤ smoothOneFormL2Pairing (o := o) u u := by
  apply integral_nonneg
  intro e
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

theorem smoothOneFormL2Pairing_definite (u : smoothCovariantFields M 1)
    (hu : smoothOneFormL2Pairing (o := o) u u = 0) : u = 0 := by
  apply oneForm_eq_zero_of_norm_integral (g := g) u
  rwa [smoothOneFormL2Pairing_self] at hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 Hilbert completion of smooth covariant one-forms.
The completion uses the definite intrinsic metric pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

structure SmoothL2OneForm (_o : FrameOrientation g) where
  toSmooth : smoothCovariantFields M 1

def smoothL2OneFormEquiv (o : FrameOrientation g) :
    SmoothL2OneForm o ≃ smoothCovariantFields M 1 where
  toFun := SmoothL2OneForm.toSmooth
  invFun := SmoothL2OneForm.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields : CoeOut (SmoothL2OneForm o) (smoothCovariantFields M 1) := ⟨SmoothL2OneForm.toSmooth⟩

instance instZeroSmoothL2OneForm : Zero (SmoothL2OneForm o) := ⟨⟨0⟩⟩
instance instAddSmoothL2OneForm : Add (SmoothL2OneForm o) := ⟨fun u v => ⟨u.toSmooth + v.toSmooth⟩⟩
instance instNegSmoothL2OneForm : Neg (SmoothL2OneForm o) := ⟨fun u => ⟨-u.toSmooth⟩⟩
instance instSubSmoothL2OneForm : Sub (SmoothL2OneForm o) := ⟨fun u v => ⟨u.toSmooth - v.toSmooth⟩⟩
instance instSMulNatSmoothL2OneForm : SMul ℕ (SmoothL2OneForm o) := ⟨fun r u => ⟨r • u.toSmooth⟩⟩
instance instSMulIntSmoothL2OneForm : SMul ℤ (SmoothL2OneForm o) := ⟨fun r u => ⟨r • u.toSmooth⟩⟩
instance instSMulRealSmoothL2OneForm : SMul ℝ (SmoothL2OneForm o) := ⟨fun r u => ⟨r • u.toSmooth⟩⟩

instance instAddCommGroupSmoothL2OneForm : AddCommGroup (SmoothL2OneForm o) :=
  Function.Injective.addCommGroup SmoothL2OneForm.toSmooth (smoothL2OneFormEquiv o).injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def smoothL2OneFormAddHom : SmoothL2OneForm o →+ smoothCovariantFields M 1 where
  toFun := SmoothL2OneForm.toSmooth
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModuleRealSmoothL2OneForm : Module ℝ (SmoothL2OneForm o) :=
  Function.Injective.module ℝ smoothL2OneFormAddHom (smoothL2OneFormEquiv o).injective
    (fun _ _ => rfl)

instance smoothOneFormInnerCore : InnerProductSpace.Core ℝ (SmoothL2OneForm o) where
  inner u v := smoothOneFormL2Pairing (o := o) u v
  conj_inner_symm u v := by
    simpa only [conj_trivial] using smoothOneFormL2Pairing_comm (o := o) v u
  re_inner_nonneg u := smoothOneFormL2Pairing_nonneg u.toSmooth
  add_left u v w := smoothOneFormL2Pairing_add u.toSmooth v.toSmooth w.toSmooth
  smul_left u v r := by
    change smoothOneFormL2Pairing (o := o) (r • (u : smoothCovariantFields M 1)) v =
      r * smoothOneFormL2Pairing (o := o) u v
    exact smoothOneFormL2Pairing_smul r u.toSmooth v.toSmooth
  definite u hu := by
    apply (smoothL2OneFormEquiv o).injective
    exact smoothOneFormL2Pairing_definite u.toSmooth hu

instance smoothOneFormNormedAddCommGroup : NormedAddCommGroup (SmoothL2OneForm o) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance smoothOneFormInnerProductSpace : InnerProductSpace ℝ (SmoothL2OneForm o) :=
  InnerProductSpace.ofCore _

def OneFormL2 (o : FrameOrientation g) := UniformSpace.Completion (SmoothL2OneForm o)
  deriving NormedAddCommGroup, NormedSpace ℝ, InnerProductSpace ℝ, CompleteSpace

def smoothOneFormToL2 : SmoothL2OneForm o →ₗᵢ[ℝ] OneFormL2 o :=
  UniformSpace.Completion.toComplₗᵢ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth functions as degree-zero covariant fields and their actual
one-form differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem smoothScalarCovariantField_coordinates (f : SmoothScalar (M := M)) (c : M) :
    covariantFieldCoordinates (smoothScalarCovariantField f).val c = scalarCoordinates f.val c := by
  funext z a
  exact frameTensor_zero _ _ a

theorem smoothScalarDifferential_framed (f : SmoothScalar (M := M))
    (e : FrameBundle g) (i : Fin 4) :
    covariantFieldFramed g (smoothScalarDifferential g f).val e ![i] =
      scalarGradient g f.val e i := by
  rw [covariantFieldFramed_eq]
  change frameTensor e.frame.matrix (covariantDerivative g e.base
    (covariantFieldCoordinates (smoothScalarCovariantField f).val e.base)
      (chartAt FourSpace e.base e.base)) ![i] = _
  rw [smoothScalarCovariantField_coordinates]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rough Green pairing is bounded by the L2 value norm.
This is the estimate needed to close the covariant derivative graph. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormBound_compactFrame : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def smoothTwoFormEuclideanValue (u : smoothTwoForms o) : C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun e => WithLp.toLp 2 (twoFormFramedValue o u.val e),
    (PiLp.continuous_toLp 2 _).comp u.property.continuous_framedValue⟩

def smoothTwoFormTensorValueL2 (u : smoothTwoForms o) : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u)

theorem continuousTwoTensor_inner_toLp (F G : C(FrameBundle g, TwoTensorEuclidean)) :
    inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F)
      (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ G) =
        ∫ e, inner ℝ (F e) (G e) ∂canonicalFrameMeasure g o := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) G] with e hF hG
  rw [hF, hG]

theorem smoothTwoFormTensorValueL2_norm_sq (u : smoothTwoForms o) :
    ‖smoothTwoFormTensorValueL2 u‖ ^ 2 = 2 * smoothTwoFormL2Inner u u := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u))
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u)) = _
  rw [continuousTwoTensor_inner_toLp]
  have hp (e : FrameBundle g) :
      inner ℝ (smoothTwoFormEuclideanValue u e) (smoothTwoFormEuclideanValue u e) =
        2 * ‖u.val e.base‖ ^ 2 := by
    change frameTensorSquareNorm (twoFormFramedValue o u.val e) = _
    exact twoFormFramedValue_norm o u.val e
  simp_rw [hp]
  rw [integral_const_mul]
  congr 1
  rw [smoothTwoFormL2Inner_self]
  exact canonicalFrameMeasure_integral_base g o (fun x => ‖u.val x‖ ^ 2)
    (by simpa only [real_inner_self_eq_norm_sq] using smoothTwoForm_pairing_integrable u u)

theorem smoothTwoFormTensorValueL2_norm_le (u : SmoothL2TwoForm o) :
    ‖smoothTwoFormTensorValueL2 (u : smoothTwoForms o)‖ ≤ 2 * ‖u‖ := by
  have h := smoothTwoFormTensorValueL2_norm_sq (u : smoothTwoForms o)
  have hu : smoothTwoFormL2Inner (u : smoothTwoForms o) u = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [hu] at h
  nlinarith [norm_nonneg u, norm_nonneg (smoothTwoFormTensorValueL2 (u : smoothTwoForms o))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite tensor estimates for the chart localization of two-forms.
The bounds involve the actual value and covariant energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def tensorTransportWeight (n : ℕ) (P : Mat4) : ℝ :=
  ∑ a : Fin n → Fin 4, ∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)|

theorem tensorTransportWeight_continuous (n : ℕ) : Continuous (tensorTransportWeight n) := by
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (continuous_finsetProd _ (fun i _ =>
    (continuous_apply (a i)).comp (continuous_apply (b i)))).abs

theorem frameTensor_abs_le_weight {n : ℕ} (P : Mat4) (T : CovariantCoordinates n)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ a, |T a| ≤ C) (a : Fin n → Fin 4) :
    |frameTensor P T a| ≤ tensorTransportWeight n P * C := by
  calc
    _ ≤ ∑ b : Fin n → Fin 4, |(∏ i, P (b i) (a i)) * T b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)| * C := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hT b) (abs_nonneg _)
    _ = (∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)|) * C :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      unfold tensorTransportWeight
      exact Finset.single_le_sum (f := fun a : Fin n → Fin 4 =>
        ∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)|)
        (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (∏ i, P (b i) (a i))))
        (Finset.mem_univ a)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Realize the actual L2 completion inside square-integrable tensors on
the canonical frame bundle. The adjoint reconstructs L2 sections from
finite-regularity frame tensors without assuming they are smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_2 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def smoothTwoFormTensorLinear : SmoothL2TwoForm o →ₗ[ℝ]
    Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) where
  toFun u := smoothTwoFormTensorValueL2 (u : smoothTwoForms o)
  map_add' u v := by
    have he : smoothTwoFormEuclideanValue ((u + v : SmoothL2TwoForm o) : smoothTwoForms o) =
        smoothTwoFormEuclideanValue (u : smoothTwoForms o) +
          smoothTwoFormEuclideanValue (v : smoothTwoForms o) := by
      ext e a
      simp only [ContinuousMap.add_apply, PiLp.add_apply]
      change twoFormFramedValue o ((u : smoothTwoForms o).val + (v : smoothTwoForms o).val) e a =
        twoFormFramedValue o (u : smoothTwoForms o).val e a +
          twoFormFramedValue o (v : smoothTwoForms o).val e a
      rw [twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormFrameValue_add]
      exact congrFun (twoFormTensorLinear.map_add _ _) a
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_add]
    rfl
  map_smul' r u := by
    have he : smoothTwoFormEuclideanValue ((r • u : SmoothL2TwoForm o) : smoothTwoForms o) =
        r • smoothTwoFormEuclideanValue (u : smoothTwoForms o) := by
      ext e a
      simp only [ContinuousMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
      change twoFormFramedValue o (r • (u : smoothTwoForms o).val) e a =
        r * twoFormFramedValue o (u : smoothTwoForms o).val e a
      rw [twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormFrameValue_smul]
      exact congrFun (twoFormTensorLinear.map_smul r _) a
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_smul]
    rfl

def smoothTwoFormTensorL2 : SmoothL2TwoForm o →L[ℝ]
    Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  (smoothTwoFormTensorLinear (o := o)).mkContinuous 2
    (fun u => smoothTwoFormTensorValueL2_norm_le u)

def twoFormTensorL2 : TwoFormL2 o →L[ℝ]
    Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  (smoothTwoFormTensorL2 (o := o)).fromCompletion

theorem twoFormTensorL2_smooth (u : SmoothL2TwoForm o) :
    twoFormTensorL2 (smoothTwoFormToL2 u) = smoothTwoFormTensorValueL2 (u : smoothTwoForms o) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem twoFormTensorL2_norm_sq (u : TwoFormL2 o) :
    ‖twoFormTensorL2 u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((twoFormTensorL2.continuous.norm).pow 2)
      (continuous_const.mul (continuous_norm.pow 2))) ?_
  intro v
  change ‖twoFormTensorL2 (smoothTwoFormToL2 v)‖ ^ 2 = 2 * ‖smoothTwoFormToL2 v‖ ^ 2
  rw [twoFormTensorL2_smooth]
  calc
    _ = 2 * smoothTwoFormL2Inner (v : smoothTwoForms o) v :=
      smoothTwoFormTensorValueL2_norm_sq (v : smoothTwoForms o)
    _ = _ := by
      change 2 * inner ℝ v v = 2 * ‖smoothTwoFormToL2 v‖ ^ 2
      rw [smoothTwoFormToL2.norm_map, real_inner_self_eq_norm_sq]

theorem twoFormTensorL2_inner (u v : TwoFormL2 o) :
    inner ℝ (twoFormTensorL2 u) (twoFormTensorL2 v) = 2 * inner ℝ u v := by
  have h := norm_add_sq_real (twoFormTensorL2 u) (twoFormTensorL2 v)
  rw [← map_add, twoFormTensorL2_norm_sq, twoFormTensorL2_norm_sq,
    twoFormTensorL2_norm_sq] at h
  nlinarith [norm_add_sq_real u v]

def twoFormFromTensorL2 : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) →L[ℝ] TwoFormL2 o :=
  (1 / 2 : ℝ) • twoFormTensorL2.adjoint

theorem twoFormFromTensorL2_pairing (F : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o))
    (u : TwoFormL2 o) :
    inner ℝ (twoFormFromTensorL2 F) u = (1 / 2 : ℝ) * inner ℝ F (twoFormTensorL2 u) := by
  simp only [twoFormFromTensorL2, smul_apply,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

theorem twoFormFromTensorL2_left_inverse (u : TwoFormL2 o) :
    twoFormFromTensorL2 (twoFormTensorL2 u) = u := by
  apply ext_inner_right ℝ
  intro v
  rw [twoFormFromTensorL2_pairing, twoFormTensorL2_inner]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual L2 sections obtained from continuous frame tensors, together
with their exact pairings against smooth two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_4 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def twoFormFromContinuousTensor : C(FrameBundle g, TwoTensorEuclidean) →L[ℝ] TwoFormL2 o :=
  (twoFormFromTensorL2 (o := o)).comp (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ)

theorem twoFormFromContinuousTensor_smooth (v : SmoothL2TwoForm o) :
    twoFormFromContinuousTensor (smoothTwoFormEuclideanValue (v : smoothTwoForms o)) =
      smoothTwoFormToL2 v := by
  change twoFormFromTensorL2 (smoothTwoFormTensorValueL2 (v : smoothTwoForms o)) = _
  rw [← twoFormTensorL2_smooth]
  exact twoFormFromTensorL2_left_inverse _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial differential and Gauss identities for the actual
exponential, expressed in the metric rather than in an output chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M]

theorem frameExponential_center_fderiv (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) :
    fderiv ℝ (fun w : FourSpace => chartAt FourSpace (frameExponential g o e v)
      (frameExponential g o e w)) v = mfderiv I4 I4 (frameExponential g o e) v := by
  let x := frameExponential g o e v
  have hc : MDifferentiableAt I4 I4 (chartAt FourSpace x) x :=
    (mdifferentiable_chart (I := I4) x).mdifferentiableAt (mem_chart_source FourSpace x)
  have he := (frameExponential_contMDiff g o e).mdifferentiable one_ne_zero v
  have h := mfderiv_comp v hc he
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun w => chartAt FourSpace x (frameExponential g o e w)) v =
    (chartForwardOperator x x).comp (mfderiv I4 I4 (frameExponential g o e) v) at h
  rw [chartForwardOperator_center] at h
  simpa only [ContinuousLinearMap.id_comp] using! h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Scalar differentiation in the normal vector, with the initial frame
held fixed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

def heatFamilyScalarPartial (f : HeatRadialFrameSpace → ℝ) (i : Fin 4)
    (z : HeatRadialFrameSpace) : ℝ := fderiv ℝ f z (coordinateVector i, 0)

theorem heatFamilyScalarPartial_contDiffAt (n : ℕ)
    (f : HeatRadialFrameSpace → ℝ) (z : HeatRadialFrameSpace)
    (hf : ContDiffAt ℝ (n + 1 : ℕ) f z) (i : Fin 4) :
    ContDiffAt ℝ n (heatFamilyScalarPartial f i) z :=
  (hf.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const

theorem heatFamilyScalarPartial_slice (f : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) (hf : DifferentiableAt ℝ f z) (i : Fin 4) :
    heatFamilyScalarPartial f i z = partialDeriv (fun x => f (x, z.2)) i z.1 := by
  have harg : HasFDerivAt (fun x : FourSpace => (x, z.2))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd : HasFDerivAt (fun x => f (x, z.2))
      ((fderiv ℝ f z).comp ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) z.1 := hf.hasFDerivAt.comp z.1 harg
  exact (congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hd.fderiv).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported four-times-differentiable scalar coefficients
can be lifted through the actual normal chart and extended by zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M]

def heatNormalScalarLift (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ C.target then ψ (C.symm x) else 0

theorem heatNormalScalarLift_on_target (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) {x : M} (hx : x ∈ C.target) :
    heatNormalScalarLift C ψ x = ψ (C.symm x) := by
  simp only [heatNormalScalarLift, ite_eq_left hx]

theorem heatNormalScalarLift_source (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) {x : FourSpace} (hx : x ∈ C.source) :
    heatNormalScalarLift C ψ (C x) = ψ x := by
  rw [heatNormalScalarLift_on_target C ψ (C.map_source hx), C.left_inv hx]

theorem heatNormalScalarLift_support (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) : support (heatNormalScalarLift C ψ) ⊆ C '' tsupport ψ := by
  classical
  intro x hx
  by_cases ht : x ∈ C.target
  · refine ⟨C.symm x, subset_closure ?_, C.right_inv ht⟩
    simpa only [mem_support, heatNormalScalarLift, ite_eq_left ht] using hx
  · exact False.elim (hx (by simp only [heatNormalScalarLift, ite_eq_right ht]))

variable [ChartedSpace FourSpace M]

theorem heatNormalScalarLift_regular [T2Space M]
    (C : OpenPartialHomeomorph FourSpace M) (ψ : FourSpace → ℝ)
    (hC : ContMDiffOn I4 I4 4 C.symm C.target)
    (hψ : ContDiff ℝ 4 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (heatNormalScalarLift C ψ) := by
  let K := C '' tsupport ψ
  have hK : IsCompact K := hc.image_of_continuousOn (C.continuousOn.mono hs)
  have hKt : K ⊆ C.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.map_source (hs hz)
  intro x
  by_cases hx : x ∈ C.target
  · have h := hψ.contMDiff.contMDiffAt.comp x
      (hC.contMDiffAt (C.open_target.mem_nhds hx))
    apply h.congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hx] with y hy
    exact heatNormalScalarLift_on_target C ψ hy
  · have hxK : x ∉ K := fun hxK => hx (hKt hxK)
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact notMem_support.mp (fun h => hy (heatNormalScalarLift_support C ψ h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Convert a two-form amplitude in the constructed parallel frame to
an actual alternating coordinate tensor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalCoordinateTensor {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → TwoFormFour) (x : FourSpace) : CovariantCoordinates 2 :=
  frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))

theorem heatNormalFrame_matrix_nondegenerate {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    {x : FourSpace} (hx : x ∈ ball 0 D.radius) : (D.point x).2.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det (D.orthonormal x hx)
  simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
  norm_num at h

theorem heatNormalCoordinateTensor_regular {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → TwoFormFour) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x) (ha : ContDiffAt ℝ 2 a x)
    (v : Fin 2 → Fin 4) : ContDiffAt ℝ 2 (fun y => heatNormalCoordinateTensor D a y v) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hEi (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2⁻¹ i j) x :=
    heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) x hE
      (heatNormalFrame_matrix_nondegenerate D hx) i j
  have hT : ContDiffAt ℝ 2 (fun y => twoFormTensor (a y)) x :=
    twoFormTensorLinear.toContinuousLinearMap.contDiff.comp_contDiffAt x ha
  change ContDiffAt ℝ 2 (fun y => ∑ b, (∏ k, (D.point y).2⁻¹ (b k) (v k)) *
    twoFormTensor (a y) b) x
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod (fun k _ => hEi (b k) (v k))).mul
    ((ContinuousLinearMap.proj b : CovariantCoordinates 2 →L[ℝ] ℝ).contDiff.comp_contDiffAt x hT)

theorem heatNormalCoordinateTensor_support {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → TwoFormFour) :
    tsupport (heatNormalCoordinateTensor D a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have ha : a x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  simp only [heatNormalCoordinateTensor, ha, show twoFormTensor 0 = 0 from map_zero twoFormTensorLinear]
  funext v
  simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact cutoff inside a genuine normal chart, equal to one on its
inner quarter ball and with four derivatives after lifting to the manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def heatNormalChartBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : FourSpace) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal-coordinate tensors define actual continuous tensors
on the intrinsic frame bundle by extension by zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalFrameTensorLift (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 2)
    (e : FrameBundle g) : CovariantCoordinates 2 := by
  classical
  exact if e.base ∈ C.target then
    frameTensor (frameChartMatrix g c e) (T (C.symm e.base)) else 0

theorem heatNormalFrameTensorLift_support (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 2)
    {e : FrameBundle g} (he : heatNormalFrameTensorLift g c C T e ≠ 0) :
    e.base ∈ C '' tsupport T := by
  classical
  by_cases hx : e.base ∈ C.target
  · refine ⟨C.symm e.base, subset_closure ?_, C.right_inv hx⟩
    intro hzero
    apply he
    rw [heatNormalFrameTensorLift, ite_eq_left hx, hzero]
    funext a
    simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · exact False.elim (he (by simp only [heatNormalFrameTensorLift, ite_eq_right hx]))

variable [T2Space M]

theorem heatNormalFrameTensorLift_continuous (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 2)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hT : ContinuousOn T C.source) (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatNormalFrameTensorLift g c C T) := by
  classical
  have hK : IsCompact (C '' tsupport T) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro e
  by_cases he : e.base ∈ C.target
  · have hinv : ContinuousAt (fun f : FrameBundle g => C.symm f.base) e :=
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)).comp
        (continuous_frameBase g).continuousAt
    have hval : ContinuousAt (fun f : FrameBundle g => T (C.symm f.base)) e :=
      (hT.continuousAt (C.open_source.mem_nhds (C.map_target he))).comp
        (f := fun f : FrameBundle g => C.symm f.base) hinv
    have hframe : ContinuousAt (fun f : FrameBundle g =>
        frameTensor (frameChartMatrix g c f) (T (C.symm f.base))) e := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        frameChartMatrix_continuousAt g c e (hCt he) (b k) (a k))).mul
          ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually (C.open_target.mem_nhds he)
    filter_upwards [hnear] with f hf
    change (if f.base ∈ C.target then _ else _) = _
    exact ite_eq_left hf
  · have hxK : e.base ∉ C '' tsupport T := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 2))).congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually
      (hK.isClosed.isOpen_compl.mem_nhds hxK)
    filter_upwards [hnear] with f hf
    exact not_ne_iff.mp (fun h => hf (heatNormalFrameTensorLift_support g c C T h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal-coordinate tensors define actual continuous tensors
on the intrinsic frame bundle by extension by zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalOneFrameLift (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 1)
    (e : FrameBundle g) : CovariantCoordinates 1 := by
  classical
  exact if e.base ∈ C.target then
    frameTensor (frameChartMatrix g c e) (T (C.symm e.base)) else 0

theorem heatNormalOneFrameLift_support (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 1)
    {e : FrameBundle g} (he : heatNormalOneFrameLift g c C T e ≠ 0) :
    e.base ∈ C '' tsupport T := by
  classical
  by_cases hx : e.base ∈ C.target
  · refine ⟨C.symm e.base, subset_closure ?_, C.right_inv hx⟩
    intro hzero
    apply he
    rw [heatNormalOneFrameLift, ite_eq_left hx, hzero]
    funext a
    simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · exact False.elim (he (by simp only [heatNormalOneFrameLift, ite_eq_right hx]))

variable [T2Space M]

theorem heatNormalOneFrameLift_continuous (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 1)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hT : ContinuousOn T C.source) (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatNormalOneFrameLift g c C T) := by
  classical
  have hK : IsCompact (C '' tsupport T) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro e
  by_cases he : e.base ∈ C.target
  · have hinv : ContinuousAt (fun f : FrameBundle g => C.symm f.base) e :=
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)).comp
        (continuous_frameBase g).continuousAt
    have hval : ContinuousAt (fun f : FrameBundle g => T (C.symm f.base)) e :=
      (hT.continuousAt (C.open_source.mem_nhds (C.map_target he))).comp
        (f := fun f : FrameBundle g => C.symm f.base) hinv
    have hframe : ContinuousAt (fun f : FrameBundle g =>
        frameTensor (frameChartMatrix g c f) (T (C.symm f.base))) e := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        frameChartMatrix_continuousAt g c e (hCt he) (b k) (a k))).mul
          ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually (C.open_target.mem_nhds he)
    filter_upwards [hnear] with f hf
    change (if f.base ∈ C.target then _ else _) = _
    exact ite_eq_left hf
  · have hxK : e.base ∉ C '' tsupport T := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 1))).congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually
      (hK.isClosed.isOpen_compl.mem_nhds hxK)
    filter_upwards [hnear] with f hf
    exact not_ne_iff.mp (fun h => hf (heatNormalOneFrameLift_support g c C T h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Zero extension through a normal chart needs only continuity on the
source when the amplitude has compact support there. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem heatNormalScalarLift_continuous (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) (hψ : ContinuousOn ψ C.source)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    Continuous (heatNormalScalarLift C ψ) := by
  classical
  have hK : IsCompact (C '' tsupport ψ) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ C.target
  · have hi := C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hx)
    have hp := hψ.continuousAt (C.open_source.mem_nhds (C.map_target hx))
    apply (hp.comp hi).congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hx] with y hy
    exact heatNormalScalarLift_on_target C ψ hy
  · have hxK : x ∉ C '' tsupport ψ := by
      rintro ⟨z, hz, hzx⟩
      exact hx (hzx ▸ C.map_source (hs hz))
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact Function.notMem_support.mp (fun h => hy (heatNormalScalarLift_support C ψ h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact finite-regularity normal-frame amplitude determines an
actual element of the global two-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalCoordinateTensor_continuousOn (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hP : ContDiffOn ℝ 2 D.point C.source)
    (hD : C.source ⊆ ball 0 D.radius) (a : FourSpace → TwoFormFour)
    (ha : ContDiff ℝ 2 a) : ContinuousOn (heatNormalCoordinateTensor D a) C.source := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro v
  exact (heatNormalCoordinateTensor_regular D a x (hD hx)
    (hP.contDiffAt (C.open_source.mem_nhds hx)) ha.contDiffAt v).continuousAt

def heatNormalAmplitudeTensor (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f),
    (PiLp.continuous_toLp 2 _).comp (heatNormalFrameTensorLift_continuous g c C _ hCt
      (heatNormalCoordinateTensor_continuousOn D C hP hD a ha)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCoordinateTensor_support D a))
      ((heatNormalCoordinateTensor_support D a).trans hs))⟩

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalAmplitudeL2 (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : TwoFormL2 o :=
  twoFormFromContinuousTensor (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Convert a one-form amplitude in the constructed parallel frame to
an actual coordinate covector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalOneCoordinates {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → FourSpace) (x : FourSpace) : CovariantCoordinates 1 :=
  frameTensor (D.point x).2⁻¹ (fun v => a x (v 0))

theorem heatNormalOneCoordinates_regular {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → FourSpace) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x) (ha : ContDiffAt ℝ 2 a x)
    (v : Fin 1 → Fin 4) : ContDiffAt ℝ 2 (fun y => heatNormalOneCoordinates D a y v) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hEi (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2⁻¹ i j) x :=
    heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) x hE
      (heatNormalFrame_matrix_nondegenerate D hx) i j
  change ContDiffAt ℝ 2 (fun y => ∑ b : Fin 1 → Fin 4, (∏ k, (D.point y).2⁻¹ (b k) (v k)) *
    a y (b 0)) x
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod (fun k _ => hEi (b k) (v k))).mul
    ((EuclideanSpace.proj (b 0) : FourSpace →L[ℝ] ℝ).contDiff.comp_contDiffAt x ha)

theorem heatNormalOneCoordinates_support {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → FourSpace) :
    tsupport (heatNormalOneCoordinates D a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have ha : a x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  simp only [heatNormalOneCoordinates, ha, PiLp.zero_apply]
  funext v
  simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-dimensional action of the actual normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatTwoFormSkewAction_swap (b a : TwoFormFour) :
    twoFormSkewAction b a = -twoFormSkewAction a b := by
  ext k
  fin_cases k <;> simp [twoFormSkewAction] <;> ring

def heatConnectionActionLinear (a : TwoFormFour) : Mat4 →ₗ[ℝ] TwoFormFour :=
  -(twoFormSkewActionLinear a).comp twoFormExtractLinear

theorem heatConnectionActionLinear_apply (a : TwoFormFour) (B : Mat4) :
    heatConnectionActionLinear a B = twoFormSkewAction (twoFormExtract B) a :=
  (heatTwoFormSkewAction_swap _ _).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.twoForm_connection_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ 11 (fun x => heatTwoFormConnection g c D.point i x k l) 0 := by
  have hB : ContDiffAt ℝ 11 (heatNormalFrameConnection g c D.point i) 0 :=
    contDiffAt_pi.mpr (fun j => contDiffAt_pi.mpr (D.connection_regular i j))
  let L := (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).toContinuousLinearMap
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hc := π.contDiff.contDiffAt.comp 0 (L.contDiff.contDiffAt.comp 0 hB)
  change ContDiffAt ℝ 11
    (fun x => heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)
      (heatNormalFrameConnection g c D.point i x) k) 0 at hc
  simpa only [heatConnectionActionLinear_apply, heatTwoFormConnection,
    heatTwoFormConnectionMatrix] using hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame curvature and potential are the intrinsic geometric
ones, evaluated on actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChartCurvature_eq (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    frameTensor (frameChartMatrix g c e) (curvatureCoordinates g c
      (chartAt FourSpace c e.base)) = twoFormMetricCurvatureTensor g e := by
  have hb := mem_chart_source FourSpace e.base
  have ht := curvatureCoordinates_transition g e.base c
    (chartAt FourSpace e.base e.base) ((chartAt FourSpace e.base).map_source hb)
    (by simpa only [(chartAt FourSpace e.base).left_inv hb] using he)
  have hz : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    change chartAt FourSpace c ((chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base e.base)) = _
    rw [(chartAt FourSpace e.base).left_inv hb]
  rw [hz] at ht
  rw [frameChartMatrix_eq, frameTensor_mul, ← ht]
  rfl

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.curvature_as_actual {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    heatNormalFrameCurvature g c D.point x =
      twoFormMetricCurvatureTensor g (D.frame x hx) := by
  have hsource : (D.frame x hx).base ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target (D.in_chart x hx)
  have h := frameChartCurvature_eq g c (D.frame x hx) hsource
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  rw [hm] at h
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hb] at h
  exact h

theorem HeatNormalFrameData.potential_as_actual {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    heatNormalPotential g c D.point x =
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g (D.frame x hx)) := by
  unfold heatNormalPotential
  rw [D.curvature_as_actual x hx]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous intrinsic Jacobian density for the actual exponential.
Its expression in any output chart is the metric density times the
absolute coordinate determinant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponentialGram_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponentialGram g o e) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hv (i : Fin 4) : Continuous (fun v : FourSpace =>
      tangentMap I4 I4 (frameExponential g o e) (⟨v, coordinateVector i⟩ : TangentBundle I4 FourSpace)) := by
    apply ((frameExponential_contMDiff g o e).continuous_tangentMap le_rfl).comp
    exact (tangentBundleModelSpaceHomeomorph I4).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hv i).inner_bundle (hv j)

theorem frameExponentialJacobian_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponentialJacobian g o e) :=
  Real.continuous_sqrt.comp ((frameExponentialGram_continuous g o e).matrix_det)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The distributional Poisson equation in metric chart measure.
Its coordinate density is derived from Riemannian volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function Filter
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem normalizedVolume_integral_chart (g : SmoothMetric M) (c : M)
    (f : M → ℝ) (hf : ∀ x, x ∉ (chartAt FourSpace c).source → f x = 0) :
    (∫ x, f x ∂normalizedVolume g) =
      (normalizedChartFactor g).toReal *
        ∫ z in (chartAt FourSpace c).target,
          chartVolumeDensity g c z * f ((chartAt FourSpace c).symm z) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf,
    normalizedVolume_restrict_chart, integral_smul_measure]
  have he : MeasurableEmbedding
      (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  rw [he.integral_map]
  have hd : Continuous (fun z : ChartTarget c => chartVolumeDensity g c z.val) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (chartVolumeDensity_contDiffAt g c z z.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hdm : Measurable (fun z : ChartTarget c =>
      ENNReal.ofReal (chartVolumeDensity g c z.val)) := by
    simpa only [Function.comp_def] using (ENNReal.continuous_ofReal.comp hd).measurable
  rw [integral_withDensity_eq_integral_toReal_smul
    hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (le_of_lt (chartVolumeDensity_pos g c _
    (Subtype.property _))), smul_eq_mul]
  congr 1
  exact integral_subtype_comap (chartAt FourSpace c).open_target.measurableSet
    (fun z => chartVolumeDensity g c z * f ((chartAt FourSpace c).symm z))

section Compact

variable [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
  [PreconnectedSpace M]

local instance scalarChartIntegral_probability_rced384_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem normalizedChartFactor_toReal_pos (g : SmoothMetric M) :
    0 < (normalizedChartFactor g).toReal := by
  have hV := actual_finitePositiveVolume g
  have hH : 0 < (euclideanHausdorffFactor : ℝ≥0∞) := by
    exact_mod_cast euclideanHausdorffFactor_pos
  apply ENNReal.toReal_pos
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hV.finite.ne)
      (mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' hH.ne')
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV.positive.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)

end Compact
end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels06
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Change of variables for a compact amplitude in an actual normal chart.
The normalization factor of the manifold measure remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem heatNormalScalarLift_integral_chart (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (J : FourSpace → FourSpace →L[ℝ] FourSpace)
    (hJ : ∀ x ∈ C.source, HasFDerivAt (fun y => chartAt FourSpace c (C y)) (J x) x)
    (ψ : FourSpace → ℝ) :
    (∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g) =
      (normalizedChartFactor g).toReal * ∫ x in C.source,
        |(J x).det| * chartVolumeDensity g c (chartAt FourSpace c (C x)) * ψ x := by
  classical
  let A := chartAt FourSpace c
  let T := C.trans A
  have hTs : T.source = C.source := by
    ext x
    change (x ∈ C.source ∧ C x ∈ A.source) ↔ x ∈ C.source
    exact ⟨And.left, fun hx => ⟨hx, hCt (C.map_source hx)⟩⟩
  let Q := fun z => chartVolumeDensity g c z * heatNormalScalarLift C ψ (A.symm z)
  let H := A.target.indicator Q
  have hHz (z : FourSpace) (hz : z ∉ T.target) : H z = 0 := by
    by_cases ha : z ∈ A.target
    · have hc : A.symm z ∉ C.target := fun hc => hz ⟨ha, hc⟩
      simp only [H, indicator_of_mem ha, Q, heatNormalScalarLift,
        ite_eq_right_iff, mul_eq_zero]
      exact Or.inr (by simp [hc])
    · exact indicator_of_notMem ha Q
  have hHT : (∫ z in A.target, Q z) = ∫ z in T.target, H z := by
    rw [← integral_indicator A.open_target.measurableSet]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hHz).symm
  have hder (x : FourSpace) (hx : x ∈ T.source) : HasFDerivAt T (J x) x :=
    hJ x (hTs ▸ hx)
  have hzero (y : M) (hy : y ∉ A.source) : heatNormalScalarLift C ψ y = 0 := by
    have hc : y ∉ C.target := fun hc => hy (hCt hc)
    simp [heatNormalScalarLift, hc]
  rw [normalizedVolume_integral_chart g c _ hzero]
  change (normalizedChartFactor g).toReal * (∫ z in A.target, Q z) = _
  rw [hHT, integral_target_eq_integral_abs_det_fderiv_smul volume hder, hTs]
  congr 1
  apply setIntegral_congr_fun C.open_source.measurableSet
  intro x hx
  have ha : T x ∈ A.target := A.map_source (hCt (C.map_source hx))
  have hi : A.symm (T x) = C x := A.left_inv (hCt (C.map_source hx))
  have hH : H (T x) = chartVolumeDensity g c (T x) * ψ x := by
    change A.target.indicator Q (T x) = _
    rw [indicator_of_mem ha]
    change chartVolumeDensity g c (T x) * heatNormalScalarLift C ψ (A.symm (T x)) = _
    rw [hi, heatNormalScalarLift_source C ψ hx]
  change |(J x).det| • H (T x) = _
  rw [hH, smul_eq_mul]
  change |(J x).det| * (chartVolumeDensity g c (chartAt FourSpace c (C x)) * ψ x) = _
  ring

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Extract a smooth real representative from all local integer Sobolev orders. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff _root_.Topology

noncomputable section

local notation "V" => FourSpace

def halfSmoothBump : ContDiffBump (0 : V) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual derivatives of a Gaussian with a smooth scalar amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators

noncomputable section

theorem fourHeatGaussian_smooth (t : ℝ) : ContDiff ℝ ∞ (fourHeatGaussian t) := by
  unfold fourHeatGaussian
  exact contDiff_const.mul ((contDiff_const.mul (contDiff_norm_sq ℝ)).exp)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact eikonal and radial transport terms of the local Gaussian
ansatz, computed from the actual coordinate derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatEikonalDefect (a : Matrix (Fin 4) (Fin 4) ℝ) (x : FourSpace) : ℝ :=
  (‖x‖ ^ 2 - ∑ i : Fin 4, ∑ j : Fin 4, a i j * x i * x j) / 4

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form H1 completion localizes into the closed Euclidean
first-jet graph. Each supported coordinate value is a compact operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff

noncomputable section

local instance instMeasurableSpaceFourSpace_1 : MeasurableSpace FourSpace := borel FourSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regular radial integral used to construct successive heat
coefficients, including at the origin. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Metric
open scoped ContDiff _root_.Topology Interval

noncomputable section

def fourHeatRadialAverageDerivative (m : ℕ) (f : FourSpace → ℝ)
    (x : FourSpace) (s : ℝ) : FourSpace →L[ℝ] ℝ :=
  s ^ (m + 1) • fderiv ℝ f (s • x)

theorem fourHeatRadialAverage_integrand_derivative (m : ℕ) (f : FourSpace → ℝ)
    (x : FourSpace) (s : ℝ) (hf : DifferentiableAt ℝ f (s • x)) :
    HasFDerivAt (fun y => s ^ m * f (s • y))
      (fourHeatRadialAverageDerivative m f x s) x := by
  have hd := (hf.hasFDerivAt.comp x
    (s • ContinuousLinearMap.id ℝ FourSpace).hasFDerivAt).const_mul (s ^ m)
  refine hd.congr_fderiv ?_
  · apply ContinuousLinearMap.ext
    intro v
    simp only [fourHeatRadialAverageDerivative, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul,
      smul_eq_mul, pow_succ]
    ring

theorem fourHeatRadialAverageDerivative_continuous (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : FourSpace × ℝ => fourHeatRadialAverageDerivative m f p.1 p.2) := by
  have hs : Continuous (fun p : FourSpace × ℝ => p.2 • p.1) :=
    continuous_snd.smul continuous_fst
  exact (continuous_snd.pow (m + 1)).smul ((hf.continuous_fderiv one_ne_zero).comp hs)

theorem fourHeatRadialAverageDerivative_bound (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (x : FourSpace) :
    ∃ C ≥ (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ ball x 1,
      ‖fourHeatRadialAverageDerivative m f y s‖ ≤ C := by
  have hD := (hf.continuous_fderiv one_ne_zero).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FourSpace) (‖x‖ + 1)).bddAbove_image
    hD.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs y hy
  have hys : s • y ∈ closedBall (0 : FourSpace) (‖x‖ + 1) := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc
      s * ‖y‖ ≤ ‖y‖ := mul_le_of_le_one_left (norm_nonneg _) hs.2
      _ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add y x
      _ ≤ ‖x‖ + 1 := by
        have hxy : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
        linarith
  have hpow : s ^ (m + 1) ≤ 1 := pow_le_one₀ hs.1 hs.2
  calc
    _ = s ^ (m + 1) * ‖fderiv ℝ f (s • y)‖ := by
      rw [fourHeatRadialAverageDerivative, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hs.1 _)]
    _ ≤ ‖fderiv ℝ f (s • y)‖ := mul_le_of_le_one_left (norm_nonneg _) hpow
    _ ≤ C := hC (mem_image_of_mem _ hys)
    _ ≤ max C 0 := le_max_left _ _

theorem fourHeatRadialAverage_hasFDerivAt (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (x : FourSpace) :
    HasFDerivAt (fourHeatRadialAverage m f)
      (∫ s : ℝ in 0..1, fourHeatRadialAverageDerivative m f x s) x := by
  obtain ⟨C, _, hC⟩ := fourHeatRadialAverageDerivative_bound m f hf x
  have hF (y : FourSpace) : Continuous (fun s : ℝ => s ^ m * f (s • y)) :=
    (continuous_id.pow m).mul (hf.continuous.comp (continuous_id.smul continuous_const))
  have hD (y : FourSpace) : Continuous (fourHeatRadialAverageDerivative m f y) :=
    (fourHeatRadialAverageDerivative_continuous m f hf).comp
      (continuous_const.prodMk continuous_id)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y s => s ^ m * f (s • y))
    (F' := fourHeatRadialAverageDerivative m f) (bound := fun _ => C)
    (ball_mem_nhds x one_pos)
    (Eventually.of_forall fun y => (hF y).aestronglyMeasurable)
    ((hF x).intervalIntegrable 0 1) (hD x).aestronglyMeasurable
    (Eventually.of_forall fun s hs => hC s (by
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩))
    (continuous_const.intervalIntegrable 0 1)
    (Eventually.of_forall fun s _ y _ =>
      fourHeatRadialAverage_integrand_derivative m f y s
        ((hf.differentiable one_ne_zero).differentiableAt))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lower-order coefficients contributed by the normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatConnectionFirst_radial (a : Mat4) (A : Fin 4 → HeatMat6)
    (x : FourSpace) (ha : ∀ j, (∑ i : Fin 4, a i j * x i) = x j)
    (hA : (∑ i : Fin 4, x i • A i) = 0) :
    (∑ i : Fin 4, x i • fourHeatConnectionFirst a A i) = 0 := by
  ext k l
  have hAl : (∑ j : Fin 4, x j * A j k l) = 0 := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      using congrArg (fun T : HeatMat6 => T k l) hA
  change (∑ i : Fin 4, x i * ((-2 : ℝ) * ∑ j : Fin 4, a i j * A j k l)) = 0
  calc
    _ = (-2 : ℝ) * ∑ j : Fin 4, (∑ i : Fin 4, a i j * x i) * A j k l := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp_rw [ha]; rw [hAl]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lower-order coefficients contributed by the normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOneConnectionFirst_contDiffAt (n : ℕ) (a : FourSpace → Mat4)
    (A : Fin 4 → FourSpace → Mat4) (x : FourSpace)
    (ha : ∀ i j, ContDiffAt ℝ n (fun y => a y i j) x)
    (hA : ∀ i k l, ContDiffAt ℝ n (fun y => A i y k l) x)
    (i : Fin 4) (k l : Fin 4) :
    ContDiffAt ℝ n (fun y => fourHeatOneConnectionFirst (a y) (fun j => A j y) i k l) x := by
  change ContDiffAt ℝ n (fun y => (-2 : ℝ) * ∑ j : Fin 4, a y i j * A j y k l) x
  exact contDiffAt_const.mul (ContDiffAt.sum (fun j _ => (ha i j).mul (hA j k l)))

theorem fourHeatOneConnectionZero_contDiffAt (n : ℕ) (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (A : Fin 4 → FourSpace → Mat4)
    (V : FourSpace → Mat4) (x : FourSpace)
    (ha : ∀ i j, ContDiffAt ℝ n (fun y => a y i j) x)
    (hb : ∀ i, ContDiffAt ℝ n (fun y => b y i) x)
    (hA : ∀ i k l, ContDiffAt ℝ (n + 1) (fun y => A i y k l) x)
    (hV : ∀ k l, ContDiffAt ℝ n (fun y => V y k l) x) (k l : Fin 4) :
    ContDiffAt ℝ n (fun y => fourHeatOneConnectionZero (a y) (b y) A (V y) y k l) x := by
  have hA0 (i : Fin 4) (k l : Fin 4) : ContDiffAt ℝ n (fun y => A i y k l) x :=
    (hA i k l).of_le (by exact_mod_cast Nat.le_succ n)
  have hD (i j : Fin 4) (k l : Fin 4) :
      ContDiffAt ℝ n (partialDeriv (fun y => A i y k l) j) x :=
    ((hA i k l).fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const
  change ContDiffAt ℝ n (fun y => V y k l +
    (∑ i : Fin 4, b y i * A i y k l) - ∑ i : Fin 4, ∑ j : Fin 4,
      a y i j * (partialDeriv (fun z => A i z k l) j y +
        ∑ q : Fin 4, A j y k q * A i y q l)) x
  apply ((hV k l).add (ContDiffAt.sum (fun i _ => (hb i).mul (hA0 i k l)))).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (ha i j).mul ((hD i j k l).add
    (ContDiffAt.sum (fun q _ => (hA0 j k q).mul (hA0 i q l))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Regularity of the radial transport solver, obtained by differentiating
its actual integral and reconstructing the derivative from four coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ContDiff BigOperators Interval

noncomputable section

theorem fourLinearForm_expansion (L : FourSpace →L[ℝ] ℝ) :
    L = ∑ i : Fin 4, L (coordinateVector i) • PiLp.proj 2 (fun _ : Fin 4 => ℝ) i := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ i : Fin 4, v i • coordinateVector i := by
    simpa only [WithLp.toLp_ofLp] using (sum_coordinateVector (WithLp.ofLp v)).symm
  have hLv := congrArg L hv
  rw [map_sum] at hLv
  simp only [map_smul, smul_eq_mul] at hLv
  rw [hLv]
  simp only [_root_.sum_apply, _root_.smul_apply, PiLp.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fourHeatRadialAverage_partial (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (x : FourSpace) (i : Fin 4) :
    partialDeriv (fourHeatRadialAverage m f) i x =
      fourHeatRadialAverage (m + 1) (partialDeriv f i) x := by
  have hD : Continuous (fourHeatRadialAverageDerivative m f x) :=
    (fourHeatRadialAverageDerivative_continuous m f hf).comp
      (continuous_const.prodMk continuous_id)
  rw [partialDeriv, (fourHeatRadialAverage_hasFDerivAt m f hf x).fderiv,
    ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 1)]
  simp only [fourHeatRadialAverageDerivative, _root_.smul_apply, smul_eq_mul,
    fourHeatRadialAverage, partialDeriv]

theorem fourHeatRadialAverage_fderiv (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (x : FourSpace) :
    fderiv ℝ (fourHeatRadialAverage m f) x =
      ∑ i : Fin 4, fourHeatRadialAverage (m + 1) (partialDeriv f i) x •
        PiLp.proj 2 (fun _ : Fin 4 => ℝ) i := by
  conv_lhs => rw [fourLinearForm_expansion (fderiv ℝ (fourHeatRadialAverage m f) x)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact fourHeatRadialAverage_partial m f hf x i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial transport with the center and initial frame as parameters.
Only the normal vector is scaled inside the transport integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Metric
open scoped ContDiff _root_.Topology Interval Matrix.Norms.Elementwise

noncomputable section

local instance heatFamilyRadialDualNormedGroup :
    NormedAddCommGroup (HeatRadialFrameSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance heatFamilyRadialDualNormedSpace :
    NormedSpace ℝ (HeatRadialFrameSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance heatFamilyRadialDualPseudoMetrizable :
    TopologicalSpace.PseudoMetrizableSpace (HeatRadialFrameSpace →L[ℝ] ℝ) :=
  PseudoEMetricSpace.pseudoMetrizableSpace

local instance heatFamilyRadialDualCountableEither :
    SecondCountableTopologyEither ℝ (HeatRadialFrameSpace →L[ℝ] ℝ) :=
  ⟨Or.inl inferInstance⟩

def heatFamilyScaleLinear (s : ℝ) : HeatRadialFrameSpace →L[ℝ] HeatRadialFrameSpace :=
  (s • ContinuousLinearMap.id ℝ FourSpace).prodMap
    (ContinuousLinearMap.id ℝ CoordinateFrameSpace)

theorem heatFamilyScaleLinear_apply (s : ℝ) (z : HeatRadialFrameSpace) :
    heatFamilyScaleLinear s z = (s • z.1, z.2) := rfl

theorem heatFamilyScaleLinear_continuous : Continuous heatFamilyScaleLinear := by
  exact Continuous.prod_mapL ℝ
    (continuous_id.smul (continuous_const (y := ContinuousLinearMap.id ℝ FourSpace)))
    (continuous_const (y := ContinuousLinearMap.id ℝ CoordinateFrameSpace))

def heatFamilyRadialAverage (m : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  ∫ s : ℝ in 0..1, s ^ m * f (heatFamilyScaleLinear s z)

theorem heatFamilyRadialAverage_continuous (m : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (hf : Continuous f) : Continuous (heatFamilyRadialAverage m f) := by
  have hc : Continuous (Function.uncurry (fun z : HeatRadialFrameSpace => fun s : ℝ =>
      s ^ m * f (heatFamilyScaleLinear s z))) :=
    (continuous_snd.pow m).mul (hf.comp
      ((heatFamilyScaleLinear_continuous.comp continuous_snd).clm_apply continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1

def heatFamilyRadialDerivative (m : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) (s : ℝ) : HeatRadialFrameSpace →L[ℝ] ℝ :=
  s ^ m • (fderiv ℝ f (heatFamilyScaleLinear s z)).comp (heatFamilyScaleLinear s)

theorem heatFamilyRadialDerivative_continuous (m : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Continuous (fun p : ℝ × HeatRadialFrameSpace => heatFamilyRadialDerivative m f p.2 p.1) := by
  have hs := heatFamilyScaleLinear_continuous.comp (continuous_fst : Continuous
    (Prod.fst : ℝ × HeatRadialFrameSpace → ℝ))
  exact (continuous_fst.pow m).smul
    (((hf.continuous_fderiv one_ne_zero).comp (hs.clm_apply continuous_snd)).clm_comp hs)

theorem heatFamilyRadialAverage_hasFDerivAt (m : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (z : HeatRadialFrameSpace) :
    HasFDerivAt (heatFamilyRadialAverage m f)
      (∫ s : ℝ in 0..1, heatFamilyRadialDerivative m f z s) z := by
  have hD := heatFamilyRadialDerivative_continuous m f hf
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
    (isCompact_closedBall z 1)).exists_bound_of_continuousOn
    hD.continuousOn
  have hF (y : HeatRadialFrameSpace) : Continuous
      (fun s : ℝ => s ^ m * f (heatFamilyScaleLinear s y)) :=
    (continuous_id.pow m).mul (hf.continuous.comp
      (heatFamilyScaleLinear_continuous.clm_apply continuous_const))
  have hDy : Continuous (heatFamilyRadialDerivative m f z) :=
    hD.comp (continuous_id.prodMk continuous_const)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y s => s ^ m * f (heatFamilyScaleLinear s y))
    (F' := heatFamilyRadialDerivative m f) (bound := fun _ => C)
    (ball_mem_nhds z one_pos)
    (Eventually.of_forall fun y => (hF y).aestronglyMeasurable)
    ((hF z).intervalIntegrable 0 1) hDy.aestronglyMeasurable
    (Eventually.of_forall fun s hs y hy => ?_)
    (continuous_const.intervalIntegrable 0 1)
    (Eventually.of_forall fun s _ y _ => ?_)
  · apply hC (s, y)
    rw [uIoc_of_le zero_le_one] at hs
    exact ⟨⟨hs.1.le, hs.2⟩, ball_subset_closedBall hy⟩
  · exact ((hf.differentiable one_ne_zero (heatFamilyScaleLinear s y)).hasFDerivAt.comp y
      (heatFamilyScaleLinear s).hasFDerivAt).const_mul (s ^ m)

theorem heatFamilyRadialAverage_fderiv_apply (m : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (z w : HeatRadialFrameSpace) :
    fderiv ℝ (heatFamilyRadialAverage m f) z w =
      heatFamilyRadialAverage (m + 1) (fun y => fderiv ℝ f y (w.1, 0)) z +
      heatFamilyRadialAverage m (fun y => fderiv ℝ f y (0, w.2)) z := by
  have hD : Continuous (heatFamilyRadialDerivative m f z) :=
    (heatFamilyRadialDerivative_continuous m f hf).comp
    (continuous_id.prodMk (continuous_const (y := z)))
  have hG (v : HeatRadialFrameSpace) (n : ℕ) : Continuous (fun s : ℝ =>
      s ^ n * fderiv ℝ f (heatFamilyScaleLinear s z) v) :=
    (continuous_id.pow n).mul (((hf.continuous_fderiv one_ne_zero).comp
      (heatFamilyScaleLinear_continuous.clm_apply continuous_const)).clm_apply continuous_const)
  have heval : (∫ s : ℝ in 0..1, heatFamilyRadialDerivative m f z s) w =
      ∫ s : ℝ in 0..1, heatFamilyRadialDerivative m f z s w :=
    ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 1) w
  rw [(heatFamilyRadialAverage_hasFDerivAt m f hf z).fderiv, heval]
  unfold heatFamilyRadialAverage
  rw [← intervalIntegral.integral_add ((hG (w.1, 0) (m + 1)).intervalIntegrable 0 1)
    ((hG (0, w.2) m).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro s _
  have hw : heatFamilyScaleLinear s w = s • (w.1, (0 : CoordinateFrameSpace)) + (0, w.2) := by
    ext <;> simp [heatFamilyScaleLinear_apply]
  change s ^ m * fderiv ℝ f (heatFamilyScaleLinear s z) (heatFamilyScaleLinear s w) = _
  rw [hw, map_add, map_smul]
  simp only [smul_eq_mul, pow_succ]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-coordinate density and its leading scalar heat
amplitude. Their normalization is obtained from the differential of the
geometric exponential at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalMetric_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : heatNormalMetric g o e 0 = 1 := by
  have hd := frameExponential_chart_strictDerivative_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hzero : fderiv ℝ (fun v : FourSpace => chartAt FourSpace e.base
      (frameExponential g o e v)) 0 = e.frame.map.toContinuousLinearMap := by
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using hd.hasFDerivAt.fderiv
  have hc := frameExponential_center_fderiv g o e 0
  rw [frameExponential_zero] at hc
  have hD : (show FourSpace →L[ℝ] FourSpace from
      mfderiv I4 I4 (frameExponential g o e) 0) = e.frame.map.toContinuousLinearMap :=
    hc.symm.trans hzero
  ext i j
  change g.inner (frameExponential g o e 0)
    ((show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) 0)
      (coordinateVector i))
    ((show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) 0)
      (coordinateVector j)) = (1 : Mat4) i j
  rw [hD, frameExponential_zero]
  change g.inner e.base (WithLp.toLp 2 (e.frame.matrix *ᵥ Pi.single i 1))
    (WithLp.toLp 2 (e.frame.matrix *ᵥ Pi.single j 1)) = _
  rw [← chartMetric_pairing, dotProduct_comm,
    ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    e.frame.orthonormal, Matrix.one_mulVec]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem frameExponentialJacobian_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : frameExponentialJacobian g o e 0 = 1 := by
  change Real.sqrt (heatNormalMetric g o e 0).det = 1
  rw [heatNormalMetric_zero, Matrix.det_one, Real.sqrt_one]

theorem heatNormalLeadingAmplitude_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : heatNormalLeadingAmplitude g o e 0 = 1 := by
  simp [heatNormalLeadingAmplitude, frameExponentialJacobian_zero]

theorem heatNormalLeadingAmplitude_normalization (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (v : FourSpace)
    (hv : 0 < frameExponentialJacobian g o e v) :
    heatNormalLeadingAmplitude g o e v ^ 2 * frameExponentialJacobian g o e v = 1 := by
  unfold heatNormalLeadingAmplitude
  rw [inv_pow, Real.sq_sqrt hv.le, inv_mul_cancel₀ hv.ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial transport preserves finite joint regularity, including the
center and frame parameters. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

local instance heatFamilyRadialRegularityDualNormedGroup :
    NormedAddCommGroup (HeatRadialFrameSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance heatFamilyRadialRegularityDualNormedSpace :
    NormedSpace ℝ (HeatRadialFrameSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

abbrev heatFamilyBasis := Module.finBasis ℝ HeatRadialFrameSpace

theorem heatFamilyLinearForm_expansion (L : HeatRadialFrameSpace →L[ℝ] ℝ) :
    L = ∑ i, L (heatFamilyBasis i) • (heatFamilyBasis.coord i).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  have hz := congrArg L (heatFamilyBasis.sum_repr z)
  rw [map_sum] at hz
  simp only [map_smul, smul_eq_mul] at hz
  rw [← hz]
  simp only [_root_.sum_apply, _root_.smul_apply, Module.Basis.coord_apply,
    LinearMap.coe_toContinuousLinearMap', smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem heatFamilyRadialAverage_preserves_contDiff (n : ℕ) :
    ∀ (m : ℕ) (f : HeatRadialFrameSpace → ℝ), ContDiff ℝ n f →
      ContDiff ℝ n (heatFamilyRadialAverage m f) := by
  induction n with
  | zero =>
    intro m f hf
    exact contDiff_zero.mpr (heatFamilyRadialAverage_continuous m f hf.continuous)
  | succ n ih =>
    intro m f hf
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hp (v : HeatRadialFrameSpace) : ContDiff ℝ n (fun y => fderiv ℝ f y v) :=
      (hf.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiff_const
    let D : HeatRadialFrameSpace → HeatRadialFrameSpace →L[ℝ] ℝ := fun z =>
      ∑ i, (heatFamilyRadialAverage (m + 1)
        (fun y => fderiv ℝ f y ((heatFamilyBasis i).1, 0)) z +
        heatFamilyRadialAverage m
          (fun y => fderiv ℝ f y (0, (heatFamilyBasis i).2)) z) •
        (heatFamilyBasis.coord i).toContinuousLinearMap
    have hD : ContDiff ℝ n D := by
      apply ContDiff.sum
      intro i _
      exact (ContinuousLinearMap.toSpanSingleton ℝ
        (heatFamilyBasis.coord i).toContinuousLinearMap).contDiff.comp
          ((ih (m + 1) _ (hp _)).add (ih m _ (hp _)))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨D, hD, ?_⟩
    intro z
    have he : fderiv ℝ (heatFamilyRadialAverage m f) z = D z := by
      rw [heatFamilyLinearForm_expansion (fderiv ℝ (heatFamilyRadialAverage m f) z)]
      apply Finset.sum_congr rfl
      intro i _
      rw [heatFamilyRadialAverage_fderiv_apply m f hf1 z]
    exact he ▸ (heatFamilyRadialAverage_hasFDerivAt m f hf1 z).differentiableAt.hasFDerivAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Regularity of the actual normal metric, volume density and leading heat
amplitude. All are derived from the exponential and the smooth metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalMetric_smoothAt_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun v => heatNormalMetric g o e v i j) 0 := by
  let c := e.base
  let F := fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)
  have hF : ContDiffAt ℝ ∞ F 0 := frameExponential_chart_smoothAt_zero g o c e
    (mem_chart_source FourSpace c)
  have hFD : ContDiffAt ℝ ∞ (fderiv ℝ F) 0 := hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hcoord (k l : Fin 4) : ContDiffAt ℝ ∞
      (fun v => (fderiv ℝ F v (coordinateVector k)) l) 0 := by
    let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) l
    have hd : ContDiffAt ℝ ∞ (fun v => fderiv ℝ F v (coordinateVector k)) 0 :=
      hFD.clm_apply contDiffAt_const
    exact π.contDiff.contDiffAt.comp 0 hd
  have htarget : F 0 ∈ (chartAt FourSpace c).target := by
    dsimp [F]
    rw [frameExponential_zero]
    exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have hmetric (k l : Fin 4) : ContDiffAt ℝ ∞
      (fun v => metricInChart g c (F v) k l) 0 :=
    (metricInChart_contDiffAt g c (F 0) htarget k l).comp 0 hF
  have hright : ContDiffAt ℝ ∞ (fun v =>
      WithLp.ofLp (fderiv ℝ F v (coordinateVector i)) ⬝ᵥ
        (metricInChart g c (F v) *ᵥ WithLp.ofLp (fderiv ℝ F v (coordinateVector j)))) 0 := by
    simp only [dotProduct, Matrix.mulVec]
    apply ContDiffAt.sum
    intro k _
    apply (hcoord i k).mul
    apply ContDiffAt.sum
    intro l _
    exact (hmetric k l).mul (hcoord j l)
  apply hright.congr_of_eventuallyEq
  have hn : ∀ᶠ v in 𝓝 (0 : FourSpace), frameExponential g o e v ∈
      (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds (by
        rw [frameExponential_zero]
        exact mem_chart_source FourSpace c))
  filter_upwards [hn] with v hv
  exact heatNormalMetric_chart_pairing g o e c v hv i j

theorem frameExponentialJacobian_smoothAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) :
    ContDiffAt ℝ ∞ (frameExponentialJacobian g o e) 0 := by
  have hd : ContDiffAt ℝ ∞ (fun v => (heatNormalMetric g o e v).det) 0 := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    exact contDiffAt_const.mul
      (contDiffAt_prod fun i _ => heatNormalMetric_smoothAt_zero g o e (σ i) i)
  exact hd.sqrt (by rw [heatNormalMetric_zero, Matrix.det_one]; norm_num)

theorem heatNormalLeadingAmplitude_smoothAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) :
    ContDiffAt ℝ ∞ (heatNormalLeadingAmplitude g o e) 0 := by
  have hJ : frameExponentialJacobian g o e 0 ≠ 0 := by
    rw [frameExponentialJacobian_zero]
    norm_num
  exact ((frameExponentialJacobian_smoothAt_zero g o e).sqrt hJ).inv
    (by rw [frameExponentialJacobian_zero]; norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smoothness of the actual inverse normal metric, by the finite adjugate
formula. No choice of matrix norm or inverse regularity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

theorem heatMatrixDeterminant_smoothAt (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun y => A y i j) x) :
    ContDiffAt ℝ ∞ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalInverse_smoothAt_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun v => (heatNormalMetric g o e v)⁻¹ i j) 0 := by
  let A := heatNormalMetric g o e
  have hA : ∀ i j, ContDiffAt ℝ ∞ (fun v => A v i j) 0 :=
    heatNormalMetric_smoothAt_zero g o e
  have hinv : ContDiffAt ℝ ∞ (fun v => ((A v).det)⁻¹) 0 :=
    (heatMatrixDeterminant_smoothAt A 0 hA).inv (by
      change (heatNormalMetric g o e 0).det ≠ 0
      rw [heatNormalMetric_zero, Matrix.det_one]
      norm_num)
  have hadj : ContDiffAt ℝ ∞ (fun v => (A v).adjugate i j) 0 := by
    simp only [Matrix.adjugate_apply]
    apply heatMatrixDeterminant_smoothAt
    intro r t
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ ∞
          (fun _ : FourSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) t) 0)
    · simpa only [Matrix.updateRow_ne hr] using hA r t
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linear operations and local vanishing for the actual radial integral. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Interval
noncomputable section

theorem heatWeighted_integrable (m : ℕ) (U F : FourSpace → ℝ)
    (hU : Continuous U) (hF : Continuous F) (hU0 : ∀ x, U x ≠ 0) (x : FourSpace) :
    IntervalIntegrable (fun s : ℝ => s ^ m * (F (s • x) / U (s • x))) volume 0 1 := by
  have hs : Continuous (fun s : ℝ => s • x) := continuous_id.smul continuous_const
  exact ((continuous_id.pow m).mul ((hF.comp hs).div (hU.comp hs)
    (fun s => hU0 (s • x)))).intervalIntegrable 0 1

theorem fourHeatWeightedRadialAverage_sum {ι : Type*} [Fintype ι]
    (m : ℕ) (U : FourSpace → ℝ) (F : ι → FourSpace → ℝ)
    (hU : Continuous U) (hF : ∀ i, Continuous (F i)) (hU0 : ∀ x, U x ≠ 0) (x : FourSpace) :
    fourHeatWeightedRadialAverage m U (fun y => ∑ i, F i y) x =
      ∑ i, fourHeatWeightedRadialAverage m U (F i) x := by
  unfold fourHeatWeightedRadialAverage fourHeatRadialAverage
  simp only [Finset.sum_div, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => heatWeighted_integrable m U (F i) hU (hF i) hU0 x)]
  rw [Finset.mul_sum]

theorem fourHeatWeightedRadialAverage_add (m : ℕ) (U F G : FourSpace → ℝ)
    (hU : Continuous U) (hF : Continuous F) (hG : Continuous G) (hU0 : ∀ x, U x ≠ 0)
    (x : FourSpace) :
    fourHeatWeightedRadialAverage m U (fun y => F y + G y) x =
      fourHeatWeightedRadialAverage m U F x + fourHeatWeightedRadialAverage m U G x := by
  unfold fourHeatWeightedRadialAverage fourHeatRadialAverage
  simp only [add_div, mul_add]
  rw [intervalIntegral.integral_add (heatWeighted_integrable m U F hU hF hU0 x)
    (heatWeighted_integrable m U G hU hG hU0 x)]
  ring

theorem fourHeatWeightedRadialAverage_const_mul (m : ℕ) (U F : FourSpace → ℝ) (a : ℝ)
    (x : FourSpace) :
    fourHeatWeightedRadialAverage m U (fun y => a * F y) x =
      a * fourHeatWeightedRadialAverage m U F x := by
  unfold fourHeatWeightedRadialAverage fourHeatRadialAverage
  have he (s : ℝ) : s ^ m * (a * F (s • x) / U (s • x)) =
      a * (s ^ m * (F (s • x) / U (s • x))) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem fourHeatWeightedRadialAverage_zero_germ (m : ℕ) (U F : FourSpace → ℝ)
    (hF : F =ᶠ[𝓝 0] fun _ => 0) :
    fourHeatWeightedRadialAverage m U F =ᶠ[𝓝 0] fun _ => 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hF
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) hr] with x hx
  have hz : fourHeatRadialAverage m (fun y => F y / U y) x = 0 := by
    unfold fourHeatRadialAverage
    have he : (∫ s : ℝ in 0..1, s ^ m * (F (s • x) / U (s • x))) =
        ∫ _s : ℝ in 0..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
      have hnorm : ‖s • x‖ ≤ ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs'.1]
        exact mul_le_of_le_one_left (norm_nonneg x) hs'.2
      have hmem : s • x ∈ Metric.ball (0 : FourSpace) r := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hnorm.trans_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
      change s ^ m * (F (s • x) / U (s • x)) = 0
      rw [hball hmem, zero_div, mul_zero]
    rw [he]
    simp
  change U x * fourHeatRadialAverage m (fun y => F y / U y) x = 0
  rw [hz, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The determinant used in Euclidean change of variables is the actual
normal volume density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_jacobianMatrix_det (F : FourSpace → FourSpace) (x : FourSpace) :
    (jacobianMatrix F x).det = (fderiv ℝ F x).det := by
  have h : jacobianMatrix F x = LinearMap.toMatrix
      (PiLp.basisFun 2 ℝ (Fin 4)) (PiLp.basisFun 2 ℝ (Fin 4))
      (fderiv ℝ F x).toLinearMap := by
    ext i j
    simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply]
    rfl
  rw [h, LinearMap.det_toMatrix]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.volume_jacobian (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source) :
    frameExponentialJacobian g o e x =
      |(fderiv ℝ (fun y => (D.point y).1) x).det| *
        chartVolumeDensity g c (D.point x).1 := by
  change Real.sqrt (heatNormalMetric g o e x).det = _
  rw [D.metric_pullback x hx hs, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hh : (jacobianMatrix (fun y => (D.point y).1) x).det *
      (metricInChart g c (D.point x).1).det *
      (jacobianMatrix (fun y => (D.point y).1) x).det =
      (jacobianMatrix (fun y => (D.point y).1) x).det ^ 2 *
        (metricInChart g c (D.point x).1).det := by ring
  rw [hh, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, heat_jacobianMatrix_det]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-coordinate integration formula, with no assumed
Jacobian or measure-identification input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalScalarLift_integral (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source)
    (hD : C.source ⊆ Metric.ball 0 D.radius)
    (ψ : FourSpace → ℝ) (hs : tsupport ψ ⊆ C.source) :
    (∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g) =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ψ x := by
  let P := fun y => (D.point y).1
  have heq : EqOn P (fun y => chartAt FourSpace c (C y)) C.source := by
    intro x hx
    exact (D.exponential x (hD hx)).trans (congrArg (chartAt FourSpace c) (hE hx).symm)
  have hd (x : FourSpace) (hx : x ∈ C.source) :
      HasFDerivAt (fun y => chartAt FourSpace c (C y)) (fderiv ℝ P x) x := by
    have hp : DifferentiableAt ℝ P x :=
      (hP.contDiffAt (C.open_source.mem_nhds hx)).fst.differentiableAt (by norm_num)
    apply hp.hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [C.open_source.mem_nhds hx] with y hy
    exact (heq hy).symm
  rw [heatNormalScalarLift_integral_chart g c C hCt (fun x => fderiv ℝ P x) hd]
  congr 1
  calc
    _ = ∫ x in C.source, frameExponentialJacobian g o e x * ψ x := by
      apply setIntegral_congr_fun C.open_source.measurableSet
      intro x hx
      have hc : frameExponential g o e x ∈ (chartAt FourSpace c).source := by
        rw [← hE hx]
        exact hCt (C.map_source hx)
      have hv := D.volume_jacobian x (hD hx) hc
      change |(fderiv ℝ P x).det| * chartVolumeDensity g c (chartAt FourSpace c (C x)) *
        ψ x = _
      have heqx : P x = chartAt FourSpace c (C x) := heq hx
      rw [← heqx]
      exact congrArg (fun z : ℝ => z * ψ x) hv.symm
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth extensions of local heat data. A positive leading
amplitude has a positive extension, so the transport integrals can be
constructed globally without division at a zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff _root_.Topology

noncomputable section

theorem heatScalarCutoff_contDiff (n : ℕ) (χ f : FourSpace → ℝ)
    (hχ : ContDiff ℝ n χ) (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ n f y) :
    ContDiff ℝ n (fun y => χ y * f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf y hy)
  · have hz : (fun z => χ z * f z) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp only [hz, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

def heatScalarBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : FourSpace) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem heatScalar_extension (n : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ n f 0) :
    ∃ F : FourSpace → ℝ, ContDiff ℝ n F ∧ HasCompactSupport F ∧ F =ᶠ[𝓝 0] f := by
  obtain ⟨r, hr, hreg⟩ := Metric.eventually_nhds_iff.mp (hf.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let χ := heatScalarBump r hr
  have hs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hF : ContDiff ℝ n (fun y => χ y * f y) :=
    heatScalarCutoff_contDiff n χ f χ.contDiff
      (fun y hy => hreg (by simpa only [mem_ball] using hs hy))
  refine ⟨fun y => χ y * f y, hF, χ.hasCompactSupport.mul_right, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  simp only [hy, Pi.one_apply, one_mul]

theorem heatScalar_positive_extension (n : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ n f 0) (hpos : 0 < f 0) :
    ∃ F : FourSpace → ℝ, ContDiff ℝ n F ∧ (∀ y, 0 < F y) ∧ F =ᶠ[𝓝 0] f := by
  have hp : ∀ᶠ y in 𝓝 (0 : FourSpace), 0 < f y :=
    hf.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨r, hr, hreg⟩ := Metric.eventually_nhds_iff.mp ((hf.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).and hp)
  let χ := heatScalarBump r hr
  have hs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hnear (y : FourSpace) (hy : y ∈ tsupport χ) : ContDiffAt ℝ n f y ∧ 0 < f y :=
    hreg (by simpa only [mem_ball] using hs hy)
  have hχ : ContDiff ℝ n χ := χ.contDiff
  let F := fun y => χ y * f y + (1 - χ y)
  refine ⟨F, (heatScalarCutoff_contDiff n χ f hχ (fun y hy => (hnear y hy).1)).add
    (contDiff_const.sub hχ), ?_, ?_⟩
  · intro y
    change 0 < χ y * f y + (1 - χ y)
    by_cases hz : χ y = 0
    · simp [hz]
    · have hχp : 0 < χ y := lt_of_le_of_ne χ.nonneg (Ne.symm hz)
      have hy : y ∈ tsupport χ := subset_tsupport χ hz
      exact add_pos_of_pos_of_nonneg (mul_pos hχp (hnear y hy).2)
        (sub_nonneg.mpr χ.le_one)
  · filter_upwards [χ.eventuallyEq_one] with y hy
    simp only [F, hy, Pi.one_apply, one_mul, sub_self, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the actual differential expression used in the
heat transport recursion. Each application loses two derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeat_partial_germ {u v : FourSpace → ℝ} {x : FourSpace}
    (h : u =ᶠ[nhds x] v) (i : Fin 4) : partialDeriv u i x = partialDeriv v i x := by
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h.fderiv_eq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality of the coefficient operator through its actual second
derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeat_second_germ {u v : FourSpace → ℝ} {x : FourSpace}
    (h : u =ᶠ[𝓝 x] v) (i j : Fin 4) :
    partialDeriv (partialDeriv u i) j x = partialDeriv (partialDeriv v i) j x := by
  have hp : partialDeriv u i =ᶠ[𝓝 x] partialDeriv v i := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact fourHeat_partial_germ hy i
  exact fourHeat_partial_germ hp j

theorem fourHeatLocalOperator_germ (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ)
    {u v : FourSpace → ℝ} {x : FourSpace} (h : u =ᶠ[𝓝 x] v) :
    fourHeatLocalOperator a b c u x = fourHeatLocalOperator a b c v x := by
  simp only [fourHeatLocalOperator, fourHeat_second_germ h, fourHeat_partial_germ h,
    h.self_of_nhds]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the local heat operator on actual twice differentiable
functions. These formulas allow cancellation in the finite heat ansatz. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeat_partial_const_mul (r : ℝ) (u : FourSpace → ℝ) (i : Fin 4)
    (x : FourSpace) : partialDeriv (fun y => r * u y) i x = r * partialDeriv u i x := by
  change fderiv ℝ (r • u) x (coordinateVector i) = _
  rw [fderiv_const_smul_field]
  rfl

theorem fourHeat_second_const_mul (r : ℝ) (u : FourSpace → ℝ) (i j : Fin 4)
    (x : FourSpace) : partialDeriv (partialDeriv (fun y => r * u y) i) j x =
      r * partialDeriv (partialDeriv u i) j x := by
  simp only [funext (fourHeat_partial_const_mul r u i), fourHeat_partial_const_mul]

theorem fourHeatLocalOperator_const_mul (a : Mat4) (b : Fin 4 → ℝ) (c r : ℝ)
    (u : FourSpace → ℝ) (x : FourSpace) :
    fourHeatLocalOperator a b c (fun y => r * u y) x =
      r * fourHeatLocalOperator a b c u x := by
  unfold fourHeatLocalOperator
  simp only [fourHeat_second_const_mul, fourHeat_partial_const_mul]
  simp only [Fin.sum_univ_four]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite smooth extensions of the normal-coordinate coefficients.
They agree with the geometric operator near the center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalDrift_smoothAt_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (j : Fin 4) :
    ContDiffAt ℝ ∞ (fun x => heatNormalDrift g o e x j) 0 := by
  have hA := heatNormalInverse_smoothAt_zero g o e
  have hJ := frameExponentialJacobian_smoothAt_zero g o e
  have hAp (i : Fin 4) : ContDiffAt ℝ ∞
      (partialDeriv (fun y => (heatNormalMetric g o e y)⁻¹ i j) i) 0 :=
    ((hA i j).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const
  have hJp (i : Fin 4) : ContDiffAt ℝ ∞
      (partialDeriv (frameExponentialJacobian g o e) i) 0 :=
    (hJ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const
  have hJ0 : frameExponentialJacobian g o e 0 ≠ 0 := by
    rw [frameExponentialJacobian_zero]; exact one_ne_zero
  exact ((ContDiffAt.sum (fun i _ => hAp i)).add
    ((hJ.inv hJ0).mul (ContDiffAt.sum (fun i _ => (hA i j).mul (hJp i))))).neg

theorem exists_heatNormalExtension (n : ℕ) (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) : Nonempty (HeatNormalExtension n g o e) := by
  choose A hA hAc hAe using fun i j => heatScalar_extension n
    (fun x => (heatNormalMetric g o e x)⁻¹ i j)
    ((heatNormalInverse_smoothAt_zero g o e i j).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  choose B hB hBc hBe using fun i => heatScalar_extension n
    (fun x => heatNormalDrift g o e x i)
    ((heatNormalDrift_smoothAt_zero g o e i).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  obtain ⟨U, hU, hUp, hUe⟩ := heatScalar_positive_extension n
    (heatNormalLeadingAmplitude g o e)
    ((heatNormalLeadingAmplitude_smoothAt_zero g o e).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (by rw [heatNormalLeadingAmplitude_zero]; exact zero_lt_one)
  refine ⟨{
    a := fun x i j => A i j x
    b := fun x i => B i x
    U := U
    a_regular := hA
    b_regular := hB
    U_regular := hU
    U_pos := hUp
    a_near := ?_
    b_near := ?_
    U_near := hUe }⟩
  · have h := eventually_all.mpr (fun i => eventually_all.mpr (fun j => hAe i j))
    filter_upwards [h] with x hx
    funext i j
    exact hx i j
  · have h := eventually_all.mpr (fun i => hBe i)
    filter_upwards [h] with x hx
    funext i
    exact hx i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual L2 values and Laplacians of C4 cutoffs. Their spectral pairing
is obtained from the finite-regularity geometric Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance scalarFinite_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def scalarFiniteValueL2 (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) :
    Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ ⟨f, hf.continuous⟩

omit [SecondCountableTopology M] in
theorem scalarFiniteValueL2_coe (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) :
    scalarFiniteValueL2 g f hf =ᵐ[normalizedVolume g] f :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite third-order scalar heat ansatz and its exact differential
identities. The coefficients here are actual scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatPolynomial_contDiff (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ i, ContDiff ℝ 2 (u i)) (t : ℝ) : ContDiff ℝ 2 (fourHeatPolynomial u t) :=
  (((hu 0).add (contDiff_const.mul (hu 1))).add
    (contDiff_const.mul (hu 2))).add (contDiff_const.mul (hu 3))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial integration preserves finite differentiability. This avoids
spending an extra derivative at every transport step in the bundle heat
construction. Only the two derivatives in the local operator are lost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ContDiff

noncomputable section

theorem fourHeatRadialAverage_preserves_contDiff (n : ℕ) :
    ∀ (m : ℕ) (f : FourSpace → ℝ), ContDiff ℝ n f →
      ContDiff ℝ n (fourHeatRadialAverage m f) := by
  induction n with
  | zero =>
    intro m f hf
    apply contDiff_zero.mpr
    have hc : Continuous (Function.uncurry (fun x : FourSpace => fun s : ℝ =>
        s ^ m * f (s • x))) :=
      (continuous_snd.pow m).mul (hf.continuous.comp (continuous_snd.smul continuous_fst))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1
  | succ n ih =>
    intro m f hf
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hp (i : Fin 4) : ContDiff ℝ n (partialDeriv f i) :=
      fourHeat_partial_contDiff n f hf i
    let D : FourSpace → FourSpace →L[ℝ] ℝ := fun x =>
      ∑ i : Fin 4, fourHeatRadialAverage (m + 1) (partialDeriv f i) x •
        PiLp.proj 2 (fun _ : Fin 4 => ℝ) i
    have hD : ContDiff ℝ n D := by
      apply ContDiff.sum
      intro i _
      exact (ih (m + 1) (partialDeriv f i) (hp i)).smul contDiff_const
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨D, hD, ?_⟩
    intro x
    have h := (fourHeatRadialAverage_hasFDerivAt m f hf1 x).differentiableAt.hasFDerivAt
    rwa [fourHeatRadialAverage_fderiv m f hf1 x] at h

theorem fourHeatWeightedRadialAverage_preserves_contDiff (n m : ℕ) (U F : FourSpace → ℝ)
    (hU : ContDiff ℝ n U) (hF : ContDiff ℝ n F) (hU0 : ∀ x, U x ≠ 0) :
    ContDiff ℝ n (fourHeatWeightedRadialAverage m U F) :=
  hU.mul (fourHeatRadialAverage_preserves_contDiff n m _ (hF.div hU hU0))

theorem fourHeatCoefficient_contDiff_two_derivatives (m : ℕ) : ∀ (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (c U : FourSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun x => a x i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun x => b x i)) →
    ContDiff ℝ (n + 2 * m : ℕ) c → ContDiff ℝ (n + 2 * m : ℕ) U →
    (∀ x, U x ≠ 0) → ContDiff ℝ n (fourHeatCoefficient a b c U m) := by
  induction m with
  | zero =>
    intro n a b c U ha hb hc hU hU0
    simpa only [fourHeatCoefficient, mul_zero, add_zero] using hU
  | succ m ih =>
    intro n a b c U ha hb hc hU hU0
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg : ContDiff ℝ (n + 2 : ℕ) (fourHeatCoefficient a b c U m) :=
      ih (n + 2) a b c U (fun i j => he ▸ ha i j) (fun i => he ▸ hb i)
        (he ▸ hc) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    apply fourHeatWeightedRadialAverage_preserves_contDiff n m U _ (hU.of_le hle) _ hU0
    exact (fourHeatLocalOperator_contDiff n a b c _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle) (hc.of_le hle) hreg).neg

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal amplitude pairs with a test tensor by evaluating the test
in the same normal orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem heat_normal_frame_pairing (G E F : Mat4)
    (hE : Eᵀ * G * E = 1) (hF : Fᵀ * G * F = 1)
    (T U : CovariantCoordinates 2) :
    frameTensorPairing (frameTensor F (frameTensor E⁻¹ T)) (frameTensor F U) =
      frameTensorPairing T (frameTensor E U) := by
  have hd : E.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hE
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
    norm_num at h
  have hi : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E (isUnit_iff_ne_zero.mpr hd)
  have hi' : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E (isUnit_iff_ne_zero.mpr hd)
  have ht : Eᵀ * E⁻¹ᵀ = 1 := by rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  have hEE : E * Eᵀ = F * Fᵀ :=
    (heat_orthonormal_inverse G E hE).trans (heat_orthonormal_inverse G F hF).symm
  have hQ : (E⁻¹ * F) * (E⁻¹ * F)ᵀ = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = E⁻¹ * (F * Fᵀ) * E⁻¹ᵀ := by simp only [Matrix.mul_assoc]
      _ = E⁻¹ * (E * Eᵀ) * E⁻¹ᵀ := by rw [← hEE]
      _ = (E⁻¹ * E) * (Eᵀ * E⁻¹ᵀ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hi, ht, Matrix.one_mul]
  have hf : frameTensor F U = frameTensor (E⁻¹ * F) (frameTensor E U) := by
    rw [← frameTensor_mul, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  rw [← frameTensor_mul, hf]
  exact frameTensor_pairing_orthogonal (E⁻¹ * F) hQ T (frameTensor E U)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-regularity coefficients of the one-form operator in
normal coordinates and the radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.oneFirst_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) (k l : Fin 4) :
    ContDiffAt ℝ 11 (fun x => heatNormalOneFirst D x i k l) 0 := by
  apply fourHeatOneConnectionFirst_contDiffAt
  · intro i j
    exact (heatNormalInverse_smoothAt_zero g o e i j).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact D.connection_regular

theorem HeatNormalFrameData.oneZero_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (k l : Fin 4) : ContDiffAt ℝ 10 (fun x => heatNormalOneZero D x k l) 0 := by
  apply fourHeatOneConnectionZero_contDiffAt
  · intro i j
    exact (heatNormalInverse_smoothAt_zero g o e i j).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · intro i
    exact (heatNormalDrift_smoothAt_zero g o e i).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact D.connection_regular
  · intro k l
    exact contDiffAt_const

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal amplitude pairs with a test tensor by evaluating the test
in the same normal orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem heat_normal_one_pairing (G E F : Mat4)
    (hE : Eᵀ * G * E = 1) (hF : Fᵀ * G * F = 1)
    (T U : CovariantCoordinates 1) :
    frameTensorPairing (frameTensor F (frameTensor E⁻¹ T)) (frameTensor F U) =
      frameTensorPairing T (frameTensor E U) := by
  have hd : E.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hE
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
    norm_num at h
  have hi : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E (isUnit_iff_ne_zero.mpr hd)
  have hi' : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E (isUnit_iff_ne_zero.mpr hd)
  have ht : Eᵀ * E⁻¹ᵀ = 1 := by rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  have hEE : E * Eᵀ = F * Fᵀ :=
    (heat_orthonormal_inverse G E hE).trans (heat_orthonormal_inverse G F hF).symm
  have hQ : (E⁻¹ * F) * (E⁻¹ * F)ᵀ = 1 := by
    rw [Matrix.transpose_mul]
    calc
      _ = E⁻¹ * (F * Fᵀ) * E⁻¹ᵀ := by simp only [Matrix.mul_assoc]
      _ = E⁻¹ * (E * Eᵀ) * E⁻¹ᵀ := by rw [← hEE]
      _ = (E⁻¹ * E) * (Eᵀ * E⁻¹ᵀ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hi, ht, Matrix.one_mul]
  have hf : frameTensor F U = frameTensor (E⁻¹ * F) (frameTensor E U) := by
    rw [← frameTensor_mul, ← Matrix.mul_assoc, hi', Matrix.one_mul]
  rw [← frameTensor_mul, hf]
  exact frameTensor_pairing_orthogonal (E⁻¹ * F) hQ T (frameTensor E U)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Values and curvature potentials in the actual normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framedValue_chart {g : SmoothMetric M} (o : FrameOrientation g)
    (u : M → TwoFormFour) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    twoFormFramedValue o u e = frameTensor (frameChartMatrix g c e)
      (twoFormCoordinates o u c (chartAt FourSpace c e.base)) := by
  have hb := mem_chart_source FourSpace e.base
  have ht := twoFormCoordinates_transition o u e.base c
    (chartAt FourSpace e.base e.base) ((chartAt FourSpace e.base).map_source hb)
    (by simpa only [(chartAt FourSpace e.base).left_inv hb] using he)
  have hz : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    change chartAt FourSpace c ((chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base e.base)) = _
    rw [(chartAt FourSpace e.base).left_inv hb]
  rw [hz] at ht
  rw [frameChartMatrix_eq, frameTensor_mul, ← ht]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the six-component local differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleOperator_contDiff (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (C : FourSpace → HeatMat6)
    (u : FourSpace → Fin 6 → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ n (fun x => b x i))
    (hB : ∀ i k l, ContDiff ℝ n (fun x => B x i k l))
    (hC : ∀ k l, ContDiff ℝ n (fun x => C x k l))
    (hu : ∀ l, ContDiff ℝ (n + 2 : ℕ) (fun x => u x l)) (k : Fin 6) :
    ContDiff ℝ n (fun x => fourHeatBundleOperator (a x) (b x) (B x) (C x) u x k) := by
  have hu0 (l : Fin 6) : ContDiff ℝ n (fun x => u x l) :=
    (hu l).of_le (by exact_mod_cast Nat.le_add_right n 2)
  have hp (i : Fin 4) (l : Fin 6) :
      ContDiff ℝ n (partialDeriv (fun x => u x l) i) :=
    fourHeat_partial_contDiff n _ ((hu l).of_le
      (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))) i
  exact ((fourHeatLocalOperator_contDiff n a b (fun _ => 0) _ ha hb contDiff_const (hu k)).add
    (ContDiff.sum (fun i _ => ContDiff.sum (fun l _ => (hB i k l).mul (hp i l))))).add
    (ContDiff.sum (fun l _ => (hC k l).mul (hu0 l)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the four-component local differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatOneOperator_contDiff (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (C : FourSpace → Mat4)
    (u : FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ n (fun x => b x i))
    (hB : ∀ i k l, ContDiff ℝ n (fun x => B x i k l))
    (hC : ∀ k l, ContDiff ℝ n (fun x => C x k l))
    (hu : ∀ l, ContDiff ℝ (n + 2 : ℕ) (fun x => u x l)) (k : Fin 4) :
    ContDiff ℝ n (fun x => fourHeatOneOperator (a x) (b x) (B x) (C x) u x k) := by
  have hu0 (l : Fin 4) : ContDiff ℝ n (fun x => u x l) :=
    (hu l).of_le (by exact_mod_cast Nat.le_add_right n 2)
  have hp (i : Fin 4) (l : Fin 4) :
      ContDiff ℝ n (partialDeriv (fun x => u x l) i) :=
    fourHeat_partial_contDiff n _ ((hu l).of_le
      (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))) i
  exact ((fourHeatLocalOperator_contDiff n a b (fun _ => 0) _ ha hb contDiff_const (hu k)).add
    (ContDiff.sum (fun i _ => ContDiff.sum (fun l _ => (hB i k l).mul (hp i l))))).add
    (ContDiff.sum (fun l _ => (hC k l).mul (hu0 l)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity, including the first spatial derivatives, of the
finite heat amplitude polynomial. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatPolynomial_joint_continuous (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ m, Continuous (u m)) :
    Continuous (fun z : ℝ × FourSpace => fourHeatPolynomial u z.1 z.2) := by
  have h0 : Continuous (fun z : ℝ × FourSpace => u 0 z.2) := (hu 0).comp continuous_snd
  have h1 : Continuous (fun z : ℝ × FourSpace => u 1 z.2) := (hu 1).comp continuous_snd
  have h2 : Continuous (fun z : ℝ × FourSpace => u 2 z.2) := (hu 2).comp continuous_snd
  have h3 : Continuous (fun z : ℝ × FourSpace => u 3 z.2) := (hu 3).comp continuous_snd
  exact ((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
    ((continuous_fst.pow 3).mul h3)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous compact chart tensors and their exact smooth realizations
on the intrinsic frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def heatChartTensor (g : SmoothMetric M) (c : M)
    (F : FourSpace → CovariantCoordinates 2) (hF : ContinuousOn F (chartAt FourSpace c).target)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ (chartAt FourSpace c).target) :
    C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f),
    (PiLp.continuous_toLp 2 _).comp
      (heatNormalFrameTensorLift_continuous g c (chartAt FourSpace c).symm F
        (fun _ h => h) hF hc hs)⟩

theorem heatChartTensor_smooth (c : M) (F : FourSpace → CovariantCoordinates 2)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    (hFa : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    heatChartTensor g c F hF.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) =
      smoothTwoFormEuclideanValue (twoFormChartTest o c F hF hFa hK hKt hFs) := by
  apply ContinuousMap.ext
  intro f
  by_cases hf : f.base ∈ (chartAt FourSpace c).source
  · change WithLp.toLp 2 (heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f) =
      WithLp.toLp 2 (twoFormFramedValue o (twoFormChartTest o c F hF hFa hK hKt hFs).val f)
    rw [heatNormalFrameTensorLift, ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hf)]
    rw [
      heat_framedValue_chart o _ c f hf,
      twoFormChartTest_coordinates c F hF hFa hK hKt hFs _ ((chartAt FourSpace c).map_source hf),
      OpenPartialHomeomorph.symm_symm]
  · have hzero := twoFormChartTest_zero_off (o := o) c F hF hFa hK hKt hFs f.base (by
      rintro ⟨z, hz, hzf⟩
      exact hf (hzf ▸ (chartAt FourSpace c).map_target (hKt hz)))
    change WithLp.toLp 2 (heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f) =
      WithLp.toLp 2 (twoFormFramedValue o (twoFormChartTest o c F hF hFa hK hKt hFs).val f)
    rw [heatNormalFrameTensorLift, ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hf)]
    rw [twoFormFramedValue_eq]
    change WithLp.toLp 2 (0 : CovariantCoordinates 2) =
      WithLp.toLp 2 (twoFormTensor (twoFormFrameAction _ ((twoFormChartTest o c F hF hFa hK hKt hFs).val f.base)))
    rw [hzero]
    change WithLp.toLp 2 (0 : CovariantCoordinates 2) =
      WithLp.toLp 2 (twoFormTensorLinear ((twoFormFrameActionLinear _) 0))
    rw [map_zero, map_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth extensions of the actual normal-frame bundle coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalOneExtension {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e) :
    Nonempty (HeatNormalOneExtension D) := by
  obtain ⟨base⟩ := exists_heatNormalExtension 10 g o e
  choose B hB hBc hBe using fun i k l => heatScalar_extension 10
    (fun x => heatNormalOneFirst D x i k l)
    ((D.oneFirst_regular i k l).of_le (by norm_num))
  choose C hC hCc hCe using fun k l => heatScalar_extension 10
    (fun x => heatNormalOneZero D x k l) (D.oneZero_regular k l)
  refine ⟨{
    base := base
    B := fun x i k l => B i k l x
    C := fun x k l => C k l x
    B_regular := hB
    C_regular := hC
    B_near := ?_
    C_near := ?_ }⟩
  · have h := eventually_all.mpr (fun i => eventually_all.mpr
      (fun k => eventually_all.mpr (fun l => hBe i k l)))
    filter_upwards [h] with x hx
    funext i k l
    exact hx i k l
  · have h := eventually_all.mpr (fun k => eventually_all.mpr (fun l => hCe k l))
    filter_upwards [h] with x hx
    funext k l
    exact hx k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp radial regularity theorem supplies the scalar
C4 amplitudes from ten coefficient derivatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff
noncomputable section

theorem fourHeatCoefficient_contDiff_two (m : ℕ) : ∀ (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (c U : FourSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun x => a x i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun x => b x i)) →
    ContDiff ℝ (n + 2 * m : ℕ) c → ContDiff ℝ (n + 2 * m : ℕ) U →
    (∀ x, U x ≠ 0) → ContDiff ℝ n (fourHeatCoefficient a b c U m) :=
  fourHeatCoefficient_contDiff_two_derivatives m

end
end PositiveEinsteinFour.Geometry
end


section

/-! Successive matrix heat amplitudes are actual radial integrals of the
preceding amplitude under the six-component differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleCoefficient_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (C : FourSpace → HeatMat6) (U : FourSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun x => a x i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun x => b x i)) →
    (∀ i k l, ContDiff ℝ (n + 2 * m : ℕ) (fun x => B x i k l)) →
    (∀ k l, ContDiff ℝ (n + 2 * m : ℕ) (fun x => C x k l)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ x, U x ≠ 0) →
    ∀ k l, ContDiff ℝ n (fun x => fourHeatBundleCoefficient a b B C U m x k l) := by
  induction m with
  | zero =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    simpa only [fourHeatBundleCoefficient, mul_zero, add_zero] using hU.mul
      (contDiff_const (c := if k = l then (1 : ℝ) else 0))
  | succ m ih =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b B C U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (fun i k l => he ▸ hB i k l)
      (fun k l => he ▸ hC k l) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    apply fourHeatWeightedRadialAverage_preserves_contDiff n m U _ (hU.of_le hle) _ hU0
    exact (fourHeatBundleOperator_contDiff n a b B C _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle)
      (fun i k l => (hB i k l).of_le hle) (fun k l => (hC k l).of_le hle)
      (fun q => hreg q l) k).neg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Successive matrix heat amplitudes are actual radial integrals of the
preceding amplitude under the four-component differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatOneCoefficient (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (C : FourSpace → Mat4) (U : FourSpace → ℝ) :
    ℕ → FourSpace → Mat4
  | 0 => fun x k l => U x * (if k = l then 1 else 0)
  | m + 1 => fun x k l => fourHeatWeightedRadialAverage m U
      (fun y => -fourHeatOneOperator (a y) (b y) (B y) (C y)
        (fun z q => fourHeatOneCoefficient a b B C U m z q l) y k) x

theorem fourHeatOneCoefficient_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (C : FourSpace → Mat4) (U : FourSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun x => a x i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun x => b x i)) →
    (∀ i k l, ContDiff ℝ (n + 2 * m : ℕ) (fun x => B x i k l)) →
    (∀ k l, ContDiff ℝ (n + 2 * m : ℕ) (fun x => C x k l)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ x, U x ≠ 0) →
    ∀ k l, ContDiff ℝ n (fun x => fourHeatOneCoefficient a b B C U m x k l) := by
  induction m with
  | zero =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    simpa only [fourHeatOneCoefficient, mul_zero, add_zero] using hU.mul
      (contDiff_const (c := if k = l then (1 : ℝ) else 0))
  | succ m ih =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b B C U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (fun i k l => he ▸ hB i k l)
      (fun k l => he ▸ hC k l) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    apply fourHeatWeightedRadialAverage_preserves_contDiff n m U _ (hU.of_le hle) _ hU0
    exact (fourHeatOneOperator_contDiff n a b B C _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle)
      (fun i k l => (hB i k l).of_le hle) (fun k l => (hC k l).of_le hle)
      (fun q => hreg q l) k).neg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity and finite time polynomials for the actual four-component
differential expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatOnePolynomial (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (t : ℝ) (x : FourSpace) (k : Fin 4) : ℝ :=
  fourHeatPolynomial (fun m y => u m y k) t x

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform control of compact chart tensors in the frame-bundle norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M}

local instance heatChartTensorBoundCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatChartTensor_bound (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (F : FourSpace → CovariantCoordinates 2)
      (hF : ContinuousOn F (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
      (r : ℝ), 0 ≤ r → (∀ z a, |F z a| ≤ r) →
      ‖heatChartTensor g c F hF
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)‖ ≤ B * r := by
  let L : Set (FrameBundle g) := (fun f => f.base) ⁻¹' ((chartAt FourSpace c).symm '' K)
  have hLc : IsCompact L :=
    ((hK.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hKt)).isClosed.preimage
      (continuous_frameBase g)).isCompact
  have hLs (f : FrameBundle g) (hf : f ∈ L) : f.base ∈ (chartAt FourSpace c).source := by
    obtain ⟨z, hz, he⟩ := hf
    change (chartAt FourSpace c).symm z = f.base at he
    rw [← he]
    exact (chartAt FourSpace c).map_target (hKt hz)
  have hcont : ContinuousOn (fun f : FrameBundle g => tensorTransportWeight 2 (frameChartMatrix g c f)) L := by
    intro f hf
    exact ((tensorTransportWeight_continuous 2).continuousAt.comp
      (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j =>
        frameChartMatrix_continuousAt g c f (hLs f hf) i j)))).continuousWithinAt
  obtain ⟨b, hb⟩ := (hLc.image_of_continuousOn hcont).isBounded.exists_norm_le
  let B := (Fintype.card (Fin 2 → Fin 4) : ℝ) * max b 0
  refine ⟨B, mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _), ?_⟩
  intro F hF hFs r hr hFr
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) hr)).mpr
  intro f
  by_cases hf : f ∈ L
  · have hw : tensorTransportWeight 2 (frameChartMatrix g c f) ≤ max b 0 :=
      (le_abs_self _).trans ((hb _ ⟨f, hf, rfl⟩).trans (le_max_left _ _))
    change ‖(WithLp.toLp 2 (heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f) : TwoTensorEuclidean)‖ ≤ _
    rw [heatNormalFrameTensorLift, ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hLs f hf)]
    refine (twoTensorEuclidean_norm_le_sum _).trans ?_
    calc
      _ ≤ ∑ _a : Fin 2 → Fin 4, tensorTransportWeight 2 (frameChartMatrix g c f) * r :=
        Finset.sum_le_sum (fun a _ => frameTensor_abs_le_weight _ _ r hr (hFr _) a)
      _ = (Fintype.card (Fin 2 → Fin 4) : ℝ) * tensorTransportWeight 2 (frameChartMatrix g c f) * r := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ B * r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)) hr
  · have hz : heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f = 0 := by
      apply not_ne_iff.mp
      intro hn
      obtain ⟨z, hz, he⟩ := heatNormalFrameTensorLift_support g c (chartAt FourSpace c).symm F hn
      exact hf ⟨z, hFs hz, he⟩
    change ‖(WithLp.toLp 2 (heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f) : TwoTensorEuclidean)‖ ≤ _
    rw [hz]
    simpa using mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card (Fin 2 → Fin 4))) (le_max_right b 0)) hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Four C4 scalar transport amplitudes. Ten derivatives of the
extended normal coefficients give four derivatives of each amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {e : FrameBundle g}

def HeatNormalExtension.scalarAmplitude (E : HeatNormalExtension 10 g o e)
    (m : ℕ) : FourSpace → ℝ :=
  fourHeatCoefficient E.a E.b (fun _ => 0) E.U m

theorem HeatNormalExtension.scalarAmplitude_regular (E : HeatNormalExtension 10 g o e)
    (m : ℕ) (hm : m ≤ 3) : ContDiff ℝ 4 (E.scalarAmplitude m) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact fourHeatCoefficient_contDiff_two m 4 E.a E.b (fun _ => 0) E.U
    (fun i j => (E.a_regular i j).of_le hle)
    (fun i => (E.b_regular i).of_le hle) contDiff_const (E.U_regular.of_le hle)
    (fun x => (E.U_pos x).ne')

def HeatNormalExtension.scalarParametrix (E : HeatNormalExtension 10 g o e)
    (t : ℝ) (x : FourSpace) : ℝ :=
  fourHeatGaussian t x * fourHeatPolynomial (fun m : Fin 4 => E.scalarAmplitude m) t x

theorem HeatNormalExtension.scalarParametrix_regular (E : HeatNormalExtension 10 g o e)
    (t : ℝ) : ContDiff ℝ 4 (E.scalarParametrix t) := by
  have hu (m : Fin 4) := E.scalarAmplitude_regular m (by omega)
  exact (fourHeatGaussian_smooth t).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.mul
    ((((hu 0).add (contDiff_const.mul (hu 1))).add
      (contDiff_const.mul (hu 2))).add (contDiff_const.mul (hu 3)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous alternating chart tensors are limits of actual
smooth two-form frame tensors in the uniform norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance heatChartTensorApproxCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [CompactSpace M] in
theorem heatChartTensor_sub (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (F H : FourSpace → CovariantCoordinates 2)
    (hF : ContinuousOn F (chartAt FourSpace c).target)
    (hH : ContinuousOn H (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (hHs : tsupport H ⊆ K)
    (hDs : tsupport (H - F) ⊆ K) :
    heatChartTensor g c (H - F) (hH.sub hF)
      (hK.of_isClosed_subset (isClosed_tsupport _) hDs) (hDs.trans hKt) =
      heatChartTensor g c H hH (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) -
      heatChartTensor g c F hF (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) := by
  classical
  apply ContinuousMap.ext
  intro f
  apply WithLp.ofLp_injective 2
  change heatNormalFrameTensorLift g c (chartAt FourSpace c).symm (H - F) f =
    heatNormalFrameTensorLift g c (chartAt FourSpace c).symm H f -
      heatNormalFrameTensorLift g c (chartAt FourSpace c).symm F f
  by_cases hf : f.base ∈ (chartAt FourSpace c).symm.target
  · simp only [heatNormalFrameTensorLift, ite_eq_left hf, Pi.sub_apply]
    funext a
    exact frameTensor_sub _ _ _ a
  · simp only [heatNormalFrameTensorLift, ite_eq_right hf, sub_self]

theorem heatChartTensor_smooth_approx (c : M)
    (F : FourSpace → CovariantCoordinates 2) (hF : Continuous F)
    (ha : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : smoothTwoForms o,
      ‖smoothTwoFormEuclideanValue u - heatChartTensor g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)‖ < ε := by
  obtain ⟨B, hB, hbound⟩ := heatChartTensor_bound (g := g) c hK hKt
  let r := ε / (B + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  obtain ⟨H, hH, hHa, hHsF, hdist⟩ := heat_alternating_smooth_approx F hF ha r hr
  have hHs : tsupport H ⊆ K := hHsF.trans hFs
  have hDs : tsupport (H - F) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    have hH0 : H z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hHs h))
    have hF0 : F z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hFs h))
    exact hz (by simp only [Pi.sub_apply, hH0, hF0, sub_self])
  refine ⟨twoFormChartTest o c H hH.contDiffOn hHa hK hKt hHs, ?_⟩
  rw [← heatChartTensor_smooth c H hH.contDiffOn hHa hK hKt hHs,
    ← heatChartTensor_sub c hK hKt F H hF.continuousOn hH.continuous.continuousOn hFs hHs hDs]
  have hb := hbound (H - F) (hH.continuous.continuousOn.sub hF.continuousOn) hDs r hr.le
    (fun z a => (hdist z a).le)
  have hbr : B * r < ε := by
    have h := (mul_div_cancel₀ ε (show B + 1 ≠ 0 by positivity))
    change (B + 1) * r = ε at h
    nlinarith
  exact hb.trans_lt hbr

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-component heat operator differentiates only normal vectors,
while retaining joint regularity in the center and frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyScalarPartial_contDiff (n : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (i : Fin 4) :
    ContDiff ℝ n (heatFamilyScalarPartial f i) := by
  rw [contDiff_iff_contDiffAt]
  exact fun z => heatFamilyScalarPartial_contDiffAt n f z hf.contDiffAt i

def heatFamilyBundleOperator (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (B : HeatRadialFrameSpace → Fin 4 → HeatMat6)
    (C : HeatRadialFrameSpace → HeatMat6) (u : HeatRadialFrameSpace → Fin 6 → ℝ)
    (z : HeatRadialFrameSpace) (k : Fin 6) : ℝ :=
  -(∑ i : Fin 4, ∑ j : Fin 4, a z i j *
      heatFamilyScalarPartial (heatFamilyScalarPartial (fun y => u y k) i) j z) +
    (∑ i : Fin 4, b z i * heatFamilyScalarPartial (fun y => u y k) i z) +
    (∑ i : Fin 4, ∑ l : Fin 6, B z i k l * heatFamilyScalarPartial (fun y => u y l) i z) +
    ∑ l : Fin 6, C z k l * u z l

theorem heatFamilyBundleOperator_contDiff (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → HeatMat6) (C : HeatRadialFrameSpace → HeatMat6)
    (u : HeatRadialFrameSpace → Fin 6 → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun z => a z i j))
    (hb : ∀ i, ContDiff ℝ n (fun z => b z i))
    (hB : ∀ i k l, ContDiff ℝ n (fun z => B z i k l))
    (hC : ∀ k l, ContDiff ℝ n (fun z => C z k l))
    (hu : ∀ l, ContDiff ℝ (n + 2 : ℕ) (fun z => u z l)) (k : Fin 6) :
    ContDiff ℝ n (fun z => heatFamilyBundleOperator a b B C u z k) := by
  have hp (i : Fin 4) (l : Fin 6) :
      ContDiff ℝ (n + 1 : ℕ) (heatFamilyScalarPartial (fun z => u z l) i) := by
    apply heatFamilyScalarPartial_contDiff
    simpa only [Nat.add_assoc] using hu l
  have hn : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hpp (i j : Fin 4) : ContDiff ℝ n
      (heatFamilyScalarPartial (heatFamilyScalarPartial (fun z => u z k) i) j) :=
    heatFamilyScalarPartial_contDiff n _ (hp i k) j
  exact (((ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (ha i j).mul (hpp i j)))).neg.add
      (ContDiff.sum (fun i _ => (hb i).mul ((hp i k).of_le hn)))).add
    (ContDiff.sum (fun i _ => ContDiff.sum (fun l _ =>
      (hB i k l).mul ((hp i l).of_le hn))))).add
    (ContDiff.sum (fun l _ => (hC k l).mul ((hu l).of_le
      (by exact_mod_cast (show n ≤ n + 2 by omega)))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first four actual normal-frame matrix heat amplitudes and their
transport equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalBundleExtension.amplitude_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (m : ℕ) (hm : m ≤ 3) (k l : Fin 6) :
    ContDiff ℝ 4 (fun x => E.amplitude m x k l) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact fourHeatBundleCoefficient_contDiff m 4 E.base.a E.base.b E.B E.C E.base.U
    (fun i j => (E.base.a_regular i j).of_le hle)
    (fun i => (E.base.b_regular i).of_le hle)
    (fun i k l => (E.B_regular i k l).of_le hle)
    (fun k l => (E.C_regular k l).of_le hle) (E.base.U_regular.of_le hle)
    (fun x => (E.base.U_pos x).ne') k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first four actual normal-frame matrix heat amplitudes and their
transport equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def HeatNormalOneExtension.amplitude {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) : ℕ → FourSpace → Mat4 :=
  fourHeatOneCoefficient E.base.a E.base.b E.B E.C E.base.U

theorem HeatNormalOneExtension.amplitude_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (m : ℕ) (hm : m ≤ 3) (k l : Fin 4) :
    ContDiff ℝ 4 (fun x => E.amplitude m x k l) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact fourHeatOneCoefficient_contDiff m 4 E.base.a E.base.b E.B E.C E.base.U
    (fun i j => (E.base.a_regular i j).of_le hle)
    (fun i => (E.base.b_regular i).of_le hle)
    (fun i k l => (E.B_regular i k l).of_le hle)
    (fun k l => (E.C_regular k l).of_le hle) (E.base.U_regular.of_le hle)
    (fun x => (E.base.U_pos x).ne') k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact realization and norm of compact continuous alternating chart
tensors in the actual two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance heatChartTensorL2Compact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatChartTensor_L2_realization (c : M)
    (F : FourSpace → CovariantCoordinates 2) (hF : Continuous F)
    (ha : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    twoFormTensorL2 (twoFormFromContinuousTensor (o := o)
      (heatChartTensor g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt))) =
    ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
      (heatChartTensor g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)) := by
  let A := (twoFormTensorL2 (o := o)).comp (twoFormFromContinuousTensor (o := o))
  let B := ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (E := TwoTensorEuclidean)
  have hclosed : IsClosed {T | A T = B T} := isClosed_eq A.continuous B.continuous
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨u, hu⟩ := heatChartTensor_smooth_approx (o := o) c F hF ha hK hKt hFs ε hε
  refine ⟨smoothTwoFormEuclideanValue u, ?_, ?_⟩
  · change twoFormTensorL2 (twoFormFromContinuousTensor (smoothTwoFormEuclideanValue u)) = _
    rw [twoFormFromContinuousTensor_smooth (show SmoothL2TwoForm o from u),
      twoFormTensorL2_smooth]
    rfl
  · simpa only [dist_eq_norm, norm_sub_rev] using hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first four transport amplitudes form a jointly finite-smooth
family. The recursive integral keeps the center and frame fixed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

def heatFamilyWeightedAverage (m : ℕ) (U f : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  U z * heatFamilyRadialAverage m (fun y => f y / U y) z

theorem heatFamilyWeightedAverage_contDiff (n m : ℕ) (U f : HeatRadialFrameSpace → ℝ)
    (hU : ContDiff ℝ n U) (hf : ContDiff ℝ n f) (hU0 : ∀ z, U z ≠ 0) :
    ContDiff ℝ n (heatFamilyWeightedAverage m U f) :=
  hU.mul (heatFamilyRadialAverage_preserves_contDiff n m _ (hf.div hU hU0))

def heatFamilyCoefficientSequence (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (B : HeatRadialFrameSpace → Fin 4 → HeatMat6)
    (C : HeatRadialFrameSpace → HeatMat6) (U : HeatRadialFrameSpace → ℝ) :
    ℕ → HeatRadialFrameSpace → HeatMat6
  | 0 => fun z k l => U z * (if k = l then 1 else 0)
  | m + 1 => fun z k l => heatFamilyWeightedAverage m U
      (fun y => -heatFamilyBundleOperator a b B C
        (fun w q => heatFamilyCoefficientSequence a b B C U m w q l) y k) z

theorem heatFamilyCoefficientSequence_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → HeatMat6) (C : HeatRadialFrameSpace → HeatMat6)
    (U : HeatRadialFrameSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun z => a z i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun z => b z i)) →
    (∀ i k l, ContDiff ℝ (n + 2 * m : ℕ) (fun z => B z i k l)) →
    (∀ k l, ContDiff ℝ (n + 2 * m : ℕ) (fun z => C z k l)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ z, U z ≠ 0) →
    ∀ k l, ContDiff ℝ n (fun z => heatFamilyCoefficientSequence a b B C U m z k l) := by
  induction m with
  | zero =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    simpa only [heatFamilyCoefficientSequence, mul_zero, add_zero] using hU.mul
      (contDiff_const (c := if k = l then (1 : ℝ) else 0))
  | succ m ih =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b B C U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (fun i k l => he ▸ hB i k l)
      (fun k l => he ▸ hC k l) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    apply heatFamilyWeightedAverage_contDiff n m U _ (hU.of_le hle) _ hU0
    exact (heatFamilyBundleOperator_contDiff n a b B C _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle)
      (fun i k l => (hB i k l).of_le hle) (fun k l => (hC k l).of_le hle)
      (fun q => hreg q l) k).neg

def HeatFamilySmoothCoefficients.amplitude (E : HeatFamilySmoothCoefficients) :
    ℕ → HeatRadialFrameSpace → HeatMat6 :=
  heatFamilyCoefficientSequence E.a E.b E.B E.C E.U

theorem HeatFamilySmoothCoefficients.amplitude_regular (E : HeatFamilySmoothCoefficients)
    (m : ℕ) (hm : m ≤ 3) (k l : Fin 6) :
    ContDiff ℝ 4 (fun z => E.amplitude m z k l) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact heatFamilyCoefficientSequence_contDiff m 4 E.a E.b E.B E.C E.U
    (fun i j => (E.a_regular i j).of_le hle) (fun i => (E.b_regular i).of_le hle)
    (fun i k l => (E.B_regular i k l).of_le hle) (fun k l => (E.C_regular k l).of_le hle)
    (E.U_regular.of_le hle) (fun z => (E.U_pos z).ne') k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form heat operator differentiates only normal vectors,
while retaining joint regularity in the center and frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

def heatFamilyOneOperator (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (B : HeatRadialFrameSpace → Fin 4 → Mat4)
    (C : HeatRadialFrameSpace → Mat4) (u : HeatRadialFrameSpace → Fin 4 → ℝ)
    (z : HeatRadialFrameSpace) (k : Fin 4) : ℝ :=
  -(∑ i : Fin 4, ∑ j : Fin 4, a z i j *
      heatFamilyScalarPartial (heatFamilyScalarPartial (fun y => u y k) i) j z) +
    (∑ i : Fin 4, b z i * heatFamilyScalarPartial (fun y => u y k) i z) +
    (∑ i : Fin 4, ∑ l : Fin 4, B z i k l * heatFamilyScalarPartial (fun y => u y l) i z) +
    ∑ l : Fin 4, C z k l * u z l

theorem heatFamilyOneOperator_contDiff (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → Mat4) (C : HeatRadialFrameSpace → Mat4)
    (u : HeatRadialFrameSpace → Fin 4 → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun z => a z i j))
    (hb : ∀ i, ContDiff ℝ n (fun z => b z i))
    (hB : ∀ i k l, ContDiff ℝ n (fun z => B z i k l))
    (hC : ∀ k l, ContDiff ℝ n (fun z => C z k l))
    (hu : ∀ l, ContDiff ℝ (n + 2 : ℕ) (fun z => u z l)) (k : Fin 4) :
    ContDiff ℝ n (fun z => heatFamilyOneOperator a b B C u z k) := by
  have hp (i : Fin 4) (l : Fin 4) :
      ContDiff ℝ (n + 1 : ℕ) (heatFamilyScalarPartial (fun z => u z l) i) := by
    apply heatFamilyScalarPartial_contDiff
    simpa only [Nat.add_assoc] using hu l
  have hn : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hpp (i j : Fin 4) : ContDiff ℝ n
      (heatFamilyScalarPartial (heatFamilyScalarPartial (fun z => u z k) i) j) :=
    heatFamilyScalarPartial_contDiff n _ (hp i k) j
  exact (((ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (ha i j).mul (hpp i j)))).neg.add
      (ContDiff.sum (fun i _ => (hb i).mul ((hp i k).of_le hn)))).add
    (ContDiff.sum (fun i _ => ContDiff.sum (fun l _ =>
      (hB i k l).mul ((hp i l).of_le hn))))).add
    (ContDiff.sum (fun l _ => (hC k l).mul ((hu l).of_le
      (by exact_mod_cast (show n ≤ n + 2 by omega)))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Slicing the family operator gives exactly the corresponding six-component
operator, including its second spatial derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyBundleOperator_slice
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → HeatMat6) (C : HeatRadialFrameSpace → HeatMat6)
    (u : HeatRadialFrameSpace → Fin 6 → ℝ)
    (hu : ∀ l, ContDiff ℝ 2 (fun z => u z l))
    (z : HeatRadialFrameSpace) (k : Fin 6) :
    heatFamilyBundleOperator a b B C u z k =
      fourHeatBundleOperator (a z) (b z) (B z) (C z) (fun x l => u (x, z.2) l) z.1 k := by
  have hp (i : Fin 4) (l : Fin 6) :
      ContDiff ℝ 1 (heatFamilyScalarPartial (fun z => u z l) i) :=
    heatFamilyScalarPartial_contDiff 1 _ (hu l) i
  have he (i : Fin 4) (l : Fin 6) :
      (fun x => heatFamilyScalarPartial (fun z => u z l) i (x, z.2)) =
        partialDeriv (fun x => u (x, z.2) l) i := by
    funext x
    exact heatFamilyScalarPartial_slice _ (x, z.2)
      ((hu l).differentiable (by norm_num) _) i
  have hfirst (i : Fin 4) (l : Fin 6) :
      heatFamilyScalarPartial (fun y => u y l) i z =
        partialDeriv (fun x => u (x, z.2) l) i z.1 :=
    heatFamilyScalarPartial_slice _ z ((hu l).differentiable (by norm_num) z) i
  have hsecond (i j : Fin 4) :
      heatFamilyScalarPartial (heatFamilyScalarPartial (fun y => u y k) i) j z =
        partialDeriv (partialDeriv (fun x => u (x, z.2) k) i) j z.1 := by
    rw [heatFamilyScalarPartial_slice _ z ((hp i k).differentiable one_ne_zero z) j]
    rw [he i k]
  unfold heatFamilyBundleOperator fourHeatBundleOperator fourHeatLocalOperator
    fourHeatBundleFirst fourHeatBundleZero
  simp only [hfirst, hsecond, zero_mul, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-frame bundle parametrix through order three. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalOneParametrix {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (t : ℝ) (x : FourSpace) : Mat4 :=
  fun k l => fourHeatGaussian t x *
    fourHeatOnePolynomial (fun m y q => E.amplitude m y q l) t x k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial first jet on two-forms is the actual curvature action,
including the sign imposed by covariant tensor slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatConnectionMatrixLinear : Mat4 →ₗ[ℝ] HeatMat6 where
  toFun := heatTwoFormConnectionMatrix
  map_add' A B := by
    ext k l
    simpa only [heatConnectionActionLinear_apply, WithLp.ofLp_add, Pi.add_apply,
      heatTwoFormConnectionMatrix, Matrix.add_apply] using congrArg (fun a : TwoFormFour => a k)
      ((heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).map_add A B)
  map_smul' r A := by
    ext k l
    simpa only [heatConnectionActionLinear_apply, PiLp.smul_apply, smul_eq_mul,
      heatTwoFormConnectionMatrix, Matrix.smul_apply, RingHom.id_apply] using
      congrArg (fun a : TwoFormFour => a k)
      ((heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).map_smul r A)

theorem heatTwoFormConnectionMatrix_infinitesimal (B : Mat4) :
    heatTwoFormConnectionMatrix B = twoFormInfinitesimalMatrix (twoFormExtract B) := by
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [heatTwoFormConnectionMatrix, twoFormInfinitesimalMatrix, twoFormSkewAction,
      EuclideanSpace.basisFun_apply]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Locality of the actual four-component covector heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped _root_.Topology
noncomputable section

theorem fourHeatOneOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4)
    {u v : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ q, (fun y => u y q) =ᶠ[𝓝 x] fun y => v y q) (k : Fin 4) :
    fourHeatOneOperator a b B C u x k = fourHeatOneOperator a b B C v x k := by
  simp only [fourHeatOneOperator, fourHeatLocalOperator_germ a b 0 (h k),
    fourHeatOneFirst, fourHeatOneZero, fourHeat_partial_germ (h _),
    fun q => (h q).self_of_nhds]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact coordinate changes for continuous alternating two-tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatCompactTensorLift (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) (z : FourSpace) : CovariantCoordinates 2 := by
  classical
  exact if z ∈ C.target then T (C.symm z) else 0

theorem heatCompactTensorLift_support (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) :
    support (heatCompactTensorLift C T) ⊆ C '' tsupport T := by
  classical
  intro z hz
  by_cases h : z ∈ C.target
  · refine ⟨C.symm z, subset_closure ?_, C.right_inv h⟩
    simpa only [heatCompactTensorLift, ite_eq_left h, mem_support] using hz
  · exact False.elim (hz (by simp only [heatCompactTensorLift, ite_eq_right h]))

theorem heatCompactTensorLift_tsupport (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) (hc : HasCompactSupport T)
    (hs : tsupport T ⊆ C.source) :
    tsupport (heatCompactTensorLift C T) ⊆ C '' tsupport T :=
  closure_minimal (heatCompactTensorLift_support C T)
    (hc.image_of_continuousOn (C.continuousOn.mono hs)).isClosed

theorem heatCompactTensorLift_continuous (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatCompactTensorLift C T) := by
  classical
  have hK := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ C.target
  · have h := (hT.continuousAt (C.open_source.mem_nhds (C.map_target hz))).comp
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hz))
    apply h.congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hz] with w hw
    exact ite_eq_left hw
  · have hzK : z ∉ C '' tsupport T := by
      rintro ⟨x, hx, rfl⟩
      exact hz (C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 2))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    exact not_ne_iff.mp (fun hn => hw (heatCompactTensorLift_support C T hn))

theorem heatCompactTensorLift_skew (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 2)
    (hT : ∀ z i j, T z ![j,i] = -T z ![i,j]) :
    ∀ z i j, heatCompactTensorLift C T z ![j,i] = -heatCompactTensorLift C T z ![i,j] := by
  classical
  intro z i j
  by_cases hz : z ∈ C.target
  · simp only [heatCompactTensorLift, ite_eq_left hz]
    exact hT _ _ _
  · simp only [heatCompactTensorLift, ite_eq_right hz, Pi.zero_apply, neg_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The jointly constructed amplitudes restrict to the radial
transport amplitudes for every fixed initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyWeightedAverage_slice (m : ℕ) (U f : HeatRadialFrameSpace → ℝ)
    (q : CoordinateFrameSpace) (x : FourSpace) :
    heatFamilyWeightedAverage m U f (x, q) =
      fourHeatWeightedRadialAverage m (fun y => U (y, q)) (fun y => f (y, q)) x := rfl

theorem HeatFamilySmoothCoefficients.amplitude_slice (E : HeatFamilySmoothCoefficients)
    (m : ℕ) : m ≤ 3 → ∀ q : CoordinateFrameSpace,
      (fun x => E.amplitude m (x, q)) =
        fourHeatBundleCoefficient (fun x => E.a (x, q)) (fun x => E.b (x, q))
          (fun x => E.B (x, q)) (fun x => E.C (x, q)) (fun x => E.U (x, q)) m := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm q
    have hrec := ih (by omega) q
    funext x k l
    have hu (a : Fin 6) : ContDiff ℝ 2 (fun z => E.amplitude m z a l) :=
      (E.amplitude_regular m (by omega) a l).of_le (by norm_num)
    have ho : (fun y => -heatFamilyBundleOperator E.a E.b E.B E.C
        (fun z a => E.amplitude m z a l) (y, q) k) =
        (fun y => -fourHeatBundleOperator (E.a (y, q)) (E.b (y, q)) (E.B (y, q)) (E.C (y, q))
          (fun z a => fourHeatBundleCoefficient (fun x => E.a (x, q))
            (fun x => E.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.U (x, q)) m z a l) y k) := by
      funext y
      rw [heatFamilyBundleOperator_slice E.a E.b E.B E.C
        (fun z a => E.amplitude m z a l) hu (y, q) k]
      have he : (fun z a => E.amplitude m (z, q) a l) =
          (fun z a => fourHeatBundleCoefficient (fun x => E.a (x, q))
            (fun x => E.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.U (x, q)) m z a l) := by
        funext z a
        exact congrArg (fun A : FourSpace → HeatMat6 => A z a l) hrec
      rw [he]
    change heatFamilyWeightedAverage m E.U (fun y => -heatFamilyBundleOperator E.a E.b E.B E.C
      (fun z a => E.amplitude m z a l) y k) (x, q) = _
    rw [heatFamilyWeightedAverage_slice, ho]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Slicing the family operator gives exactly the corresponding one-form
operator, including its second spatial derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyOneOperator_slice
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → Mat4) (C : HeatRadialFrameSpace → Mat4)
    (u : HeatRadialFrameSpace → Fin 4 → ℝ)
    (hu : ∀ l, ContDiff ℝ 2 (fun z => u z l))
    (z : HeatRadialFrameSpace) (k : Fin 4) :
    heatFamilyOneOperator a b B C u z k =
      fourHeatOneOperator (a z) (b z) (B z) (C z) (fun x l => u (x, z.2) l) z.1 k := by
  have hp (i : Fin 4) (l : Fin 4) :
      ContDiff ℝ 1 (heatFamilyScalarPartial (fun z => u z l) i) :=
    heatFamilyScalarPartial_contDiff 1 _ (hu l) i
  have he (i : Fin 4) (l : Fin 4) :
      (fun x => heatFamilyScalarPartial (fun z => u z l) i (x, z.2)) =
        partialDeriv (fun x => u (x, z.2) l) i := by
    funext x
    exact heatFamilyScalarPartial_slice _ (x, z.2)
      ((hu l).differentiable (by norm_num) _) i
  have hfirst (i : Fin 4) (l : Fin 4) :
      heatFamilyScalarPartial (fun y => u y l) i z =
        partialDeriv (fun x => u (x, z.2) l) i z.1 :=
    heatFamilyScalarPartial_slice _ z ((hu l).differentiable (by norm_num) z) i
  have hsecond (i j : Fin 4) :
      heatFamilyScalarPartial (heatFamilyScalarPartial (fun y => u y k) i) j z =
        partialDeriv (partialDeriv (fun x => u (x, z.2) k) i) j z.1 := by
    rw [heatFamilyScalarPartial_slice _ z ((hp i k).differentiable one_ne_zero z) j]
    rw [he i k]
  unfold heatFamilyOneOperator fourHeatOneOperator fourHeatLocalOperator
    fourHeatOneFirst fourHeatOneZero
  simp only [hfirst, hsecond, zero_mul, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and exact cutoff residual of the actual normal
bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalBundleParametrix_space_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (t : ℝ) (k l : Fin 6) :
    ContDiff ℝ 2 (fun x => heatNormalBundleParametrix E t x k l) := by
  exact ((fourHeatGaussian_smooth t).of_le (by norm_num)).mul
    (fourHeatPolynomial_contDiff (fun m y => E.amplitude m y k l)
      (fun m => (E.amplitude_regular m (by omega) k l).of_le (by norm_num)) t)

def heatNormalCutoffParametrix {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (t : ℝ)
    (x : FourSpace) : HeatMat6 := fun k l => χ x * heatNormalBundleParametrix E t x k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Second derivatives of the signed quadratic connection term at a
radial center, where the connection itself vanishes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_partial_finite_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (x : FourSpace)
    (hF : ∀ k, DifferentiableAt ℝ (F k) x) (i : Fin 4) :
    partialDeriv (fun y => ∑ k, F k y) i x = ∑ k, partialDeriv (F k) i x := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun k _ => hF k), _root_.sum_apply]

def heatSixPartial (A : FourSpace → HeatMat6) (i : Fin 4) (x : FourSpace) : HeatMat6 :=
  fun k l => partialDeriv (fun y => A y k l) i x

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint C4 one-form amplitudes with the center and frame retained. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

def heatFamilyOneCoefficientSequence (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (B : HeatRadialFrameSpace → Fin 4 → Mat4)
    (C : HeatRadialFrameSpace → Mat4) (U : HeatRadialFrameSpace → ℝ) :
    ℕ → HeatRadialFrameSpace → Mat4
  | 0 => fun z k l => U z * (if k = l then 1 else 0)
  | m + 1 => fun z k l => heatFamilyWeightedAverage m U
      (fun y => -heatFamilyOneOperator a b B C
        (fun w q => heatFamilyOneCoefficientSequence a b B C U m w q l) y k) z

theorem heatFamilyOneCoefficientSequence_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (B : HeatRadialFrameSpace → Fin 4 → Mat4) (C : HeatRadialFrameSpace → Mat4)
    (U : HeatRadialFrameSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun z => a z i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun z => b z i)) →
    (∀ i k l, ContDiff ℝ (n + 2 * m : ℕ) (fun z => B z i k l)) →
    (∀ k l, ContDiff ℝ (n + 2 * m : ℕ) (fun z => C z k l)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ z, U z ≠ 0) →
    ∀ k l, ContDiff ℝ n (fun z => heatFamilyOneCoefficientSequence a b B C U m z k l) := by
  induction m with
  | zero =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    simpa only [heatFamilyOneCoefficientSequence, mul_zero, add_zero] using hU.mul
      (contDiff_const (c := if k = l then (1 : ℝ) else 0))
  | succ m ih =>
    intro n a b B C U ha hb hB hC hU hU0 k l
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b B C U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (fun i k l => he ▸ hB i k l)
      (fun k l => he ▸ hC k l) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    apply heatFamilyWeightedAverage_contDiff n m U _ (hU.of_le hle) _ hU0
    exact (heatFamilyOneOperator_contDiff n a b B C _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle)
      (fun i k l => (hB i k l).of_le hle) (fun k l => (hC k l).of_le hle)
      (fun q => hreg q l) k).neg

def HeatFamilyOneCoefficients.amplitude (E : HeatFamilyOneCoefficients) :
    ℕ → HeatRadialFrameSpace → Mat4 :=
  heatFamilyOneCoefficientSequence E.base.a E.base.b E.B E.C E.base.U

theorem HeatFamilyOneCoefficients.amplitude_regular (E : HeatFamilyOneCoefficients)
    (m : ℕ) (hm : m ≤ 3) (k l : Fin 4) :
    ContDiff ℝ 4 (fun z => E.amplitude m z k l) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact heatFamilyOneCoefficientSequence_contDiff m 4 E.base.a E.base.b E.B E.C E.base.U
    (fun i j => (E.base.a_regular i j).of_le hle) (fun i => (E.base.b_regular i).of_le hle)
    (fun i k l => (E.B_regular i k l).of_le hle) (fun k l => (E.C_regular k l).of_le hle)
    (E.base.U_regular.of_le hle) (fun z => (E.base.U_pos z).ne') k l


end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar transport amplitudes with joint center and frame dependence. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

def heatFamilyScalarOperator (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (u : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  heatFamilyOneOperator a b (fun _ => 0) (fun _ => 0) (fun y _ => u y) z 0

theorem heatFamilyScalarOperator_contDiff (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (u : HeatRadialFrameSpace → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun z => a z i j))
    (hb : ∀ i, ContDiff ℝ n (fun z => b z i)) (hu : ContDiff ℝ (n + 2 : ℕ) u) :
    ContDiff ℝ n (heatFamilyScalarOperator a b u) :=
  heatFamilyOneOperator_contDiff n a b _ _ _ ha hb
    (fun _ _ _ => contDiff_const) (fun _ _ => contDiff_const) (fun _ => hu) 0

theorem heatFamilyScalarOperator_slice (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (u : HeatRadialFrameSpace → ℝ)
    (hu : ContDiff ℝ 2 u) (z : HeatRadialFrameSpace) :
    heatFamilyScalarOperator a b u z =
      fourHeatLocalOperator (a z) (b z) 0 (fun x => u (x, z.2)) z.1 := by
  unfold heatFamilyScalarOperator
  rw [heatFamilyOneOperator_slice a b _ _ _ (fun _ => hu) z 0]
  simp only [fourHeatOneOperator, fourHeatOneFirst, fourHeatOneZero, Pi.zero_apply,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

def heatFamilyScalarSequence (a : HeatRadialFrameSpace → Mat4)
    (b : HeatRadialFrameSpace → Fin 4 → ℝ) (U : HeatRadialFrameSpace → ℝ) :
    ℕ → HeatRadialFrameSpace → ℝ
  | 0 => U
  | m + 1 => heatFamilyWeightedAverage m U
      (fun z => -heatFamilyScalarOperator a b (heatFamilyScalarSequence a b U m) z)

theorem heatFamilyScalarSequence_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : HeatRadialFrameSpace → Mat4) (b : HeatRadialFrameSpace → Fin 4 → ℝ)
    (U : HeatRadialFrameSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 2 * m : ℕ) (fun z => a z i j)) →
    (∀ i, ContDiff ℝ (n + 2 * m : ℕ) (fun z => b z i)) →
    ContDiff ℝ (n + 2 * m : ℕ) U → (∀ z, U z ≠ 0) →
    ContDiff ℝ n (heatFamilyScalarSequence a b U m) := by
  induction m with
  | zero =>
    intro n a b U ha hb hU hU0
    simpa only [heatFamilyScalarSequence, mul_zero, add_zero] using hU
  | succ m ih =>
    intro n a b U ha hb hU hU0
    have he : n + 2 * (m + 1) = (n + 2) + 2 * m := by omega
    have hreg := ih (n + 2) a b U (fun i j => he ▸ ha i j)
      (fun i => he ▸ hb i) (he ▸ hU) hU0
    have hle : (n : ℕ∞ω) ≤ (n + 2 * (m + 1) : ℕ) := by
      exact_mod_cast (show n ≤ n + 2 * (m + 1) by omega)
    exact heatFamilyWeightedAverage_contDiff n m U _ (hU.of_le hle)
      ((heatFamilyScalarOperator_contDiff n a b _ (fun i j => (ha i j).of_le hle)
        (fun i => (hb i).of_le hle) hreg).neg) hU0

def HeatFamilySmoothCoefficients.scalarAmplitude (E : HeatFamilySmoothCoefficients) :
    ℕ → HeatRadialFrameSpace → ℝ := heatFamilyScalarSequence E.a E.b E.U

theorem HeatFamilySmoothCoefficients.scalarAmplitude_regular (E : HeatFamilySmoothCoefficients)
    (m : ℕ) (hm : m ≤ 3) : ContDiff ℝ 4 (E.scalarAmplitude m) := by
  have hle : ((4 + 2 * m : ℕ) : ℕ∞ω) ≤ 10 := by
    exact_mod_cast (show 4 + 2 * m ≤ 10 by omega)
  exact heatFamilyScalarSequence_contDiff m 4 E.a E.b E.U
    (fun i j => (E.a_regular i j).of_le hle) (fun i => (E.b_regular i).of_le hle)
    (E.U_regular.of_le hle) (fun z => (E.U_pos z).ne')

theorem HeatFamilySmoothCoefficients.scalarAmplitude_slice (E : HeatFamilySmoothCoefficients)
    (m : ℕ) : m ≤ 3 → ∀ q : CoordinateFrameSpace,
      (fun x => E.scalarAmplitude m (x, q)) =
        fourHeatCoefficient (fun x => E.a (x, q)) (fun x => E.b (x, q))
          (fun _ => 0) (fun x => E.U (x, q)) m := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm q
    have hrec := ih (by omega) q
    have hu : ContDiff ℝ 2 (E.scalarAmplitude m) :=
      (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)
    funext x
    change heatFamilyWeightedAverage m E.U
      (fun y => -heatFamilyScalarOperator E.a E.b (E.scalarAmplitude m) y) (x, q) = _
    rw [heatFamilyWeightedAverage_slice]
    have ho : (fun y => -heatFamilyScalarOperator E.a E.b (E.scalarAmplitude m) (y, q)) =
        (fun y => -fourHeatLocalOperator (E.a (y, q)) (E.b (y, q)) 0
          (fourHeatCoefficient (fun z => E.a (z, q)) (fun z => E.b (z, q))
            (fun _ => 0) (fun z => E.U (z, q)) m) y) := by
      funext y
      rw [heatFamilyScalarOperator_slice E.a E.b _ hu, hrec]
    rw [ho]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express compact normal-coordinate tensors in one actual smooth
manifold chart, without changing their frame-bundle values. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {c : M}

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem heatNormalChartMap_source (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source) :
    (C.trans (chartAt FourSpace c)).source = C.source := by
  ext x
  change (x ∈ C.source ∧ C x ∈ (chartAt FourSpace c).source) ↔ x ∈ C.source
  exact ⟨And.left, fun hx => ⟨hx, hCt (C.map_source hx)⟩⟩

omit [T3Space M] in
theorem heatNormalChartTensor_realization (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 2) (f : FrameBundle g) :
    heatNormalFrameTensorLift g c C T f =
    heatNormalFrameTensorLift g c (chartAt FourSpace c).symm
      (heatCompactTensorLift (C.trans (chartAt FourSpace c)) T) f := by
  classical
  let B := C.trans (chartAt FourSpace c)
  by_cases hf : f.base ∈ C.target
  · have hfc := hCt hf
    have hz : chartAt FourSpace c f.base ∈ B.target := by
      change chartAt FourSpace c f.base ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target
      exact ⟨(chartAt FourSpace c).map_source hfc, by rwa [(chartAt FourSpace c).left_inv hfc]⟩
    rw [heatNormalFrameTensorLift, ite_eq_left hf, heatNormalFrameTensorLift,
      ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (heatCompactTensorLift B T (chartAt FourSpace c f.base))
    rw [heatCompactTensorLift, ite_eq_left hz]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (T (C.symm ((chartAt FourSpace c).symm (chartAt FourSpace c f.base))))
    rw [(chartAt FourSpace c).left_inv hfc]
  · rw [heatNormalFrameTensorLift, ite_eq_right hf]
    by_cases hfc : f.base ∈ (chartAt FourSpace c).source
    · have hz : chartAt FourSpace c f.base ∉ B.target := by
        intro h
        apply hf
        have h' : (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target := h.2
        rwa [(chartAt FourSpace c).left_inv hfc] at h'
      rw [heatNormalFrameTensorLift,
        ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
      change (0 : CovariantCoordinates 2) =
        frameTensor _ (heatCompactTensorLift B T (chartAt FourSpace c f.base))
      rw [heatCompactTensorLift, ite_eq_right hz]
      funext a
      simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · rw [heatNormalFrameTensorLift,
        ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hfc)]

local instance heatNormalChartTensorCompact [CompactSpace M] : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalTensor_L2_realization [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] [Nonempty M] {o : FrameOrientation g}
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 2) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source)
    (ha : ∀ z i j, T z ![j,i] = -T z ![i,j]) :
    let F : C(FrameBundle g, TwoTensorEuclidean) :=
      ⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c C T f),
        (PiLp.continuous_toLp 2 _).comp
          (heatNormalFrameTensorLift_continuous g c C T hCt hT hc hs)⟩
    twoFormTensorL2 (twoFormFromContinuousTensor (o := o) F) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F := by
  let B := C.trans (chartAt FourSpace c)
  have hBs : tsupport T ⊆ B.source := by rwa [heatNormalChartMap_source C hCt]
  have hBT : ContinuousOn T B.source := hT.mono (by rw [heatNormalChartMap_source C hCt])
  let H := heatCompactTensorLift B T
  have hH : Continuous H := heatCompactTensorLift_continuous B T hBT hc hBs
  have hK : IsCompact (B '' tsupport T) := hc.image_of_continuousOn (B.continuousOn.mono hBs)
  have hKt : B '' tsupport T ⊆ (chartAt FourSpace c).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (B.map_source (hBs hx)).1
  have hHs := heatCompactTensorLift_tsupport B T hc hBs
  have heq : heatChartTensor g c H hH.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) =
      (⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c C T f),
        (PiLp.continuous_toLp 2 _).comp
          (heatNormalFrameTensorLift_continuous g c C T hCt hT hc hs)⟩ :
        C(FrameBundle g, TwoTensorEuclidean)) := by
    ext f a
    exact congrFun (heatNormalChartTensor_realization C hCt T f).symm a
  simpa only [heq] using heatChartTensor_L2_realization (o := o) c H hH
    (heatCompactTensorLift_skew B T ha) hK hKt hHs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the first covariant derivatives of actual
smooth one-forms, and their Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormGreenCompactFrames_rced384_1 : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneForm_ricci_commutator (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (e : FrameBundle g) (j : Fin 4) :
    (∑ i, (covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![i,j,i] -
      covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![j,i,i])) =
      3 * covariantFieldFramed g u.val e ![j] := by
  have hidx (a b c : Fin 4) : Fin.cons a (Fin.cons b ![c]) = ![a,b,c] := by
    ext k
    fin_cases k <;> rfl
  have hc (i : Fin 4) : covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![i,j,i] -
      covariantFieldFramed g
        (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e ![j,i,i] =
      -(∑ p, frameCurvature g e.base e.frame i j i p *
        covariantFieldFramed g u.val e ![p]) := by
    simpa only [tensorSlotAction_one, curvatureEndomorphism, hidx] using
      u.property.framed_commutator (g := g) e i j ![i]
  simp_rw [hc]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  have hr (a b : Fin 4) : (∑ i, frameCurvature g e.base e.frame i a b i) =
      if a = b then 3 else 0 := frame_algebraic_ricciThree e.frame hRic a b
  calc
    -(∑ p, ∑ i, frameCurvature g e.base e.frame i j i p * covariantFieldFramed g u.val e ![p]) =
        ∑ p, (∑ i, frameCurvature g e.base e.frame i j p i) *
          covariantFieldFramed g u.val e ![p] := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [frameCurvature_last_skew e.frame i j i p]
      ring
    _ = 3 * covariantFieldFramed g u.val e ![j] := by
      simp only [hr j, ite_mul, zero_mul]
      simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The joint one-form amplitudes restrict to the actual radial solver. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section

theorem HeatFamilyOneCoefficients.amplitude_slice (E : HeatFamilyOneCoefficients)
    (m : ℕ) : m ≤ 3 → ∀ q : CoordinateFrameSpace,
      (fun x => E.amplitude m (x, q)) =
        fourHeatOneCoefficient (fun x => E.base.a (x, q)) (fun x => E.base.b (x, q))
          (fun x => E.B (x, q)) (fun x => E.C (x, q)) (fun x => E.base.U (x, q)) m := by
  induction m with
  | zero => intro _ _; rfl
  | succ m ih =>
    intro hm q
    have hrec := ih (by omega) q
    funext x k l
    have hu (a : Fin 4) : ContDiff ℝ 2 (fun z => E.amplitude m z a l) :=
      (E.amplitude_regular m (by omega) a l).of_le (by norm_num)
    have ho : (fun y => -heatFamilyOneOperator E.base.a E.base.b E.B E.C
        (fun z a => E.amplitude m z a l) (y, q) k) =
        (fun y => -fourHeatOneOperator (E.base.a (y, q)) (E.base.b (y, q)) (E.B (y, q)) (E.C (y, q))
          (fun z a => fourHeatOneCoefficient (fun x => E.base.a (x, q))
            (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.base.U (x, q)) m z a l) y k) := by
      funext y
      rw [heatFamilyOneOperator_slice E.base.a E.base.b E.B E.C
        (fun z a => E.amplitude m z a l) hu (y, q) k]
      have he : (fun z a => E.amplitude m (z, q) a l) =
          (fun z a => fourHeatOneCoefficient (fun x => E.base.a (x, q))
            (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) (fun x => E.C (x, q))
              (fun x => E.base.U (x, q)) m z a l) := by
        funext z a
        exact congrArg (fun A : FourSpace → Mat4 => A z a l) hrec
      rw [he]
    change heatFamilyWeightedAverage m E.base.U (fun y => -heatFamilyOneOperator E.base.a E.base.b E.B E.C
      (fun z a => E.amplitude m z a l) y k) (x, q) = _
    rw [heatFamilyWeightedAverage_slice, ho]
    rfl


end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar normal parametrix has the actual delta initial pairing
and may be differentiated under each compactly supported test integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {e : FrameBundle g}

def HeatNormalExtension.scalarCutoff (E : HeatNormalExtension 10 g o e)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  χ x * E.scalarParametrix t x

theorem HeatNormalExtension.scalarCutoff_regular (E : HeatNormalExtension 10 g o e)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) :
    ContDiff ℝ 4 (E.scalarCutoff χ t) := hχ.mul (E.scalarParametrix_regular t)

theorem HeatNormalExtension.scalarCutoff_support (E : HeatNormalExtension 10 g o e)
    (χ : FourSpace → ℝ) (t : ℝ) : tsupport (E.scalarCutoff χ t) ⊆ tsupport χ :=
  tsupport_mul_subset_left

end
end PositiveEinsteinFour.Geometry
end


section

/-! The residual of every member of the common family is the same jointly
continuous last transport coefficient, times its explicit Gaussian factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.amplitude_family (N : HeatCommonNormalMember g o c E r e)
    (m : ℕ) (hm : m ≤ 3) :
    N.extension.amplitude m = fun x => E.amplitude m (x, frameCoordinateState g c e) := by
  unfold HeatNormalBundleExtension.amplitude
  rw [N.a_family, N.b_family, N.B_family, N.C_family, N.U_family]
  exact (E.amplitude_slice m hm _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-one Weitzenböck equation for Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

include o in
theorem oneFormDivergence_gradient (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (e : FrameBundle g) (j : Fin 4) :
    scalarGradient g (oneFormDivergence g u) e j =
      ∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![j,i,i] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow j).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic j e
  have hidx (i : Fin 4) : Fin.cons j ![i,i] = ![j,i,i] := by
    ext k
    fin_cases k <;> rfl
  have hd : HasDerivAt
      (fun t => ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![i,i])
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (γ 0) ![j,i,i]) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [hidx] using u.property.derivative.parallel_derivative (g := g) γ 0 j
      (d.curve_continuous j e).continuousAt (d.parallelCurve j 0 e) ![i,i]
  have heq : (fun t => ∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) (γ t) ![i,i]) =
      (fun t => oneFormDivergence g u (γ t).base) := by
    funext t
    exact (oneFormDivergence_eq_frame u (γ t)).symm
  rw [heq] at hd
  have hg := actual_scalarValue_parallel_derivative g (oneFormDivergence_smooth (g := g) u) γ 0 j
    (d.curve_continuous j e).continuousAt (d.parallelCurve j 0 e)
  have h := hg.unique hd
  simpa only [hzero] using h

theorem smoothOneForm_Weitzenbock (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (e : FrameBundle g) (j : Fin 4) :
    covariantFieldFramed g (smoothOneFormHodgeLaplacian (o := o) u).val e ![j] =
      -(∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,i,j]) + 3 * covariantFieldFramed g u.val e ![j] := by
  have hsub := congrFun (covariantFieldFramed_add (g := g)
    (smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) u)).val
    (-((smoothScalarDifferential g (smoothOneFormDivergence g u)).val)) e) ![j]
  have hneg := congrFun (covariantFieldFramed_smul (g := g) (-1 : ℝ)
    (smoothScalarDifferential g (smoothOneFormDivergence g u)).val e) ![j]
  have hc := oneForm_ricci_commutator hRic u e j
  rw [Finset.sum_sub_distrib] at hc
  change covariantFieldFramed g
    ((smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) u)).val +
      -(smoothScalarDifferential g (smoothOneFormDivergence g u)).val) e ![j] = _
  rw [hsub]
  simp only [Pi.add_apply]
  rw [← neg_one_smul ℝ ((smoothScalarDifferential g (smoothOneFormDivergence g u)).val),
    hneg, smoothTwoFormCodifferentialField_component]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [smoothScalarDifferential_framed]
  change -(∑ i, twoFormFramedCovariantDerivative o (smoothOneFormExterior (o := o) u).val e ![i,i,j]) +
    (-1 : ℝ) * scalarGradient g (oneFormDivergence g u) e j = _
  simp_rw [smoothOneFormExterior_covariant hRic, Finset.sum_sub_distrib]
  rw [oneFormDivergence_gradient (o := o) hRic]
  linarith only [hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form transport operator is the actual geometric Hodge Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatNormalFrameData.actual_one_operator_at (D : HeatNormalFrameData g o c e)
    (hRic : RicciThree g) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalOneFirst D x) (heatNormalOneZero D x)
      (heatNormalOneFormValue c D.point u) x k =
      heatNormalOneFormValue c D.point (smoothOneFormHodgeLaplacian (o := o) u) x k := by
  have hdet : (D.point x).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hA (i j l : Fin 4) : DifferentiableAt ℝ
      (fun y => heatNormalFrameConnection g c D.point i y j l) x :=
    (heatNormalFrameConnection_contDiffAt 1 g c D.point x hP (D.in_chart x hx) hdet i j l).differentiableAt one_ne_zero
  have hu (l : Fin 4) : ContDiffAt ℝ 2 (fun y => heatNormalOneFormValue c D.point u y l) x :=
    heatNormalOneFormValue_regular 2 c D.point u x hP (D.in_chart x hx) l
  have ha (i j : Fin 4) : (heatNormalMetric g o e x)⁻¹ i j =
      (heatNormalMetric g o e x)⁻¹ j i :=
    congrArg (fun A : Mat4 => A j i) (heatNormalInverse_symm g o e x)
  unfold heatNormalOneFirst heatNormalOneZero
  rw [← fourHeatOneCovariantOperator_eq _ _ _ _ _ x ha hA hu k]
  unfold fourHeatOneCovariantOperator
  rw [D.oneRough_components_at x hx hP hs hd u k]
  have hv : (∑ l : Fin 4, ((3 : ℝ) • (1 : Mat4)) k l *
      heatNormalOneFormValue c D.point u x l) = 3 * heatNormalOneFormValue c D.point u x k := by
    simp [Matrix.one_apply, mul_ite]
  rw [hv, D.oneValue_as_actual u x hx k,
    D.oneValue_as_actual (smoothOneFormHodgeLaplacian (o := o) u) x hx k]
  exact (smoothOneForm_Weitzenbock hRic u (D.frame x hx) k).symm

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

/-! Actual exact and coexact smooth one-form eigensections and their
orthogonality. The coexact eigenspaces are finite images of the proved
two-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothOneFormWrap : smoothCovariantFields M 1 →ₗ[ℝ] SmoothL2OneForm o where
  toFun u := ⟨u⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def smoothOneFormL2Linear : smoothCovariantFields M 1 →ₗ[ℝ] OneFormL2 o :=
  smoothOneFormToL2.toLinearMap.comp smoothOneFormWrap

end
end PositiveEinsteinFour.Geometry
end


section

/-! Isometric frame-coordinate realization of the actual one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_16 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def smoothOneFormEuclideanValue (u : smoothCovariantFields M 1) : C(FrameBundle g, FourSpace) where
  toFun e := WithLp.toLp 2 (fun i : Fin 4 => covariantFieldFramed g u.val e ![i])
  continuous_toFun := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
    (continuous_apply ![i]).comp u.property.continuous_framed))

def smoothOneFormFrameLinear : SmoothL2OneForm o →ₗ[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) where
  toFun u := ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothOneFormEuclideanValue (g := g) u.toSmooth)
  map_add' u v := by
    have he : smoothOneFormEuclideanValue (g := g) (u + v).toSmooth =
        smoothOneFormEuclideanValue (g := g) u.toSmooth + smoothOneFormEuclideanValue (g := g) v.toSmooth := by
      ext e i
      exact congrFun (covariantFieldFramed_add (g := g) u.toSmooth.val v.toSmooth.val e) ![i]
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_add]
  map_smul' r u := by
    have he : smoothOneFormEuclideanValue (g := g) (r • u).toSmooth =
        r • smoothOneFormEuclideanValue (g := g) u.toSmooth := by
      ext e i
      exact congrFun (covariantFieldFramed_smul (g := g) r u.toSmooth.val e) ![i]
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_smul]
    rfl

theorem smoothOneFormFrameLinear_norm (u : SmoothL2OneForm o) :
    ‖smoothOneFormFrameLinear u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← real_inner_self_eq_norm_sq]
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
    (smoothOneFormEuclideanValue (g := g) u.toSmooth)
  change (∫ e, inner ℝ ((smoothOneFormFrameLinear u : Lp FourSpace 2 (canonicalFrameMeasure g o)) e)
      ((smoothOneFormFrameLinear u : Lp FourSpace 2 (canonicalFrameMeasure g o)) e)
      ∂canonicalFrameMeasure g o) = smoothOneFormL2Pairing u.toSmooth u.toSmooth
  unfold smoothOneFormL2Pairing
  apply integral_congr_ae
  filter_upwards [he] with e he
  change (smoothOneFormFrameLinear u : FrameBundle g → FourSpace) e = _ at he
  rw [he]
  simp only [PiLp.inner_apply, smoothOneFormEuclideanValue, ContinuousMap.coe_mk,
    Real.inner_apply]

def smoothOneFormFrameL2 : SmoothL2OneForm o →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) :=
  smoothOneFormFrameLinear.mkContinuous 1 (fun u => by rw [one_mul, smoothOneFormFrameLinear_norm])

def oneFormFrameL2 : OneFormL2 o →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) :=
  (smoothOneFormFrameL2 (o := o)).fromCompletion

theorem oneFormFrameL2_smooth (u : smoothCovariantFields M 1) :
    oneFormFrameL2 (smoothOneFormL2Linear (o := o) u) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothOneFormEuclideanValue (g := g) u) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ (⟨u⟩ : SmoothL2OneForm o)

theorem oneFormFrameL2_norm (u : OneFormL2 o) : ‖oneFormFrameL2 u‖ = ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (oneFormFrameL2.continuous.norm) continuous_norm) ?_
  intro v
  change ‖oneFormFrameL2 (smoothOneFormToL2 v)‖ = ‖smoothOneFormToL2 v‖
  rw [smoothOneFormToL2.norm_map]
  have hv := ContinuousLinearMap.fromCompletion_apply_coe (smoothOneFormFrameL2 (o := o)) v
  change oneFormFrameL2 (smoothOneFormToL2 v) = smoothOneFormFrameLinear v at hv
  rw [hv, smoothOneFormFrameLinear_norm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The adjoint of the actual isometric frame realization reconstructs one-form
L2 sections from continuous frame data. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
local instance instCompactSpaceFrameBundle_18 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem oneFormFrameL2_inner (u v : OneFormL2 o) :
    inner ℝ (oneFormFrameL2 u) (oneFormFrameL2 v) = inner ℝ u v := by
  have h := norm_add_sq_real (oneFormFrameL2 u) (oneFormFrameL2 v)
  rw [← map_add, oneFormFrameL2_norm, oneFormFrameL2_norm, oneFormFrameL2_norm] at h
  nlinarith [norm_add_sq_real u v]

def oneFormFromFrameL2 : Lp FourSpace 2 (canonicalFrameMeasure g o) →L[ℝ] OneFormL2 o :=
  (oneFormFrameL2 (o := o)).adjoint

theorem oneFormFromFrameL2_pairing (F : Lp FourSpace 2 (canonicalFrameMeasure g o))
    (u : OneFormL2 o) :
    inner ℝ (oneFormFromFrameL2 F) u = inner ℝ F (oneFormFrameL2 u) :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem oneFormFromFrameL2_left_inverse (u : OneFormL2 o) :
    oneFormFromFrameL2 (oneFormFrameL2 u) = u := by
  apply ext_inner_right ℝ
  intro v
  rw [oneFormFromFrameL2_pairing, oneFormFrameL2_inner]

def oneFormFromContinuous : C(FrameBundle g, FourSpace) →L[ℝ] OneFormL2 o :=
  (oneFormFromFrameL2 (o := o)).comp (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ)

theorem oneFormFromContinuous_smooth (u : smoothCovariantFields M 1) :
    oneFormFromContinuous (smoothOneFormEuclideanValue (g := g) u) =
      smoothOneFormL2Linear (o := o) u := by
  change oneFormFromFrameL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _) = _
  rw [← oneFormFrameL2_smooth, oneFormFromFrameL2_left_inverse]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact finite-regularity normal-frame amplitude determines an
actual element of the global one-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalOneCoordinates_continuousOn (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hP : ContDiffOn ℝ 2 D.point C.source)
    (hD : C.source ⊆ ball 0 D.radius) (a : FourSpace → FourSpace)
    (ha : ContDiff ℝ 2 a) : ContinuousOn (heatNormalOneCoordinates D a) C.source := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro v
  exact (heatNormalOneCoordinates_regular D a x (hD hx)
    (hP.contDiffAt (C.open_source.mem_nhds hx)) ha.contDiffAt v).continuousAt

def heatNormalOneAmplitude (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : C(FrameBundle g, FourSpace) :=
  ⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
      (heatNormalOneFrameLift_continuous g c C _ hCt
        (heatNormalOneCoordinates_continuousOn D C hP hD a ha)
        (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCoordinates_support D a))
        ((heatNormalOneCoordinates_support D a).trans hs))))⟩

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalOneAmplitudeL2 (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : OneFormL2 o :=
  oneFormFromContinuous (heatNormalOneAmplitude D C hCt hP hD a ha hc hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous one-form chart data and their genuine smooth realizations. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M}

def heatOneChart (g : SmoothMetric M) (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : ContinuousOn F (chartAt FourSpace c).target)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ (chartAt FourSpace c).target) :
    C(FrameBundle g, FourSpace) :=
  ⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
      (heatNormalOneFrameLift_continuous g c (chartAt FourSpace c).symm F
        (fun _ h => h) hF hc hs)))⟩

theorem heatOneChart_smooth
    (c : M) (F : FourSpace → CovariantCoordinates 1)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    heatOneChart g c F hF.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) =
      smoothOneFormEuclideanValue (g := g) (oneFormChartTest g c F hF hK hKt hFs) := by
  apply ContinuousMap.ext
  intro f
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hf : f.base ∈ (chartAt FourSpace c).source
  · change heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i] =
      covariantFieldFramed g (oneFormChartTest g c F hF hK hKt hFs).val f ![i]
    rw [heatNormalOneFrameLift, ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hf)]
    rw [heat_covariantField_chart g _ c f hf,
      oneFormChartTest_coordinates c F hF hK hKt hFs _ ((chartAt FourSpace c).map_source hf)]
    rfl
  · have hz := oneFormChartTest_zero_off (g := g) c F hF hK hKt hFs f.base (by
      rintro ⟨z, hz, hzf⟩
      exact hf (hzf ▸ (chartAt FourSpace c).map_target (hKt hz)))
    change heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i] =
      covariantFieldFramed g (oneFormChartTest g c F hF hK hKt hFs).val f ![i]
    rw [heatNormalOneFrameLift, ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hf)]
    rw [covariantFieldFramed, covariantFieldCoordinates_center, hz, frameTensor_zero_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal one-form lift preserves the actual orthonormal fiber norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneAmplitude_norm_sq
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (f : FrameBundle g) (hf : f.base ∈ C.target) :
    ‖heatNormalOneAmplitude D C hCt hP hD a ha hc hs f‖ ^ 2 =
      ‖a (C.symm f.base)‖ ^ 2 := by
  let x := C.symm f.base
  have hx : x ∈ C.source := C.map_target hf
  have hxb := hD hx
  have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
    rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
  have hF := frameChartMatrix_normalizes g c f (hCt hf)
  rw [← hbase] at hF
  have hi : (D.point x).2⁻¹ * (D.point x).2 = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (heatNormalFrame_matrix_nondegenerate D hxb))
  have hback : frameTensor (D.point x).2 (heatNormalOneCoordinates D a x) =
      fun v => a x (v 0) := by
    unfold heatNormalOneCoordinates
    rw [← frameTensor_mul, hi, frameTensor_one]
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i] ^ 2) = _
  rw [← oneForm_squareNorm, heatNormalOneFrameLift, ite_eq_left hf]
  change frameTensorPairing
    (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (fun v => a x (v 0))))
    (frameTensor (frameChartMatrix g c f) (heatNormalOneCoordinates D a x)) = _
  rw [heat_normal_one_pairing _ _ _ (D.orthonormal x hxb) hF, hback]
  change frameTensorSquareNorm (fun v => a x (v 0)) = _
  rw [oneForm_squareNorm, EuclideanSpace.real_norm_sq_eq]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform control of compact chart tensors in the frame-bundle norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourSpace_norm_le_sum (v : Fin 4 → ℝ) :
    ‖(WithLp.toLp 2 v : FourSpace)‖ ≤ ∑ i, |v i| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => |v i|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mp
  simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M}

local instance heatOneChartBoundCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatOneChart_bound (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (F : FourSpace → CovariantCoordinates 1)
      (hF : ContinuousOn F (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
      (r : ℝ), 0 ≤ r → (∀ z a, |F z a| ≤ r) →
      ‖heatOneChart g c F hF
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)‖ ≤ B * r := by
  let L : Set (FrameBundle g) := (fun f => f.base) ⁻¹' ((chartAt FourSpace c).symm '' K)
  have hLc : IsCompact L :=
    ((hK.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hKt)).isClosed.preimage
      (continuous_frameBase g)).isCompact
  have hLs (f : FrameBundle g) (hf : f ∈ L) : f.base ∈ (chartAt FourSpace c).source := by
    obtain ⟨z, hz, he⟩ := hf
    change (chartAt FourSpace c).symm z = f.base at he
    rw [← he]
    exact (chartAt FourSpace c).map_target (hKt hz)
  have hcont : ContinuousOn (fun f : FrameBundle g => tensorTransportWeight 1 (frameChartMatrix g c f)) L := by
    intro f hf
    exact ((tensorTransportWeight_continuous 1).continuousAt.comp
      (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j =>
        frameChartMatrix_continuousAt g c f (hLs f hf) i j)))).continuousWithinAt
  obtain ⟨b, hb⟩ := (hLc.image_of_continuousOn hcont).isBounded.exists_norm_le
  let B := (Fintype.card (Fin 4) : ℝ) * max b 0
  refine ⟨B, mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _), ?_⟩
  intro F hF hFs r hr hFr
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) hr)).mpr
  intro f
  by_cases hf : f ∈ L
  · have hw : tensorTransportWeight 1 (frameChartMatrix g c f) ≤ max b 0 :=
      (le_abs_self _).trans ((hb _ ⟨f, hf, rfl⟩).trans (le_max_left _ _))
    change ‖(WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]) : FourSpace)‖ ≤ _
    rw [heatNormalOneFrameLift, ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hLs f hf)]
    refine (fourSpace_norm_le_sum _).trans ?_
    calc
      _ ≤ ∑ _a : Fin 4, tensorTransportWeight 1 (frameChartMatrix g c f) * r :=
        Finset.sum_le_sum (fun a _ => frameTensor_abs_le_weight _ _ r hr (hFr _) ![a])
      _ = (Fintype.card (Fin 4) : ℝ) * tensorTransportWeight 1 (frameChartMatrix g c f) * r := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ B * r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)) hr
  · have hz : heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f = 0 := by
      apply not_ne_iff.mp
      intro hn
      obtain ⟨z, hz, he⟩ := heatNormalOneFrameLift_support g c (chartAt FourSpace c).symm F hn
      exact hf ⟨z, hFs hz, he⟩
    change ‖(WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]) : FourSpace)‖ ≤ _
    simp only [hz, Pi.zero_apply]
    change ‖(0 : FourSpace)‖ ≤ _
    rw [norm_zero]
    simpa using mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card (Fin 4))) (le_max_right b 0)) hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous one-form chart tensors are limits of actual
smooth one-form frame tensors in the uniform norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance heatOneChartApproxCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [CompactSpace M] in
theorem heatOneChart_sub (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (F H : FourSpace → CovariantCoordinates 1)
    (hF : ContinuousOn F (chartAt FourSpace c).target)
    (hH : ContinuousOn H (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (hHs : tsupport H ⊆ K)
    (hDs : tsupport (H - F) ⊆ K) :
    heatOneChart g c (H - F) (hH.sub hF)
      (hK.of_isClosed_subset (isClosed_tsupport _) hDs) (hDs.trans hKt) =
      heatOneChart g c H hH (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) -
      heatOneChart g c F hF (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) := by
  classical
  apply ContinuousMap.ext
  intro f
  apply WithLp.ofLp_injective 2
  funext i
  change heatNormalOneFrameLift g c (chartAt FourSpace c).symm (H - F) f ![i] =
    heatNormalOneFrameLift g c (chartAt FourSpace c).symm H f ![i] -
      heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]
  by_cases hf : f.base ∈ (chartAt FourSpace c).symm.target
  · simp only [heatNormalOneFrameLift, ite_eq_left hf, Pi.sub_apply]
    exact frameTensor_sub _ _ _ ![i]
  · simp only [heatNormalOneFrameLift, ite_eq_right hf, Pi.zero_apply, sub_self]

theorem heatOneChart_smooth_approx (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : Continuous F)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : smoothCovariantFields M 1,
      ‖smoothOneFormEuclideanValue (g := g) u - heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)‖ < ε := by
  obtain ⟨B, hB, hbound⟩ := heatOneChart_bound (g := g) c hK hKt
  let r := ε / (B + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  obtain ⟨H, hH, hdist, hHsF⟩ := hF.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => r) continuous_const (fun _ => hr)
  have hHs : tsupport H ⊆ K := (closure_mono hHsF).trans hFs
  have hDs : tsupport (H - F) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    have hH0 : H z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hHs h))
    have hF0 : F z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hFs h))
    exact hz (by simp only [Pi.sub_apply, hH0, hF0, sub_self])
  refine ⟨oneFormChartTest g c H hH.contDiffOn hK hKt hHs, ?_⟩
  rw [← heatOneChart_smooth c H hH.contDiffOn hK hKt hHs,
    ← heatOneChart_sub c hK hKt F H hF.continuousOn hH.continuous.continuousOn hFs hHs hDs]
  have hb := hbound (H - F) (hH.continuous.continuousOn.sub hF.continuousOn) hDs r hr.le
    (fun z a => (norm_le_pi_norm (H z - F z) a).trans
      (by simpa only [dist_eq_norm] using (hdist z).le))
  have hbr : B * r < ε := by
    have h := (mul_div_cancel₀ ε (show B + 1 ≠ 0 by positivity))
    change (B + 1) * r = ε at h
    nlinarith
  exact hb.trans_lt hbr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous chart one-forms lie in the actual one-form L2 completion. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
local instance instCompactSpaceFrameBundle_22 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatOneChart_L2_realization (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : Continuous F)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    oneFormFrameL2 (oneFormFromContinuous (o := o)
      (heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt))) =
    ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
      (heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)) := by
  let A := (oneFormFrameL2 (o := o)).comp (oneFormFromContinuous (o := o))
  let B := ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (E := FourSpace)
  have hclosed : IsClosed {T | A T = B T} := isClosed_eq A.continuous B.continuous
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨u, hu⟩ := heatOneChart_smooth_approx (g := g) c F hF hK hKt hFs ε hε
  refine ⟨smoothOneFormEuclideanValue (g := g) u, ?_, ?_⟩
  · change oneFormFrameL2 (oneFormFromContinuous (smoothOneFormEuclideanValue (g := g) u)) = _
    rw [oneFormFromContinuous_smooth, oneFormFrameL2_smooth]
  · simpa only [dist_eq_norm, norm_sub_rev] using hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact coordinate changes for continuous one-tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatCompactOneLift (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) (z : FourSpace) : CovariantCoordinates 1 := by
  classical
  exact if z ∈ C.target then T (C.symm z) else 0

theorem heatCompactOneLift_support (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) :
    support (heatCompactOneLift C T) ⊆ C '' tsupport T := by
  classical
  intro z hz
  by_cases h : z ∈ C.target
  · refine ⟨C.symm z, subset_closure ?_, C.right_inv h⟩
    simpa only [heatCompactOneLift, ite_eq_left h, mem_support] using hz
  · exact False.elim (hz (by simp only [heatCompactOneLift, ite_eq_right h]))

theorem heatCompactOneLift_tsupport (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) (hc : HasCompactSupport T)
    (hs : tsupport T ⊆ C.source) :
    tsupport (heatCompactOneLift C T) ⊆ C '' tsupport T :=
  closure_minimal (heatCompactOneLift_support C T)
    (hc.image_of_continuousOn (C.continuousOn.mono hs)).isClosed

theorem heatCompactOneLift_continuous (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatCompactOneLift C T) := by
  classical
  have hK := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ C.target
  · have h := (hT.continuousAt (C.open_source.mem_nhds (C.map_target hz))).comp
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hz))
    apply h.congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hz] with w hw
    exact ite_eq_left hw
  · have hzK : z ∉ C '' tsupport T := by
      rintro ⟨x, hx, rfl⟩
      exact hz (C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 1))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    exact not_ne_iff.mp (fun hn => hw (heatCompactOneLift_support C T hn))


end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal one-form parametrix columns and their actual time derivatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneCutoffParametrix (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (x : FourSpace) (k l : Fin 4) : ℝ := χ x * heatNormalOneParametrix E t x k l

theorem heatNormalOneParametrix_space_regular (E : HeatNormalOneExtension D)
    (t : ℝ) (k l : Fin 4) : ContDiff ℝ 4 (fun x => heatNormalOneParametrix E t x k l) := by
  have hP := (((E.amplitude_regular 0 (by omega) k l).add
    ((contDiff_const (c := t)).mul (E.amplitude_regular 1 (by omega) k l))).add
    ((contDiff_const (c := t ^ 2)).mul (E.amplitude_regular 2 (by omega) k l))).add
    ((contDiff_const (c := t ^ 3)).mul (E.amplitude_regular 3 (by omega) k l))
  exact ((fourHeatGaussian_smooth t).of_le (by norm_num)).mul hP

def heatNormalOneCutoffColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => heatNormalOneCutoffParametrix E χ t x k l)

theorem heatNormalOneCutoffColumn_regular (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 4) :
    ContDiff ℝ 4 (heatNormalOneCutoffColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  exact hχ.mul (heatNormalOneParametrix_space_regular E t k l)

theorem heatNormalOneCutoffColumn_support (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) :
    tsupport (heatNormalOneCutoffColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalOneCutoffColumn, WithLp.ofLp_toLp, heatNormalOneCutoffParametrix,
    hχ, zero_mul, Pi.zero_apply, WithLp.ofLp_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalOneGlobalColumn (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneAmplitudeL2 D C hCt hP hD (heatNormalOneCutoffColumn E χ t l)
    ((heatNormalOneCutoffColumn_regular E χ hχ t l).of_le (by norm_num))
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCutoffColumn_support E χ t l))
    ((heatNormalOneCutoffColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal parametrix columns as elements of the
global two-form Hilbert space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalCutoffColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => heatNormalCutoffParametrix E χ t x k l)

theorem heatNormalCutoffColumn_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 2 (heatNormalCutoffColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  exact hχ.mul (heatNormalBundleParametrix_space_regular E t k l)

theorem heatNormalCutoffColumn_support (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) :
    tsupport (heatNormalCutoffColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalCutoffColumn, WithLp.ofLp_toLp, heatNormalCutoffParametrix,
    hχ, zero_mul, Pi.zero_apply, WithLp.ofLp_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalGlobalParametrixColumn (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D C hCt hP hD (heatNormalCutoffColumn E χ t l)
    (heatNormalCutoffColumn_regular E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
    ((heatNormalCutoffColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express compact normal-coordinate tensors in one actual smooth
manifold chart, without changing their frame-bundle values. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {c : M}

omit [T3Space M] in
theorem heatNormalOneChart_realization (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 1) (f : FrameBundle g) :
    heatNormalOneFrameLift g c C T f =
    heatNormalOneFrameLift g c (chartAt FourSpace c).symm
      (heatCompactOneLift (C.trans (chartAt FourSpace c)) T) f := by
  classical
  let B := C.trans (chartAt FourSpace c)
  by_cases hf : f.base ∈ C.target
  · have hfc := hCt hf
    have hz : chartAt FourSpace c f.base ∈ B.target := by
      change chartAt FourSpace c f.base ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target
      exact ⟨(chartAt FourSpace c).map_source hfc, by rwa [(chartAt FourSpace c).left_inv hfc]⟩
    rw [heatNormalOneFrameLift, ite_eq_left hf, heatNormalOneFrameLift,
      ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (heatCompactOneLift B T (chartAt FourSpace c f.base))
    rw [heatCompactOneLift, ite_eq_left hz]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (T (C.symm ((chartAt FourSpace c).symm (chartAt FourSpace c f.base))))
    rw [(chartAt FourSpace c).left_inv hfc]
  · rw [heatNormalOneFrameLift, ite_eq_right hf]
    by_cases hfc : f.base ∈ (chartAt FourSpace c).source
    · have hz : chartAt FourSpace c f.base ∉ B.target := by
        intro h
        apply hf
        have h' : (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target := h.2
        rwa [(chartAt FourSpace c).left_inv hfc] at h'
      rw [heatNormalOneFrameLift,
        ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
      change (0 : CovariantCoordinates 1) =
        frameTensor _ (heatCompactOneLift B T (chartAt FourSpace c f.base))
      rw [heatCompactOneLift, ite_eq_right hz]
      funext a
      simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · rw [heatNormalOneFrameLift,
        ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hfc)]

local instance heatNormalOneChartCompact [CompactSpace M] : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalOneTensor_L2_realization [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] [Nonempty M] {o : FrameOrientation g}
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 1) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source)
 :
    let F : C(FrameBundle g, FourSpace) :=
      ⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C T f ![i]),
        (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
          (heatNormalOneFrameLift_continuous g c C T hCt hT hc hs)))⟩
    oneFormFrameL2 (oneFormFromContinuous (o := o) F) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F := by
  let B := C.trans (chartAt FourSpace c)
  have hBs : tsupport T ⊆ B.source := by rwa [heatNormalChartMap_source C hCt]
  have hBT : ContinuousOn T B.source := hT.mono (by rw [heatNormalChartMap_source C hCt])
  let H := heatCompactOneLift B T
  have hH : Continuous H := heatCompactOneLift_continuous B T hBT hc hBs
  have hK : IsCompact (B '' tsupport T) := hc.image_of_continuousOn (B.continuousOn.mono hBs)
  have hKt : B '' tsupport T ⊆ (chartAt FourSpace c).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (B.map_source (hBs hx)).1
  have hHs := heatCompactOneLift_tsupport B T hc hBs
  have heq : heatOneChart g c H hH.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) =
      (⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C T f ![i]),
        (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
          (heatNormalOneFrameLift_continuous g c C T hCt hT hc hs)))⟩ :
        C(FrameBundle g, FourSpace)) := by
    ext f i
    exact congrFun (heatNormalOneChart_realization C hCt T f).symm ![i]
  simpa only [heq] using heatOneChart_L2_realization (o := o) c H hH
    hK hKt hHs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact norm integral for the actual compact normal amplitude, obtained
by smooth approximation inside the genuine one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance heatNormalOneExactCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatNormalOneExactProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatNormalOneAmplitude_L2_realization
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    oneFormFrameL2 (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
        (heatNormalOneAmplitude D C hCt hP hD a ha hc hs) := by
  exact heatNormalOneTensor_L2_realization C hCt (heatNormalOneCoordinates D a)
    (heatNormalOneCoordinates_continuousOn D C hP hD a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCoordinates_support D a))
    ((heatNormalOneCoordinates_support D a).trans hs)

theorem heatNormalOneAmplitudeL2_norm_sq_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    ‖heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
  let F := heatNormalOneAmplitude D C hCt hP hD a ha hc hs
  let ψ := fun x => ‖a x‖ ^ 2
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change ‖a x‖ ^ 2 = 0
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.norm.pow 2).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : ‖F f‖ ^ 2 = heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalOneAmplitude_norm_sq C hE hCt hP hD a ha hc hs f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : F f = 0 := by
        change WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) = _
        simp only [heatNormalOneFrameLift, ite_eq_right hf]
        rfl
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      simp only [heatNormalScalarLift, ite_eq_right hf]
  have hex : oneFormFrameL2 (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F :=
    heatNormalOneAmplitude_L2_realization C hCt hP hD a ha hc hs
  have hcalc : ‖heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
    calc
      _ = ‖ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F‖ ^ 2 := by
        rw [← hex, oneFormFrameL2_norm]
      _ = ∫ f, ‖F f‖ ^ 2 ∂canonicalFrameMeasure g o := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F] with f hf
        rw [hf, real_inner_self_eq_norm_sq]
      _ = ∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g := by
        simp_rw [heq]
        rw [canonicalFrameMeasure_integral_base g o _ hLi]
      _ = _ := by
        rw [heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hs)]
  exact hcalc

end
end PositiveEinsteinFour.Geometry
end


section

/-! Correct normalization of the compact parametrix for the actual
probability measure used by the spectral Hodge heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

def heatNormalizedParametrixColumn (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ •
    heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary connection traces in degrees one and two cancel in the
four-dimensional de Rham supertrace. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatTwoFormConnectionMatrix_trace (A : Mat4) :
    (heatTwoFormConnectionMatrix A).trace = 0 := by
  rw [heatTwoFormConnectionMatrix_infinitesimal]
  simp [twoFormInfinitesimalMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem heatTwoFormConnectionMatrix_square_trace (A : Mat4) (hA : Aᵀ = -A) :
    (heatTwoFormConnectionMatrix A * heatTwoFormConnectionMatrix A).trace =
      2 * (A * A).trace := by
  have h := twoFormInfinitesimalMatrix_euler_trace (twoFormExtract A)
  rw [twoFormMatrix_extract A hA] at h
  rw [heatTwoFormConnectionMatrix_infinitesimal]
  linarith only [h]

theorem heatTwoFormConnectionMatrix_product_trace (A B : Mat4)
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) :
    (heatTwoFormConnectionMatrix A * heatTwoFormConnectionMatrix B).trace =
      2 * (A * B).trace := by
  have hAB : (A + B)ᵀ = -(A + B) := by
    rw [Matrix.transpose_add, hA, hB, neg_add]
  have h := heatTwoFormConnectionMatrix_square_trace (A + B) hAB
  have hm : heatTwoFormConnectionMatrix (A + B) =
      heatTwoFormConnectionMatrix A + heatTwoFormConnectionMatrix B :=
    heatConnectionMatrixLinear.map_add A B
  rw [hm] at h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add] at h
  rw [heatTwoFormConnectionMatrix_square_trace A hA,
    heatTwoFormConnectionMatrix_square_trace B hB,
    Matrix.trace_mul_comm (heatTwoFormConnectionMatrix B) (heatTwoFormConnectionMatrix A),
    Matrix.trace_mul_comm B A] at h
  linarith only [h]

theorem heatFour_skew_trace (A : Mat4) (hA : Aᵀ = -A) : A.trace = 0 := by
  have h := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h
  linarith only [h]

theorem heatOneConnectionZero_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4) (x : FourSpace)
    (hA : ∀ i, (A i x).trace = 0)
    (hD : ∀ i j, (matrixPartial (A i) j x).trace = 0) :
    (fourHeatOneConnectionZero a b A V x).trace =
      V.trace - ∑ i, ∑ j, a i j * (A j x * A i x).trace := by
  change (V + (∑ i, b i • A i x) -
    ∑ i, ∑ j, a i j • (matrixPartial (A i) j x + A j x * A i x)).trace = _
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hA, hD, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

theorem heatTwoConnectionZero_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6) (x : FourSpace)
    (hA : ∀ i, (A i x).trace = 0)
    (hD : ∀ i j, (heatSixPartial (A i) j x).trace = 0) :
    (fourHeatConnectionZero a b A V x).trace =
      V.trace - ∑ i, ∑ j, a i j * (A j x * A i x).trace := by
  change (V + (∑ i, b i • A i x) -
    ∑ i, ∑ j, a i j • (heatSixPartial (A i) j x + A j x * A i x)).trace = _
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hA, hD, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Gaussian-free column and its uniform density-weighted bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalPolynomialColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => χ x * fourHeatPolynomial (fun m y => E.amplitude m y k l) t x)

theorem heatNormalPolynomialColumn_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 6) :
    Continuous (fun z : ℝ × FourSpace => heatNormalPolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp continuous_snd).mul
    (fourHeatPolynomial_joint_continuous _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatNormalCutoffColumn_gaussian (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalCutoffColumn E χ t l x =
      fourHeatGaussian t x • heatNormalPolynomialColumn E χ t l x := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * (fourHeatGaussian t x * _) = fourHeatGaussian t x * (χ x * _)
  unfold fourHeatBundlePolynomial fourHeatPolynomial
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Trace and actual coordinate differentiation commute for the two
connection representations used in the de Rham heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatFourTrace_partial (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ k, DifferentiableAt ℝ (fun y => A y k k) x) (i : Fin 4) :
    partialDeriv (fun y => (A y).trace) i x = (matrixPartial A i x).trace := by
  unfold Matrix.trace Matrix.diag
  exact heat_partial_finite_sum (fun k y => A y k k) x hA i

theorem heatSixTrace_partial (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k, DifferentiableAt ℝ (fun y => A y k k) x) (i : Fin 4) :
    partialDeriv (fun y => (A y).trace) i x = (heatSixPartial A i x).trace := by
  unfold Matrix.trace Matrix.diag
  exact heat_partial_finite_sum (fun k y => A y k k) x hA i

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.oneConnection_partial_trace (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ Metric.ball 0 D.radius) (i j : Fin 4)
    (hd : ∀ k, DifferentiableAt ℝ (fun y => heatNormalFrameConnection g c D.point i y k k) x) :
    (matrixPartial (heatNormalFrameConnection g c D.point i) j x).trace = 0 := by
  rw [← heatFourTrace_partial _ x hd j]
  have hz : (fun y => (heatNormalFrameConnection g c D.point i y).trace) =ᶠ[𝓝 x]
      fun _ => 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact heatFour_skew_trace _ (D.connection_skew y hy i)
  rw [fourHeat_partial_germ hz j]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]

theorem HeatNormalFrameData.twoConnection_partial_trace (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (i j : Fin 4)
    (hd : ∀ k, DifferentiableAt ℝ (fun y => heatTwoFormConnection g c D.point i y k k) x) :
    (heatSixPartial (heatTwoFormConnection g c D.point i) j x).trace = 0 := by
  rw [← heatSixTrace_partial _ x hd j]
  have hz : (fun y => (heatTwoFormConnection g c D.point i y).trace) = fun _ => 0 :=
    funext (fun _ => heatTwoFormConnectionMatrix_trace _)
  rw [hz]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The source of the first radial amplitude has a signed trace equal
to the leading scalar amplitude times the quadratic connection term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatBundleOperator_leading (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (U : FourSpace → ℝ)
    (x : FourSpace) (k l : Fin 6) :
    fourHeatBundleOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k =
      (if k = l then 1 else 0) * fourHeatLocalOperator a b 0 U x +
        (∑ i, B i k l * partialDeriv U i x) + U x * C k l := by
  have hf (q : Fin 6) : (fun y => U y * (if q = l then 1 else 0)) =
      (fun y => (if q = l then 1 else 0) * U y) := by funext y; ring
  unfold fourHeatBundleOperator fourHeatBundleFirst fourHeatBundleZero
  simp_rw [hf, fourHeatLocalOperator_const_mul, fourHeat_partial_const_mul]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.firstSource (E : HeatNormalBundleExtension D)
    (x : FourSpace) : HeatMat6 := fun k l =>
  -fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y q => E.base.U y * (if q = l then 1 else 0)) x k

theorem HeatNormalBundleExtension.firstSource_regular (E : HeatNormalBundleExtension D)
    (k l : Fin 6) : ContDiff ℝ 2 (fun x => E.firstSource x k l) := by
  apply ContDiff.neg
  apply fourHeatBundleOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · intro i j
    exact (E.base.a_regular i j).of_le (by norm_num)
  · intro i
    exact (E.base.b_regular i).of_le (by norm_num)
  · intro i a b
    exact (E.B_regular i a b).of_le (by norm_num)
  · intro a b
    exact (E.C_regular a b).of_le (by norm_num)
  · intro q
    exact (E.base.U_regular.of_le (by norm_num)).mul contDiff_const

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Gaussian-free column and its uniform density-weighted bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOnePolynomialColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => χ x * fourHeatPolynomial (fun m y => E.amplitude m y k l) t x)

theorem heatNormalOneCutoffColumn_gaussian (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOneCutoffColumn E χ t l x =
      fourHeatGaussian t x • heatNormalOnePolynomialColumn E χ t l x := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * (fourHeatGaussian t x * _) = fourHeatGaussian t x * (χ x * _)
  unfold fourHeatOnePolynomial fourHeatPolynomial
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common density-weighted polynomial bound for the actual nearby
normal-frame columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyPolynomialColumn (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (z : HeatRadialFrameSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => χ z.1 *
    fourHeatPolynomial (fun m x => E.amplitude m (x, z.2) k l) t z.1)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.polynomialColumn_family (N : HeatCommonNormalMember g o c E r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn N.extension χ t l x =
      heatFamilyPolynomialColumn E χ t l (x, frameCoordinateState g c e) := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * fourHeatPolynomial _ t x = χ x * fourHeatPolynomial _ t x
  have hu : (fun (m : Fin 4) y => N.extension.amplitude m y k l) =
      (fun (m : Fin 4) y => E.amplitude m (y, frameCoordinateState g c e) k l) := by
    funext m y
    exact congrArg (fun f : FourSpace → HeatMat6 => f y k l) (N.amplitude_family m (by omega))
  rw [hu]


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual zeroth-order coefficient has zero alternating degree trace.
This is a geometric identity on a neighborhood, not a heat assumption. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.bundleOne_trace_relation_near
    (D : HeatNormalFrameData g o c e) (hRic : RicciThree g) :
    (fun x => (heatNormalBundleZero D x).trace) =ᶠ[𝓝 0]
      fun x => 2 * (heatNormalOneZero D x).trace := by
  have hd₁ : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i k l,
      DifferentiableAt ℝ (fun y => heatNormalFrameConnection g c D.point i y k l) x :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      ((D.connection_regular i k l).eventually (by norm_num)).mono
        (fun _ h => h.differentiableAt (by norm_num)))))
  have hd₂ : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i k l,
      DifferentiableAt ℝ (fun y => heatTwoFormConnection g c D.point i y k l) x :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      ((D.twoForm_connection_regular i k l).eventually (by norm_num)).mono
        (fun _ h => h.differentiableAt (by norm_num)))))
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos, hd₁, hd₂] with x hx h₁ h₂
  have hquad : (∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      (heatTwoFormConnection g c D.point j x * heatTwoFormConnection g c D.point i x).trace) =
      2 * ∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        (heatNormalFrameConnection g c D.point j x * heatNormalFrameConnection g c D.point i x).trace := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [heatTwoFormConnection, heatTwoFormConnection,
      heatTwoFormConnectionMatrix_product_trace _ _ (D.connection_skew x hx j) (D.connection_skew x hx i)]
    ring
  rw [heatNormalBundleZero, heatTwoConnectionZero_trace _ _ _ _ x
    (fun i => heatTwoFormConnectionMatrix_trace _)
    (fun i j => D.twoConnection_partial_trace x i j (fun k => h₂ i k k)),
    heatNormalOneZero, heatOneConnectionZero_trace _ _ _ _ x
    (fun i => heatFour_skew_trace _ (D.connection_skew x hx i))
    (fun i j => D.oneConnection_partial_trace x hx i j (fun k => h₁ i k k))]
  rw [D.potential_as_actual x hx, actual_twoFormPotential_trace hRic, hquad]
  norm_num [Matrix.trace_smul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common leading amplitude has a vanishing first Euler source
for the actual scalar, one-form and two-form heat operators. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem fourHeatOneOperator_leading (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (U : FourSpace → ℝ)
    (x : FourSpace) (k l : Fin 4) :
    fourHeatOneOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k =
      (if k = l then 1 else 0) * fourHeatLocalOperator a b 0 U x +
        (∑ i, B i k l * partialDeriv U i x) + U x * C k l := by
  have hf (q : Fin 4) : (fun y => U y * (if q = l then 1 else 0)) =
      (fun y => (if q = l then 1 else 0) * U y) := by funext y; ring
  unfold fourHeatOneOperator fourHeatOneFirst fourHeatOneZero
  simp_rw [hf, fourHeatLocalOperator_const_mul, fourHeat_partial_const_mul]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  ring

theorem heatOneLeadingSource_trace (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (U : FourSpace → ℝ) (x : FourSpace)
    (hB : ∀ i, (B i).trace = 0) :
    (show Mat4 from fun k l => -fourHeatOneOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k).trace =
      -4 * fourHeatLocalOperator a b 0 U x - U x * C.trace := by
  have hm : (show Mat4 from fun k l => -fourHeatOneOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k) =
      -(fourHeatLocalOperator a b 0 U x • (1 : Mat4) +
        (∑ i, partialDeriv U i x • B i) + U x • C) := by
    ext k l
    rw [fourHeatOneOperator_leading]
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, smul_eq_mul]
    have hs : (∑ i, B i k l * partialDeriv U i x) =
        ∑ i, partialDeriv U i x * B i k l := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  rw [hm]
  simp only [Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hB, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
  norm_num
  ring

theorem heatTwoLeadingSource_trace (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (U : FourSpace → ℝ) (x : FourSpace)
    (hB : ∀ i, (B i).trace = 0) :
    (show HeatMat6 from fun k l => -fourHeatBundleOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k).trace =
      -6 * fourHeatLocalOperator a b 0 U x - U x * C.trace := by
  have hm : (show HeatMat6 from fun k l => -fourHeatBundleOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k) =
      -(fourHeatLocalOperator a b 0 U x • (1 : HeatMat6) +
        (∑ i, partialDeriv U i x • B i) + U x • C) := by
    ext k l
    rw [fourHeatBundleOperator_leading]
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, smul_eq_mul]
    have hs : (∑ i, B i k l * partialDeriv U i x) =
        ∑ i, partialDeriv U i x * B i k l := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  rw [hm]
  simp only [Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hB, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
  norm_num
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.oneCompanion (E : HeatNormalBundleExtension D) :
    HeatNormalOneExtension D :=
  { Classical.choice (exists_heatNormalOneExtension D) with base := E.base }

def HeatNormalOneExtension.firstSource (E : HeatNormalOneExtension D) (x : FourSpace) : Mat4 :=
  fun k l => -fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y q => E.base.U y * (if q = l then 1 else 0)) x k

theorem HeatNormalOneExtension.firstSource_regular (E : HeatNormalOneExtension D)
    (k l : Fin 4) : ContDiff ℝ 2 (fun x => E.firstSource x k l) := by
  apply ContDiff.neg
  apply fourHeatOneOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · intro i j
    exact (E.base.a_regular i j).of_le (by norm_num)
  · intro i
    exact (E.base.b_regular i).of_le (by norm_num)
  · intro i a b
    exact (E.B_regular i a b).of_le (by norm_num)
  · intro a b
    exact (E.C_regular a b).of_le (by norm_num)
  · intro q
    exact (E.base.U_regular.of_le (by norm_num)).mul contDiff_const

theorem HeatNormalBundleExtension.B_trace_near (E : HeatNormalBundleExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i, (E.B x i).trace = 0 := by
  filter_upwards [E.B_near] with x hx
  intro i
  rw [hx]
  simp only [heatNormalBundleFirst, fourHeatConnectionFirst, Matrix.trace_smul,
    Matrix.trace_sum, heatTwoFormConnection, heatTwoFormConnectionMatrix_trace,
    smul_eq_mul, mul_zero, Finset.sum_const_zero]

theorem HeatNormalOneExtension.B_trace_near (E : HeatNormalOneExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i, (E.B x i).trace = 0 := by
  filter_upwards [E.B_near, Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx hb
  intro i
  rw [hx]
  simp only [heatNormalOneFirst, fourHeatOneConnectionFirst, Matrix.trace_smul, Matrix.trace_sum]
  simp only [heatFour_skew_trace _ (D.connection_skew x hb _), smul_eq_mul,
    mul_zero, Finset.sum_const_zero]

def HeatNormalBundleExtension.eulerFirstSource (E : HeatNormalBundleExtension D) (x : FourSpace) : ℝ :=
  2 * (-fourHeatLocalOperator (E.base.a x) (E.base.b x) 0 E.base.U x) -
    2 * (E.oneCompanion.firstSource x).trace + (E.firstSource x).trace

theorem HeatNormalBundleExtension.eulerFirstSource_zero_near
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    E.eulerFirstSource =ᶠ[𝓝 0] fun _ => 0 := by
  have hC : (fun x => (E.C x).trace) =ᶠ[𝓝 0] fun x => 2 * (E.oneCompanion.C x).trace := by
    filter_upwards [E.C_near, E.oneCompanion.C_near, D.bundleOne_trace_relation_near hRic]
      with x h₂ h₁ h
    rwa [h₂, h₁]
  filter_upwards [E.B_trace_near, E.oneCompanion.B_trace_near, hC] with x h₂ h₁ h
  change 2 * (-fourHeatLocalOperator (E.base.a x) (E.base.b x) 0 E.base.U x) -
    2 * (show Mat4 from fun k l => -fourHeatOneOperator _ _ _ _
      (fun y q => E.base.U y * (if q = l then 1 else 0)) x k).trace +
    (show HeatMat6 from fun k l => -fourHeatBundleOperator _ _ _ _
      (fun y q => E.base.U y * (if q = l then 1 else 0)) x k).trace = 0
  rw [heatOneLeadingSource_trace _ _ _ _ _ x h₁, heatTwoLeadingSource_trace _ _ _ _ _ x h₂, h]
  rw [show E.oneCompanion.base = E.base from rfl]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single genuine normal chart and compact cutoff for the time-dependent
parametrix. Its existence simultaneously enforces the domain and residual bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

structure HeatNormalParametrixData (D : HeatNormalFrameData g o c e) where
  chart : OpenPartialHomeomorph FourSpace M
  exponential : EqOn chart (frameExponential g o e) chart.source
  in_chart : chart.target ⊆ (chartAt FourSpace c).source
  point_regular : ContDiffOn ℝ 2 D.point chart.source
  inside_radius : chart.source ⊆ ball 0 D.radius
  cutoff : FourSpace → ℝ
  cutoff_regular : ContDiff ℝ 4 cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.source
  cutoff_zero : cutoff 0 = 1

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.column (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalGlobalParametrixColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.normalizedColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalizedParametrixColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual radial integral preserves the Euler source cancellation,
so the first alternating heat coefficient vanishes near the center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.first_amplitude_trace_radial
    (E : HeatNormalOneExtension D) (x : FourSpace) :
    (E.amplitude 1 x).trace =
      fourHeatWeightedRadialAverage 0 E.base.U (fun y => (E.firstSource y).trace) x := by
  change (∑ k : Fin 4, fourHeatWeightedRadialAverage 0 E.base.U
      (fun y => E.firstSource y k k) x) = _
  exact (fourHeatWeightedRadialAverage_sum 0 E.base.U
    (fun k y => E.firstSource y k k) E.base.U_regular.continuous
    (fun k => (E.firstSource_regular k k).continuous) (fun y => (E.base.U_pos y).ne') x).symm

theorem HeatNormalBundleExtension.first_amplitude_trace_radial
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    (E.amplitude 1 x).trace =
      fourHeatWeightedRadialAverage 0 E.base.U (fun y => (E.firstSource y).trace) x := by
  change (∑ k : Fin 6, fourHeatWeightedRadialAverage 0 E.base.U
      (fun y => E.firstSource y k k) x) = _
  exact (fourHeatWeightedRadialAverage_sum 0 E.base.U
    (fun k y => E.firstSource y k k) E.base.U_regular.continuous
    (fun k => (E.firstSource_regular k k).continuous) (fun y => (E.base.U_pos y).ne') x).symm

def HeatNormalBundleExtension.eulerFirstAmplitude (E : HeatNormalBundleExtension D)
    (x : FourSpace) : ℝ :=
  2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1 x -
    2 * (E.oneCompanion.amplitude 1 x).trace + (E.amplitude 1 x).trace

theorem HeatNormalBundleExtension.eulerFirstAmplitude_radial
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    E.eulerFirstAmplitude x = fourHeatWeightedRadialAverage 0 E.base.U E.eulerFirstSource x := by
  let F := fun y => -fourHeatLocalOperator (E.base.a y) (E.base.b y) 0 E.base.U y
  let G := fun y => (E.oneCompanion.firstSource y).trace
  let H := fun y => (E.firstSource y).trace
  have hU := E.base.U_regular.continuous
  have hU0 (y : FourSpace) := (E.base.U_pos y).ne'
  have hF : Continuous F := by
    have hr : ContDiff ℝ 1 F := (fourHeatLocalOperator_contDiff 1 E.base.a E.base.b (fun _ => 0) E.base.U
      (fun i j => (E.base.a_regular i j).of_le (by norm_num))
      (fun i => (E.base.b_regular i).of_le (by norm_num)) contDiff_const
      (E.base.U_regular.of_le (by norm_num))).neg
    exact hr.continuous
  have hG : Continuous G :=
    continuous_finsetSum _ (fun k _ => (E.oneCompanion.firstSource_regular k k).continuous)
  have hH : Continuous H :=
    continuous_finsetSum _ (fun k _ => (E.firstSource_regular k k).continuous)
  rw [eulerFirstAmplitude, E.oneCompanion.first_amplitude_trace_radial, E.first_amplitude_trace_radial]
  change 2 * fourHeatWeightedRadialAverage 0 E.base.U F x -
    2 * fourHeatWeightedRadialAverage 0 E.base.U G x +
      fourHeatWeightedRadialAverage 0 E.base.U H x = _
  have heq : E.eulerFirstSource = (fun y => 2 * F y + (-2) * G y + H y) := by
    funext y
    dsimp only [HeatNormalBundleExtension.eulerFirstSource, F, G, H]
    ring
  rw [heq]
  rw [fourHeatWeightedRadialAverage_add 0 E.base.U (fun y => 2 * F y + (-2) * G y) H hU
    ((continuous_const.mul hF).add (continuous_const.mul hG)) hH hU0 x,
    fourHeatWeightedRadialAverage_add 0 E.base.U (fun y => 2 * F y) (fun y => (-2) * G y) hU
      (continuous_const.mul hF) (continuous_const.mul hG) hU0 x,
    fourHeatWeightedRadialAverage_const_mul, fourHeatWeightedRadialAverage_const_mul]
  ring

theorem HeatNormalBundleExtension.eulerFirstAmplitude_zero_near
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    E.eulerFirstAmplitude =ᶠ[𝓝 0] fun _ => 0 := by
  have h := fourHeatWeightedRadialAverage_zero_germ 0 E.base.U E.eulerFirstSource
    (E.eulerFirstSource_zero_near hRic)
  filter_upwards [h] with x hx
  rw [E.eulerFirstAmplitude_radial]
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform normal-frame amplitude bound gives an actual global L2
bound. The moving-frame tensor norm is computed using its orthogonality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalAmplitudeTensor_norm_sq
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (f : FrameBundle g) (hf : f.base ∈ C.target) :
    ‖heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f‖ ^ 2 =
      2 * ‖a (C.symm f.base)‖ ^ 2 := by
  let x := C.symm f.base
  have hx : x ∈ C.source := C.map_target hf
  have hxb := hD hx
  have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
    rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
  have hF := frameChartMatrix_normalizes g c f (hCt hf)
  rw [← hbase] at hF
  have hi : (D.point x).2⁻¹ * (D.point x).2 = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (heatNormalFrame_matrix_nondegenerate D hxb))
  have hback : frameTensor (D.point x).2 (heatNormalCoordinateTensor D a x) = twoFormTensor (a x) := by
    unfold heatNormalCoordinateTensor
    rw [← frameTensor_mul, hi, frameTensor_one]
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f)
    : TwoTensorEuclidean) (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f)) = _
  rw [heat_euclideanTensor_inner, heatNormalFrameTensorLift, ite_eq_left hf]
  change frameTensorPairing
    (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))))
    (frameTensor (frameChartMatrix g c f) (heatNormalCoordinateTensor D a x)) = _
  rw [heat_normal_frame_pairing _ _ _ (D.orthonormal x hxb) hF, hback,
    twoFormTensor_pairing, real_inner_self_eq_norm_sq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One genuine chart and cutoff for the actual one-form weak heat equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneGlobalColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff P.cutoff_regular P.cutoff_compact P.cutoff_support t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual normal chart and compact scalar cutoff. All functions have
the four derivatives required by the finite Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

structure HeatScalarChartData (D : HeatNormalFrameData g o c e) where
  extension : HeatNormalExtension 10 g o e
  chart : OpenPartialHomeomorph FourSpace M
  exponential : EqOn chart (frameExponential g o e) chart.source
  in_chart : chart.target ⊆ (chartAt FourSpace c).source
  point_regular : ContDiffOn ℝ 4 D.point chart.source
  inverse_regular : ContMDiffOn I4 I4 4 chart.symm chart.target
  inside_radius : chart.source ⊆ ball 0 D.radius
  cutoff : FourSpace → ℝ
  cutoff_regular : ContDiff ℝ 4 cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.source
  cutoff_zero : cutoff 0 = 1

variable {D : HeatNormalFrameData g o c e}

def HeatScalarChartData.function (P : HeatScalarChartData D) (t : ℝ) : M → ℝ :=
  heatNormalScalarLift P.chart (P.extension.scalarCutoff P.cutoff t)

theorem HeatScalarChartData.function_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (P.function t) :=
  heatNormalScalarLift_regular P.chart _ P.inverse_regular
    (P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (P.extension.scalarCutoff_support P.cutoff t))
    ((P.extension.scalarCutoff_support P.cutoff t).trans P.cutoff_support)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def HeatScalarChartData.column (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  scalarFiniteValueL2 g (P.function t) (P.function_regular t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common normal ball and fixed bump define actual compact
parametrix data, with the actual Hodge generator identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

def HeatCommonNormalMember.parametrixData (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) : HeatNormalParametrixData N.frameData := by
  let C := N.chart.restrOpen (ball 0 r) isOpen_ball
  have hs : C.source = ball 0 r := inter_eq_right.mpr N.ball_source
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ C.source := by
    rw [hs, (heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  exact {
    chart := C
    exponential := fun x hx => N.exponential hx.1
    in_chart := fun y hy => N.target_chart hy.1
    point_regular := fun x hx => (N.point_regular x (hs ▸ hx)).contDiffWithinAt
    inside_radius := fun x hx => ball_subset_ball N.radius_le (hs ▸ hx)
    cutoff := χ
    cutoff_regular := (heatNormalChartBump r hr).contDiff
    cutoff_compact := (heatNormalChartBump r hr).hasCompactSupport
    cutoff_support := hχs
    cutoff_zero := (heatNormalChartBump r hr).one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ r / 4; positivity)) }

theorem HeatCommonNormalMember.parametrixData_cutoff (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) : (N.parametrixData hr).cutoff = heatNormalChartBump r hr := rfl

theorem HeatCommonNormalMember.parametrixData_source (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) : (N.parametrixData hr).chart.source = ball 0 r :=
  inter_eq_right.mpr N.ball_source

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local transport amplitudes are independent of the chosen extensions.
This permits the common smooth family to supply the one-form companion. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology
noncomputable section

theorem fourHeatWeightedRadialAverage_congr_germ (m : ℕ) (U F G : FourSpace → ℝ)
    (h : F =ᶠ[𝓝 0] G) :
    fourHeatWeightedRadialAverage m U F =ᶠ[𝓝 0] fourHeatWeightedRadialAverage m U G := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp h
  filter_upwards [ball_mem_nhds (0 : FourSpace) hr] with x hx
  unfold fourHeatWeightedRadialAverage fourHeatRadialAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  have hn : ‖s • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs'.1]
    exact mul_le_of_le_one_left (norm_nonneg x) hs'.2
  have hm : s • x ∈ ball (0 : FourSpace) r := by
    rw [mem_ball, dist_zero_right]
    exact hn.trans_lt (by simpa only [mem_ball, dist_zero_right] using hx)
  change s ^ m * (F (s • x) / U (s • x)) = s ^ m * (G (s • x) / U (s • x))
  rw [hball hm]

theorem fourHeatOneCoefficient_congr_germ (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (U : FourSpace → ℝ)
    (B B' : FourSpace → Fin 4 → Mat4) (C C' : FourSpace → Mat4)
    (hB : B =ᶠ[𝓝 0] B') (hC : C =ᶠ[𝓝 0] C') :
    fourHeatOneCoefficient a b B C U m =ᶠ[𝓝 0] fourHeatOneCoefficient a b B' C' U m := by
  induction m with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ m ih =>
    have hs (k l : Fin 4) :
        (fun x => -fourHeatOneOperator (a x) (b x) (B x) (C x)
          (fun y q => fourHeatOneCoefficient a b B C U m y q l) x k) =ᶠ[𝓝 0]
        (fun x => -fourHeatOneOperator (a x) (b x) (B' x) (C' x)
          (fun y q => fourHeatOneCoefficient a b B' C' U m y q l) x k) := by
      filter_upwards [hB, hC, ih.eventuallyEq_nhds] with x hBx hCx hx
      rw [hBx, hCx]
      congr 1
      exact fourHeatOneOperator_germ _ _ _ _ (fun q =>
        hx.mono fun y hy => congrArg (fun A : Mat4 => A q l) hy) k
    have h := eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      fourHeatWeightedRadialAverage_congr_germ m U _ _ (hs k l)))
    filter_upwards [h] with x hx
    funext k l
    exact hx k l

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.amplitude_companion_germ (A : HeatNormalOneExtension D)
    (E : HeatNormalBundleExtension D) (hbase : A.base = E.base) (m : ℕ) :
    A.amplitude m =ᶠ[𝓝 0] E.oneCompanion.amplitude m := by
  have h := fourHeatOneCoefficient_congr_germ m E.base.a E.base.b E.base.U
    A.B E.oneCompanion.B A.C E.oneCompanion.C
    (A.B_near.trans E.oneCompanion.B_near.symm) (A.C_near.trans E.oneCompanion.C_near.symm)
  change fourHeatOneCoefficient A.base.a A.base.b A.B A.C A.base.U m =ᶠ[𝓝 0]
    fourHeatOneCoefficient E.base.a E.base.b E.oneCompanion.B E.oneCompanion.C E.base.U m
  simpa only [hbase] using h

theorem HeatNormalOneExtension.eulerFirst_zero_near (A : HeatNormalOneExtension D)
    (E : HeatNormalBundleExtension D) (hbase : A.base = E.base) (hRic : RicciThree g) :
    (fun x => 2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1 x -
      2 * (A.amplitude 1 x).trace + (E.amplitude 1 x).trace) =ᶠ[𝓝 0] fun _ => 0 := by
  filter_upwards [A.amplitude_companion_germ E hbase 1, E.eulerFirstAmplitude_zero_near hRic]
    with x hx he
  simpa only [hx, HeatNormalBundleExtension.eulerFirstAmplitude] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact norm integral for the actual compact normal amplitude, obtained
by smooth approximation inside the genuine two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance heatNormalExactCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatNormalExactProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatNormalAmplitudeTensor_L2_realization
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    twoFormTensorL2 (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
        (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs) := by
  apply heatNormalTensor_L2_realization C hCt (heatNormalCoordinateTensor D a)
    (heatNormalCoordinateTensor_continuousOn D C hP hD a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCoordinateTensor_support D a))
    ((heatNormalCoordinateTensor_support D a).trans hs)
  intro z i j
  apply twoTensor_frame_skew
  intro k l
  exact congrArg (fun A : Mat4 => A k l) (twoFormMatrix_skew (a z))

theorem heatNormalAmplitudeL2_norm_sq_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
  let F := heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs
  let ψ := fun x => ‖a x‖ ^ 2
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change ‖a x‖ ^ 2 = 0
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.norm.pow 2).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : ‖F f‖ ^ 2 = 2 * heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalAmplitudeTensor_norm_sq C hE hCt hP hD a ha hc hs f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : F f = 0 := by
        change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
        simp only [heatNormalFrameTensorLift, ite_eq_right hf]
        rfl
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      simp only [heatNormalScalarLift, ite_eq_right hf, mul_zero]
  have hex : twoFormTensorL2 (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F :=
    heatNormalAmplitudeTensor_L2_realization C hCt hP hD a ha hc hs
  have hcalc : 2 * ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      2 * ((normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2) := by
    calc
      _ = ‖ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F‖ ^ 2 := by
        rw [← hex, twoFormTensorL2_norm_sq]
      _ = ∫ f, ‖F f‖ ^ 2 ∂canonicalFrameMeasure g o := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F] with f hf
        rw [hf, real_inner_self_eq_norm_sq]
      _ = 2 * ∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g := by
        simp_rw [heq]
        rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi]
      _ = _ := by
        rw [heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hs)]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal one-form parametrix tends to the correctly normalized delta. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]


variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneNormalizedColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn E t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global scalar parametrix has exact normal-coordinate pairings,
including the explicit factor from the normalized geometric volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatNormalScalarLift_mul {X : Type*} [TopologicalSpace X]
    (C : OpenPartialHomeomorph FourSpace X) (ψ : FourSpace → ℝ) (f : X → ℝ) (x : X) :
    heatNormalScalarLift C ψ x * f x =
      heatNormalScalarLift C (fun y => ψ y * f (C y)) x := by
  classical
  by_cases hx : x ∈ C.target
  · rw [heatNormalScalarLift_on_target C ψ hx, heatNormalScalarLift_on_target C _ hx,
      C.right_inv hx]
  · simp only [heatNormalScalarLift, ite_eq_right hx, zero_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarGlobal_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem HeatScalarChartData.column_pairing (P : HeatScalarChartData D)
    (t : ℝ) (f : C(M, ℝ)) :
    inner ℝ (P.column t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f) =
      (normalizedChartFactor g).toReal * ∫ x,
        P.extension.scalarCutoff P.cutoff t x *
          (frameExponentialJacobian g o e x * f (P.chart x)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, P.function t y * f y ∂normalizedVolume g := by
      apply integral_congr_ae
      filter_upwards [scalarFiniteValueL2_coe g (P.function t) (P.function_regular t),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) f] with y hy hf
      simp only [RCLike.inner_apply', conj_trivial, HeatScalarChartData.column, hy, hf]
    _ = ∫ y, heatNormalScalarLift P.chart
        (fun x => P.extension.scalarCutoff P.cutoff t x * f (P.chart x)) y
          ∂normalizedVolume g := by
      apply integral_congr_ae
      exact Eventually.of_forall (heatNormalScalarLift_mul P.chart _ f)
    _ = _ := by
      rw [heatNormalScalarLift_integral D P.chart P.exponential P.in_chart
        (P.point_regular.of_le (by norm_num)) P.inside_radius]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      · exact tsupport_mul_subset_left.trans
          ((P.extension.scalarCutoff_support P.cutoff t).trans P.cutoff_support)

def HeatScalarChartData.normalizedColumn (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.column t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate L2 pairing and the sharp order of growth
of the actual scalar parametrix column. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarGaussian_probability_rced384_1 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem HeatScalarChartData.column_norm_sq_integral (P : HeatScalarChartData D) (t : ℝ) :
    ‖P.column t‖ ^ 2 = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x * (P.extension.scalarCutoff P.cutoff t x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := P.column_pairing t (⟨P.function t, (P.function_regular t).continuous⟩ : C(M, ℝ))
  change inner ℝ (P.column t) (P.column t) = _ at h
  rw [h]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ P.chart.source
    · have hf := heatNormalScalarLift_source P.chart (P.extension.scalarCutoff P.cutoff t) hx
      change P.extension.scalarCutoff P.cutoff t x *
        (frameExponentialJacobian g o e x * P.function t (P.chart x)) = _
      change P.function t (P.chart x) = P.extension.scalarCutoff P.cutoff t x at hf
      rw [hf]
      ring
    · have hz : P.extension.scalarCutoff P.cutoff t x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs => hx
          (P.cutoff_support (P.extension.scalarCutoff_support P.cutoff t hs)))
      change P.extension.scalarCutoff P.cutoff t x *
        (frameExponentialJacobian g o e x * P.function t (P.chart x)) =
        frameExponentialJacobian g o e x * (P.extension.scalarCutoff P.cutoff t x) ^ 2
      rw [hz]
      ring

def HeatScalarChartData.polynomial (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) : ℝ :=
  P.cutoff x * fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t x

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.cutoff_gaussian (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) :
    P.extension.scalarCutoff P.cutoff t x = fourHeatGaussian t x * P.polynomial t x := by
  unfold HeatNormalExtension.scalarCutoff HeatNormalExtension.scalarParametrix polynomial
  ring

theorem HeatScalarChartData.normalizedColumn_gaussian_integral
    (P : HeatScalarChartData D) (t : ℝ) :
    ‖P.normalizedColumn t‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column t‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, P.column_norm_sq_integral]
  have he : (∫ x, frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) =
      ∫ x, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change frameExponentialJacobian g o e x * (P.extension.scalarCutoff P.cutoff t x) ^ 2 = _
      rw [P.cutoff_gaussian]
      ring
  rw [he]
  field_simp [(normalizedChartFactor_toReal_pos g).ne']

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

/-! The finite alternating Gram polynomial for degrees zero, one and two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section

abbrev HeatEulerFiber := ℝ × Mat4 × HeatMat6

def heatEulerUnit : HeatEulerFiber := (1, 1, 1)

def heatEulerTrace (A : HeatEulerFiber) : ℝ := 2 * A.1 - 2 * A.2.1.trace + A.2.2.trace

def heatEulerGram (A B : HeatEulerFiber) : ℝ :=
  2 * A.1 * B.1 - 2 * (A.2.1ᵀ * B.2.1).trace + (A.2.2ᵀ * B.2.2).trace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first Euler coefficient is a jointly C2 family with a uniform
quadratic zero at each actual normal center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def HeatFamilyOneCoefficients.eulerAmplitude (F : HeatFamilyOneCoefficients)
    (m : ℕ) (z : HeatRadialFrameSpace) : HeatEulerFiber :=
  (F.base.scalarAmplitude m z, F.amplitude m z, F.base.amplitude m z)

def heatFamilyEulerFirst (F : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  χ z.1 ^ 2 / F.base.U z * heatEulerTrace (F.eulerAmplitude 1 z)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_amplitude_family (N : HeatCommonEulerMember g o c F r e)
    (m : ℕ) (hm : m ≤ 3) :
    N.one.amplitude m = fun x => F.amplitude m (x, frameCoordinateState g c e) := by
  unfold HeatNormalOneExtension.amplitude
  rw [N.one_base, N.normal.a_family, N.normal.b_family,
    N.one_B_family, N.one_C_family, N.normal.U_family]
  exact (F.amplitude_slice m hm _).symm

theorem HeatCommonEulerMember.scalar_amplitude_family (N : HeatCommonEulerMember g o c F r e)
    (m : ℕ) (hm : m ≤ 3) :
    N.normal.extension.base.scalarAmplitude m =
      fun x => F.base.scalarAmplitude m (x, frameCoordinateState g c e) := by
  unfold HeatNormalExtension.scalarAmplitude
  rw [N.normal.a_family, N.normal.b_family, N.normal.U_family]
  exact (F.base.scalarAmplitude_slice m hm _).symm

theorem HeatCommonEulerMember.eulerFirst_zero_near (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (χ : FourSpace → ℝ) :
    (fun x => heatFamilyEulerFirst F χ (x, frameCoordinateState g c e)) =ᶠ[𝓝 0] fun _ => 0 := by
  have h := N.one.eulerFirst_zero_near N.normal.extension N.one_base hRic
  filter_upwards [h] with x hx
  have htrace : heatEulerTrace (F.eulerAmplitude 1 (x, frameCoordinateState g c e)) = 0 := by
    change 2 * F.base.scalarAmplitude 1 (x, frameCoordinateState g c e) -
      2 * (F.amplitude 1 (x, frameCoordinateState g c e)).trace +
      (F.base.amplitude 1 (x, frameCoordinateState g c e)).trace = 0
    rw [← congrFun (N.one_amplitude_family 1 (by norm_num)) x,
      ← congrFun (N.normal.amplitude_family 1 (by norm_num)) x,
      ← congrFun (N.scalar_amplitude_family 1 (by norm_num)) x]
    exact hx
  simp only [heatFamilyEulerFirst, htrace, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common density-weighted polynomial bound for the actual nearby
normal-frame columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyOnePolynomialColumn (E : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (z : HeatRadialFrameSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => χ z.1 *
    fourHeatPolynomial (fun m x => E.amplitude m (x, z.2) k l) t z.1)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.onePolynomialColumn_family (N : HeatCommonEulerMember g o c E r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOnePolynomialColumn N.one χ t l x =
      heatFamilyOnePolynomialColumn E χ t l (x, frameCoordinateState g c e) := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * fourHeatPolynomial _ t x = χ x * fourHeatPolynomial _ t x
  have hu : (fun (m : Fin 4) y => N.one.amplitude m y k l) =
      (fun (m : Fin 4) y => E.amplitude m (y, frameCoordinateState g c e) k l) := by
    funext m y
    exact congrArg (fun f : FourSpace → Mat4 => f y k l) (N.one_amplitude_family m (by omega))
  rw [hu]


end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform bounds for the remaining coefficients of the common Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def HeatFamilyOneCoefficients.eulerPolynomial (F : HeatFamilyOneCoefficients)
    (t : ℝ) (z : HeatRadialFrameSpace) : HeatEulerFiber :=
  F.base.U z • heatEulerUnit + t • F.eulerAmplitude 1 z +
    t ^ 2 • F.eulerAmplitude 2 z + t ^ 3 • F.eulerAmplitude 3 z

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form operator and Green coefficients on the common normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonEulerMember.actual_one_operator (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (x : FourSpace) (hx : x ∈ ball 0 r)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalOneFirst N.normal.frameData x) (heatNormalOneZero N.normal.frameData x)
      (heatNormalOneFormValue c N.normal.frameData.point u) x k =
    heatNormalOneFormValue c N.normal.frameData.point (smoothOneFormHodgeLaplacian (o := o) u) x k :=
  N.normal.frameData.actual_one_operator_at hRic x (ball_subset_ball N.normal.radius_le hx)
    (N.normal.point_regular x hx) (N.normal.exponential_source x hx) (N.normal.metric_pos x hx) u k

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar and one-form data on the same actual chart and fixed cutoff as degree two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

def HeatCommonEulerMember.scalarData (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) : HeatScalarChartData N.normal.frameData where
  extension := N.normal.extension.base
  chart := (N.normal.parametrixData hr).chart
  exponential := (N.normal.parametrixData hr).exponential
  in_chart := (N.normal.parametrixData hr).in_chart
  point_regular := fun x hx => (N.point_regular_four x
    ((N.normal.parametrixData_source hr) ▸ hx)).contDiffWithinAt
  inverse_regular := N.normal.inverse_regular.mono (fun _ hy => hy.1)
  inside_radius := (N.normal.parametrixData hr).inside_radius
  cutoff := (N.normal.parametrixData hr).cutoff
  cutoff_regular := (N.normal.parametrixData hr).cutoff_regular
  cutoff_compact := (N.normal.parametrixData hr).cutoff_compact
  cutoff_support := (N.normal.parametrixData hr).cutoff_support
  cutoff_zero := (N.normal.parametrixData hr).cutoff_zero

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform density-weighted scalar polynomial bound over the actual frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def heatFamilyScalarPolynomial (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  χ z.1 * fourHeatPolynomial (fun m x => E.scalarAmplitude m (x, z.2)) t z.1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalarPolynomial_family (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (x : FourSpace) :
    (N.scalarData hr).polynomial t x =
      heatFamilyScalarPolynomial F.base (heatNormalChartBump r hr) t (x, frameCoordinateState g c e) := by
  change (heatNormalChartBump r hr) x * fourHeatPolynomial
    (fun (m : Fin 4) y => N.normal.extension.base.scalarAmplitude m y) t x = _
  have hu : (fun (m : Fin 4) y => N.normal.extension.base.scalarAmplitude m y) =
      (fun (m : Fin 4) y => F.base.scalarAmplitude m (y, frameCoordinateState g c e)) := by
    funext m y
    exact congrFun (N.scalar_amplitude_family m (by omega)) y
  rw [hu]
  rfl

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

theorem HeatNormalParametrixData.oneColumn_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    ‖P.oneColumn E t l‖ ^ 2 = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalOneCutoffColumn E P.cutoff t l x‖ ^ 2 :=
  heatNormalOneAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalOneCutoffColumn E P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.oneNormalizedColumn_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    ‖P.oneNormalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalOneCutoffColumn E P.cutoff t l x‖ ^ 2 := by
  have he : P.oneNormalizedColumn E t l = ((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn E t l := rfl
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, P.oneColumn_norm_sq_integral E t l]
  have hn := (normalizedChartFactor_toReal_pos g).ne'
  field_simp

theorem HeatNormalParametrixData.oneNormalizedColumn_gaussian_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    ‖P.oneNormalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn E P.cutoff t l x‖ ^ 2) := by
  rw [P.oneNormalizedColumn_norm_sq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatNormalOneCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

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

theorem HeatNormalParametrixData.column_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    ‖P.column E t l‖ ^ 2 = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalCutoffColumn E P.cutoff t l x‖ ^ 2 :=
  heatNormalAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalCutoffColumn E P.cutoff t l)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.normalizedColumn_norm_sq_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    ‖P.normalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, frameExponentialJacobian g o e x * ‖heatNormalCutoffColumn E P.cutoff t l x‖ ^ 2 := by
  have he : P.normalizedColumn E t l = ((normalizedChartFactor g).toReal)⁻¹ • P.column E t l := rfl
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, P.column_norm_sq_integral E t l]
  have hn := (normalizedChartFactor_toReal_pos g).ne'
  field_simp

theorem HeatNormalParametrixData.normalizedColumn_gaussian_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    ‖P.normalizedColumn E t l‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn E P.cutoff t l x‖ ^ 2) := by
  rw [P.normalizedColumn_norm_sq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [heatNormalCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairing of the actual normalized heat columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem heatNormalPolynomialColumn_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) (hx : χ x = 0) :
    heatNormalPolynomialColumn E χ t l x = 0 := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * _ = 0
  rw [hx, zero_mul]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalParametrixData.polynomial_pair_integrable
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
      inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x) (heatNormalPolynomialColumn E P.cutoff t m x))) := by
  have hc (j : Fin 6) : Continuous (fun x => heatNormalPolynomialColumn E P.cutoff t j x) :=
    (heatNormalPolynomialColumn_continuous E P.cutoff P.cutoff_regular.continuous j).comp
      (continuous_const.prodMk continuous_id)
  apply (((fourHeatGaussian_continuous t).pow 2).mul
    ((frameExponentialJacobian_continuous g o e).mul ((hc l).inner (hc m)))).integrable_of_hasCompactSupport
  apply P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport P.cutoff)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  apply hx
  change fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
    inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x) (heatNormalPolynomialColumn E P.cutoff t m x)) = 0
  rw [heatNormalPolynomialColumn_zero E P.cutoff t l x hz, inner_zero_left, mul_zero, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The three genuine compact column polynomials are one Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatEulerGram_columns (A : HeatEulerFiber) :
    heatEulerGram A A = 2 * A.1 ^ 2 -
      2 * ∑ l : Fin 4, ‖(WithLp.toLp 2 (fun k => A.2.1 k l) : FourSpace)‖ ^ 2 +
      ∑ l : Fin 6, ‖(WithLp.toLp 2 (fun k => A.2.2 k l) : TwoFormFour)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, heatEulerGram, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact integration of the common scalar and form column polynomials. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatEuler_cutoff_integrable (χ F : FourSpace → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hF : Continuous F) (t : ℝ) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * χ x ^ 2 * F x)) := by
  apply (((fourHeatGaussian_continuous t).pow 2).mul
    ((((frameExponentialJacobian_continuous g o e).mul (hχ.pow 2))).mul hF)).integrable_of_hasCompactSupport
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [hz])

end
end PositiveEinsteinFour.Geometry
end


section

/-! The three actual column polynomials are the components of the common Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.eulerPolynomial_scalar (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (x : FourSpace) :
    (N.scalarData hr).polynomial t x = (heatNormalChartBump r hr) x *
      (F.eulerPolynomial t (x, frameCoordinateState g c e)).1 := by
  rw [N.scalarPolynomial_family]
  unfold heatFamilyScalarPolynomial HeatFamilyOneCoefficients.eulerPolynomial
    HeatFamilyOneCoefficients.eulerAmplitude
  change (heatNormalChartBump r hr) x * _ = (heatNormalChartBump r hr) x * _
  congr 1
  change F.base.scalarAmplitude 0 (x, frameCoordinateState g c e) +
    t * F.base.scalarAmplitude 1 (x, frameCoordinateState g c e) +
    t ^ 2 * F.base.scalarAmplitude 2 (x, frameCoordinateState g c e) +
    t ^ 3 * F.base.scalarAmplitude 3 (x, frameCoordinateState g c e) = _
  have hz : F.base.scalarAmplitude 0 (x, frameCoordinateState g c e) =
      F.base.U (x, frameCoordinateState g c e) := rfl
  rw [hz]
  change _ = F.base.U (x, frameCoordinateState g c e) * 1 +
    t * F.base.scalarAmplitude 1 (x, frameCoordinateState g c e) +
    t ^ 2 * F.base.scalarAmplitude 2 (x, frameCoordinateState g c e) +
    t ^ 3 * F.base.scalarAmplitude 3 (x, frameCoordinateState g c e)
  ring

theorem HeatCommonEulerMember.eulerPolynomial_one (N : HeatCommonEulerMember g o c F r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOnePolynomialColumn N.one χ t l x =
      χ x • (WithLp.toLp 2 (fun k =>
        (F.eulerPolynomial t (x, frameCoordinateState g c e)).2.1 k l) : FourSpace) := by
  rw [N.onePolynomialColumn_family]
  rfl

theorem HeatCommonEulerMember.eulerPolynomial_two (N : HeatCommonEulerMember g o c F r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn N.normal.extension χ t l x =
      χ x • (WithLp.toLp 2 (fun k =>
        (F.eulerPolynomial t (x, frameCoordinateState g c e)).2.2 k l) : TwoFormFour) := by
  rw [N.normal.polynomialColumn_family]
  rfl

theorem HeatCommonEulerMember.eulerPolynomial_gram (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (x : FourSpace) :
    2 * ((N.scalarData hr).polynomial t x) ^ 2 -
      2 * (∑ l : Fin 4, ‖heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x‖ ^ 2) +
      (∑ l : Fin 6, ‖heatNormalPolynomialColumn N.normal.extension (heatNormalChartBump r hr) t l x‖ ^ 2) =
    (heatNormalChartBump r hr) x ^ 2 *
      heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
        (F.eulerPolynomial t (x, frameCoordinateState g c e)) := by
  rw [heatEulerGram_columns, N.eulerPolynomial_scalar]
  simp_rw [N.eulerPolynomial_one, N.eulerPolynomial_two, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact Gaussian integral of the actual common-family column supertrace. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalar_polynomial_integrable (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) : Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2)) := by
  let P := N.scalarData hr
  have hc : Continuous (fun x => fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t x) :=
    (fourHeatPolynomial_joint_continuous _ (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous)).comp
      (continuous_const.prodMk continuous_id)
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) P.cutoff
    (fun x => (fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t x) ^ 2)
    P.cutoff_regular.continuous P.cutoff_compact (hc.pow 2) t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  unfold HeatScalarChartData.polynomial
  ring

theorem HeatCommonEulerMember.one_polynomial_integrable (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) (l : Fin 4) : Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x‖ ^ 2)) := by
  have hc : Continuous (fun x => (WithLp.toLp 2
      (fun k => fourHeatPolynomial (fun m y => N.one.amplitude m y k l) t x) : FourSpace)) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro k
    exact (fourHeatPolynomial_joint_continuous _ (fun m => (N.one.amplitude_regular m (by omega) k l).continuous)).comp
      (continuous_const.prodMk continuous_id)
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) (heatNormalChartBump r hr)
    (fun x => ‖(WithLp.toLp 2
      (fun k => fourHeatPolynomial (fun m y => N.one.amplitude m y k l) t x) : FourSpace)‖ ^ 2)
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport (hc.norm.pow 2) t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  have heq : heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x =
      (heatNormalChartBump r hr) x • (WithLp.toLp 2
        (fun k => fourHeatPolynomial (fun m y => N.one.amplitude m y k l) t x) : FourSpace) := rfl
  rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem HeatCommonEulerMember.euler_integral (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) :
    2 * (∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2)) -
    2 * (∑ l : Fin 4, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn N.one (heatNormalChartBump r hr) t l x‖ ^ 2)) +
    (∑ l : Fin 6, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn N.normal.extension (heatNormalChartBump r hr) t l x‖ ^ 2)) =
    ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
      (heatNormalChartBump r hr) x ^ 2 *
      heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
        (F.eulerPolynomial t (x, frameCoordinateState g c e))) := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  let F₀ := fun x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x * ((N.scalarData hr).polynomial t x) ^ 2)
  let F₁ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalOnePolynomialColumn N.one χ t l x‖ ^ 2)
  let F₂ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalPolynomialColumn N.normal.extension χ t l x‖ ^ 2)
  have h₀ : Integrable F₀ := N.scalar_polynomial_integrable hr t
  have h₁ (l : Fin 4) : Integrable (F₁ l) := N.one_polynomial_integrable hr t l
  have h₂ (l : Fin 6) : Integrable (F₂ l) := by
    simpa only [F₂, χ, N.normal.parametrixData_cutoff hr, real_inner_self_eq_norm_sq] using
      (N.normal.parametrixData hr).polynomial_pair_integrable N.normal.extension t l l
  have hs₁ : Integrable (fun x => ∑ l, F₁ l x) := integrable_finsetSum _ (fun l _ => h₁ l)
  have hs₂ : Integrable (fun x => ∑ l, F₂ l x) := integrable_finsetSum _ (fun l _ => h₂ l)
  change 2 * (∫ x, F₀ x) - 2 * (∑ l, ∫ x, F₁ l x) + (∑ l, ∫ x, F₂ l x) = _
  rw [← integral_finsetSum _ (fun l _ => h₁ l), ← integral_finsetSum _ (fun l _ => h₂ l),
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (h₀.const_mul 2) (hs₁.const_mul 2)]
  change (∫ x, ((fun y => 2 * F₀ y) - (fun y => 2 * ∑ l, F₁ l y)) x) +
    (∫ x, ∑ l, F₂ l x) = _
  rw [← integral_add ((h₀.const_mul 2).sub (hs₁.const_mul 2)) hs₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.sub_apply, F₀, F₁, F₂]
    rw [mul_assoc (frameExponentialJacobian g o e x) (χ x ^ 2),
      ← N.eulerPolynomial_gram hr t x]
    simp only [mul_add, mul_sub, Finset.mul_sum, mul_left_comm, χ]


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized column supertrace is the common Euler Gaussian integral. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

def HeatCommonEulerMember.eulerColumnTrace (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) : ℝ :=
  2 * ‖(N.scalarData hr).normalizedColumn t‖ ^ 2 -
    2 * (∑ l : Fin 4, ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l‖ ^ 2) +
    (∑ l : Fin 6, ‖(N.normal.parametrixData hr).normalizedColumn N.normal.extension t l‖ ^ 2)

theorem HeatCommonEulerMember.eulerColumnTrace_integral (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) :
    N.eulerColumnTrace hr t = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        (heatNormalChartBump r hr) x ^ 2 *
        heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
          (F.eulerPolynomial t (x, frameCoordinateState g c e))) := by
  unfold eulerColumnTrace
  rw [(N.scalarData hr).normalizedColumn_gaussian_integral]
  simp_rw [(N.normal.parametrixData hr).oneNormalizedColumn_gaussian_integral,
    (N.normal.parametrixData hr).normalizedColumn_gaussian_integral]
  simp only [← Finset.mul_sum]
  rw [show (N.normal.parametrixData hr).cutoff = heatNormalChartBump r hr from rfl]
  rw [← N.euler_integral hr t]
  ring

theorem HeatCommonEulerMember.eulerColumnTrace_family (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) (t : ℝ) :
    N.eulerColumnTrace hr t = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * ((F.base.U (x, frameCoordinateState g c e) ^ 2)⁻¹ *
        (heatNormalChartBump r hr) x ^ 2 *
        heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
          (F.eulerPolynomial t (x, frameCoordinateState g c e))) := by
  rw [N.eulerColumnTrace_integral hr t]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport (heatNormalChartBump r hr)
  · have hxs : x ∈ ball (0 : FourSpace) r := by
      rw [(heatNormalChartBump r hr).tsupport_eq] at hx
      exact closedBall_subset_ball (by change r / 2 < r; linarith) hx
    have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.normal.metric_pos x hxs))
    rw [← (N.normal.actual x hxs).2.2.2.2, N.normal.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh]
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


