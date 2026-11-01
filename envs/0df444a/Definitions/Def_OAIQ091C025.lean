-- Prove2me | Definitions.Def_OAIQ091C025
-- name    : OAIQ091C025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:23:11.342101+00:00
-- url     : https://prove2.me/theorems/ed849b14-e4ae-494a-b221-e89950d570ec
-- title:
--   Definitions bundle OAIQ091C025 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 23 definitions and 109 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.residualAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.residualFunction`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.timeAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.timeColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.timeFunction`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.toL4Linear`, `OAI.PositiveEinsteinFour.Geometry.SharpScalarSobolev`, `OAI.PositiveEinsteinFour.Geometry.TwoFormDeRhamCohomology`, `OAI.PositiveEinsteinFour.Geometry.deRhamSignatureClosedAddGroup`, `OAI.PositiveEinsteinFour.Geometry.deRhamSignatureHarmonicAddGroup`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneScaledCommutator`, `OAI.PositiveEinsteinFour.Geometry.harmonicIntersectionQuadratic`, `OAI.PositiveEinsteinFour.Geometry.harmonicSignatureAddGroup`, `OAI.PositiveEinsteinFour.Geometry.harmonicTraceAddGroup`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyCommutator`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyEulerTail`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyOneCommutator`, `OAI.PositiveEinsteinFour.Geometry.heatRadialFrameEndpoint`, `OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms`, `OAI.PositiveEinsteinFour.Geometry.smoothClosedTwoForms`, `OAI.PositiveEinsteinFour.Geometry.smoothExactTwoForms`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicIntersection`, `OAI.PositiveEinsteinFour.Geometry.twoFormIntersection`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C019`, `OAIQ091C040`, `OAIQ091C041` and `OAIQ091C022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C043`, `OAIQ091C045`, `OAIQ091C046`, `OAIQ091C047`, `OAIQ091C048`, `OAIQ091C049`, `OAIQ091C050`, `OAIQ091C051`, `OAIQ091C052` and `OAIQ091C053`; the proof of `OAI_PositiveEinsteinFour_QuarticClosed_quartic_energy_bound_closed`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C019
import Definitions.Def_OAIQ091C040
import Definitions.Def_OAIQ091C041
import Definitions.Def_OAIQ091C022

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual local radial-frame trajectories with finite smooth dependence
at zero velocity, constructed by the Picard flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_heatRadialFrameFlow (g : SmoothMetric M) (c : M) (p : CoordinateFrameSpace)
    (hp : p.1 ∈ (chartAt FourSpace c).target) : Nonempty (HeatRadialFrameFlow g c p) := by
  let p₀ : HeatRadialFrameSpace := (0, p)
  let U : Set HeatRadialFrameSpace := {q | q.2.1 ∈ (chartAt FourSpace c).target}
  have hf : ContDiffAt ℝ ∞ (heatRadialFrameField g c) p₀ :=
    heatRadialFrameField_contDiffAt g c p₀ hp
  have hU : U ∈ 𝓝 p₀ := (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
    ((chartAt FourSpace c).open_target.mem_nhds hp)
  obtain ⟨r, hr, ε, hε, β, hβc, hβ⟩ := FlowCalculus.exists_continuous_local_variational_flow
    (heatRadialFrameField g c) p₀ (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) U hU
  let A : HeatRadialFrameSpace × ℝ → HeatRadialFrameSpace := fun z => (β z).1
  have hAc : ContinuousOn A (closedBall p₀ r ×ˢ Ioo (-ε) ε) := hβc.fst
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hdom : closedBall p₀ r ×ˢ Ioo (-ε) ε ∈ 𝓝 (p₀, (0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (closedBall_mem_nhds p₀ hr) (isOpen_Ioo.mem_nhds hzero)
  have hi : ∀ᶠ q in 𝓝 p₀, A (q, 0) = q := by
    filter_upwards [closedBall_mem_nhds p₀ hr] with q hq
    exact congrArg Prod.fst (hβ q hq).1
  have hs : ∀ᶠ z in 𝓝 (p₀, (0 : ℝ)), HasDerivAt (fun s => A (z.1, s))
      (heatRadialFrameField g c (A z)) z.2 := by
    filter_upwards [hdom] with z hz
    exact ((hβ z.1 hz.1).2 z.2 hz.2).2.fst
  refine ⟨{
    radius := r
    radius_pos := hr
    time := ε
    time_pos := hε
    map := A
    continuous := hAc
    initial := fun q hq => congrArg Prod.fst (hβ q hq).1
    in_chart := fun q hq t ht => ((hβ q hq).2 t ht).1
    derivative := fun q hq t ht => ((hβ q hq).2 t ht).2.fst
    regular := ?_ }⟩
  intro n
  exact FlowCalculus.local_flow_contDiffAt_finite n HeatRadialFrameSpace
    (heatRadialFrameField g c) A p₀ (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (contDiffAt_zero.mpr ⟨_, hdom, hAc⟩) hi hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth finite-order endpoint frames for arbitrary small velocities,
including zero. The frame equations and orthonormality come from the
constructed horizontal ODE, not from a choice of unit directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatRadialFrameEndpoint {g : SmoothMetric M} {c : M} {p : CoordinateFrameSpace}
    (F : HeatRadialFrameFlow g c p) (t : ℝ) (v : FourSpace) : CoordinateFrameSpace :=
  (F.map ((t⁻¹ • v, p), t)).2

theorem heatRadialFrameEndpoint_zero {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) : heatRadialFrameEndpoint F t 0 = p := by
  simp only [heatRadialFrameEndpoint, smul_zero, F.stationary t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial volume bound for the metric fields. The Weyl identities
are Gursky--LeBrun (1999), equations (3), (12) and Lemma 1; spherical
disintegration and parallel flow are Brin--Karcher (1984), Section 1.
The Jacobi/polar construction retains the ordinary ODE and polar density
formula (Sakai, Chapter II, Section 5), together with the diameter truncation.
No curvature-energy bound or radial-volume deficit is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.geometricVolumeNormedAddCommGroup
local instance geometricVolumeNormedSpace_rd0f954_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace
theorem WeylEnergyIdentities.curvature_energy {g : SmoothMetric M}
    {o : FrameOrientation g} {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (w : WeylEnergyIdentities g o μ) (h : FollandMoments) (hRic : RicciThree g)
    (hnorm : PetersenOrientedNormInput o) (hvolume : FinitePositiveVolume g)
    (hCi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2) μ) :
    (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) =
      (3 / 2) * (∫ c, plusNorm o c ^ 2 + minusNorm o c ^ 2 ∂normalizedVolume g) := by
  have hi := orientedNormSquares_integrable o hnorm hvolume
  exact frameCurvatureField_mean_square g w.averaging h _ hCi
    (hi.1.add hi.2) (frameCurvatureField_directionInvariant g)
    (fun _ e => actual_einstein_decomposition e hRic)
    (fun _ e => actual_weyl_traceFree e hRic) (actual_baseCurvature o hRic)

theorem WeylEnergyIdentities.derivative_energy {g : SmoothMetric M}
    {o : FrameOrientation g} {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (w : WeylEnergyIdentities g o μ) (d : MetricGreenData g μ)
    (opposite : OppositeWeylData d) (hparallel : ParallelReflection d) (h : FollandMoments)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (hnorm : PetersenOrientedNormInput o) (hvolume : FinitePositiveVolume g)
    (hDi : Integrable (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) μ) :
    (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤
      (9 / 4) * (∫ c, plusNorm o c ^ 2 + minusNorm o c ^ 2 ∂normalizedVolume g) := by
  have hi := orientedNormSquares_integrable o hnorm hvolume
  exact frame_derivative_energy_le_of_parallel_data d opposite hparallel o w.averaging h
    hDi (totalGradientEnergy_integrable d opposite o hRic hvolume)
    (frameCurvatureDerivative_directionInvariant g hRic)
    (fun _ e q => frameCurvatureDerivative_turn e hRic q)
    (actual_baseDerivative o hRic) (actual_baseCurvature o hRic) hi.1 hi.2 hRic hpositive

end

end PositiveEinsteinFour.Geometry
end


section

/-! A common radial-frame flow for nearby centers and nearby initial frames.
This retains joint finite regularity instead of choosing a new flow at each center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M} {p : CoordinateFrameSpace}

theorem heatRadialFrameFamily_zero (F : HeatRadialFrameFlow g c p)
    (q : CoordinateFrameSpace) (hq : ((0 : FourSpace), q) ∈ closedBall (0, p) F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) : heatRadialFrameFamily F t (0, q) = q := by
  simp only [heatRadialFrameFamily, smul_zero, F.stationary_at q hq t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! In the vanishing Weyl summand the actual curvature operator is the
identity. This is the finite-dimensional input to harmonic vanishing. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian
open scoped BigOperators Manifold ContDiff
noncomputable section

theorem halfFlat_curvature_matrix_negative (T : Matrix (Fin 3) (Fin 3) ℝ)
    (a : TwoFormFour) (ha : twoFormHodge a = -a) :
    twoFormMatrixMul (twoFormCurvatureMatrix (fun v =>
      einsteinCurvatureTensor T 0 (v 0) (v 1) (v 2) (v 3))) a = a := by
  have h3 : a 3 = -a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = -a 1 at h
    linarith
  have h5 : a 5 = -a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  ext i
  fin_cases i <;>
    simp [twoFormMatrixMul, twoFormCurvatureMatrix, einsteinCurvatureTensor,
      blockTensor, twoFormProduct, quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      AlgebraicCurvature.pair, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h3, h4, h5] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_curvature_action_negative (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) (x : M)
    (a : TwoFormFour) (ha : twoFormHodge a = -a) :
    twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩) a = a := by
  let e : FrameBundle g := ⟨x,o.frame x⟩
  have hlast : ∀ i j k l, twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have heq : twoFormMetricCurvatureTensor g e = fun v =>
      einsteinCurvatureTensor (plusWeyl g x (o.frame x)) 0 (v 0) (v 1) (v 2) (v 3) := by
    funext v
    have hv : v = ![v 0, v 1, v 2, v 3] := by ext i; fin_cases i <;> rfl
    rw [hv]
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    rw [actual_einstein_decomposition e.frame hRic]
    rw [show minusWeyl g e.base e.frame = 0 from hminus x]
    rfl
  rw [← twoFormCurvatureMatrix_apply _ hlast, heq]
  exact halfFlat_curvature_matrix_negative _ a ha

end
end PositiveEinsteinFour.Geometry
end


section

/-! Disintegration of the constructed frame probability for functions that
only depend on the first frame direction. The measure is the actual product
of normalized Riemannian volume and oriented orthogonal Haar probability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- The canonical frame probability gives the averaged energy identities. -/
theorem canonicalFrameMeasure_energy (g : SmoothMetric M) (o : FrameOrientation g) :
    WeylEnergyIdentities g o (canonicalFrameMeasure g o) where
  averaging := canonicalFrameMeasure_averaging g o

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The regularized Weyl cube root is an actual smooth base scalar.
Its moments and Dirichlet energy agree with the frame quantities in the
regularized gap argument. The sharp scalar inequality remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weylScalarFrameCompact
/-- The sharp scalar inequality in normalized base volume, with the actual
Dirichlet pairing. Its geometric proof is independent of this transfer. -/
def SharpScalarSobolev (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o)) : Prop :=
  ∀ a : SmoothScalar (M := M),
    Real.sqrt (∫ x, a.val x ^ 4 ∂normalizedVolume g) ≤
      (∫ x, a.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet p a a / 2

theorem canonicalParallelMetricData_orientation (o : FrameOrientation g)
    (hRic : RicciThree g) :
    OrientationPreservingFlow (canonicalParallelMetricData g o hRic).toMetricGreenData o := by
  intro i t e
  exact ((canonicalParallelMetricData g o hRic).flow i).orientation_preserving
    (fun e => actualParallelMetricData_zero g (canonicalFrameMeasure g o)
      (parallelFrameFlowMap_measurePreserving g o) hRic i e) o t e

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed radial frame lies over the actual exponential map,
by uniqueness of the metric Hamiltonian trajectories. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem heatRadialCotangentState_frame (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) :
    heatRadialCotangentState g c v (frameCoordinateState g c e) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
  rw [frameMomentumMap_apply g c e he v]
  rfl

theorem heatRadialFrameEndpoint_exponential (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (F : HeatRadialFrameFlow g c (frameCoordinateState g c e))
    (K : KineticLocalFlow g c (chartAt FourSpace c e.base, 0))
    (hT : K.time ≤ F.time) (t : ℝ) (ht : t ∈ Ioo (-K.time) K.time) (ht0 : 0 < t) :
    (fun v => (heatRadialFrameEndpoint F t v).1) =ᶠ[𝓝 0]
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
  let p := frameCoordinateState g c e
  have hFinit : ∀ᶠ v : FourSpace in 𝓝 0, (v, p) ∈ closedBall (0, p) F.radius := by
    have hc : Continuous (fun v : FourSpace => (v, p)) := continuous_id.prodMk continuous_const
    exact hc.continuousAt.preimage_mem_nhds (closedBall_mem_nhds (0, p) F.radius_pos)
  have hKinit : ∀ᶠ v : FourSpace in 𝓝 0,
      heatRadialCotangentState g c v p ∈ ball (p.1, 0) K.radius := by
    have hc : Continuous (fun v => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) :=
      continuous_const.prodMk (frameMomentumMap g c e).continuous
    have hc0 : ContinuousAt (fun v =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 := hc.continuousAt
    have hh := hc0.preimage_mem_nhds
      (by simpa only [map_zero] using
        ball_mem_nhds (chartAt FourSpace c e.base, (0 : FourSpace)) K.radius_pos)
    filter_upwards [hh] with v hv
    change heatRadialCotangentState g c v (frameCoordinateState g c e) ∈ _
    rw [heatRadialCotangentState_frame g c e he v]
    exact hv
  have hraw : ∀ᶠ v : FourSpace in 𝓝 0,
      (F.map ((v, p), t)).2.1 = chartAt FourSpace c (frameExponential g o e (t • v)) := by
    filter_upwards [hFinit, hKinit,
      frameExponential_chart_eventually_kinetic g o c e he K t ht ht0] with v hv hKv hexp
    have h := congrArg Prod.fst (F.kinetic_eq K hT v hv hKv t ht)
    rw [heatRadialCotangentState_frame g c e he v] at h
    exact h.symm.trans hexp.symm
  have hs : Tendsto (fun v : FourSpace => t⁻¹ • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun v : FourSpace => t⁻¹ • v) :=
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).continuous
    have h := (show ContinuousAt (fun v : FourSpace => t⁻¹ • v) 0 from hc.continuousAt).tendsto
    simpa only [smul_zero] using h
  filter_upwards [hs.eventually hraw] with v hv
  change (F.map ((t⁻¹ • v, p), t)).2.1 = _
  rw [hv, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common chart interval works for every direction and every nearby
initial frame. Compactness is used only for the unit direction sphere. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_common_source (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
      ∀ e' ∈ U, ∀ v ∈ ball (0 : FourSpace) r,
        frameExponential g o e' v ∈ (chartAt FourSpace c).source := by
  obtain ⟨U, hU, heU, r, hr, hchart⟩ := unitGeodesic_common_chart g o c e he
  refine ⟨U, hU, heU, r, hr, ?_⟩
  intro e' he' v hv
  have hvnorm : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hv
  by_cases hv0 : v = 0
  · subst v
    rw [frameExponential_zero]
    have hh := hchart e' he' firstDirection 0 (by constructor <;> linarith)
    simpa only [unitGeodesic_turn_zero] using hh
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv0⟩
    let q := (euclideanPolarHomeomorph w).1
    let ρ := (euclideanPolarHomeomorph w).2
    have hρ : 0 < ρ.val := ρ.property
    have hρnorm : ρ.val = ‖v‖ := homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    have hvr : ρ.val • q.val = v := congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
    have hh := frameExponential_radial g o e' q ρ
    rw [hvr] at hh
    rw [hh]
    exact hchart e' he' q ρ.val ⟨by linarith, hρnorm ▸ hvnorm⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth orthonormal frames over the actual normal exponential
chart, constructed by radial parallel transport through zero velocity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

theorem exists_heatRadialNormalFrame_flow (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (n : ℕ) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e), ∃ t > (0 : ℝ),
      t ∈ Ioo (-F.time) F.time ∧ ContDiffAt ℝ n (heatRadialFrameEndpoint F t) 0 ∧
      (fun v => (heatRadialFrameEndpoint F t v).1) =ᶠ[𝓝 0]
        (fun v => chartAt FourSpace c (frameExponential g o e v)) ∧
      ∀ᶠ v in 𝓝 (0 : FourSpace),
        (heatRadialFrameEndpoint F t v).1 ∈ (chartAt FourSpace c).target ∧
        (heatRadialFrameEndpoint F t v).2ᵀ *
          metricInChart g c (heatRadialFrameEndpoint F t v).1 *
          (heatRadialFrameEndpoint F t v).2 = 1 := by
  let p := frameCoordinateState g c e
  have hp : p.1 ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source he
  obtain ⟨F₀⟩ := exists_heatRadialFrameFlow g c p hp
  obtain ⟨K₀⟩ := exists_kineticLocalFlow g c (p.1, 0) hp
  let δ := min F₀.time K₀.time
  have hδ : 0 < δ := lt_min F₀.time_pos K₀.time_pos
  let F := F₀.restrictTime δ hδ (min_le_left _ _)
  let K := K₀.restrictTime δ hδ (min_le_right _ _)
  obtain ⟨t, ht, htI, hFt⟩ := F.exists_pos_slice n
  let A : FourSpace → HeatRadialFrameSpace := fun v => (t⁻¹ • v, p)
  let P := heatRadialFrameEndpoint F t
  have hL : ContDiff ℝ ∞ (fun v : FourSpace => t⁻¹ • v) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff
  have hA : ContDiff ℝ ∞ A := hL.prodMk contDiff_const
  have hA0 : A 0 = (0, p) := by simp [A]
  have hFt' : ContDiffAt ℝ n (fun q => F.map (q, t)) (A 0) := by
    simpa only [hA0] using hFt
  have hP : ContDiffAt ℝ n P 0 :=
    (ContDiffAt.comp (f := A) (g := fun q => F.map (q, t)) 0 hFt'
      (hA.contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by first | simp | exact_mod_cast le_top))).snd
  refine ⟨F, t, ht, htI, hP, ?_, ?_⟩
  · exact heatRadialFrameEndpoint_exponential g o c e he F K le_rfl t htI ht
  · have hnear : ∀ᶠ v in 𝓝 (0 : FourSpace), A v ∈ closedBall (0, p) F.radius :=
      hA.continuous.continuousAt.preimage_mem_nhds (by
        rw [hA0]
        exact closedBall_mem_nhds (0, p) F.radius_pos)
    filter_upwards [hnear] with v hv
    refine ⟨F.in_chart (A v) hv t htI, ?_⟩
    exact (F.gram (A v) hv t htI).trans (frameChartMatrix_normalizes g c e he)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential maps of all nearby frames agree with one
kinetic flow on a common velocity ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem KineticLocalFlow.common_exponential_endpoint (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (K : KineticLocalFlow g c (chartAt FourSpace c e.base, 0)) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ ε > (0 : ℝ),
      ∀ e' ∈ U, e'.base ∈ (chartAt FourSpace c).source ∧
        ∀ v : FourSpace, ‖v‖ < ε → ∀ t ∈ Ioo (-K.time) K.time, 0 < t →
          (K.map ((chartAt FourSpace c e'.base, frameMomentumMap g c e' v), t)).1 =
            chartAt FourSpace c (frameExponential g o e' (t • v)) := by
  obtain ⟨U₀, hU₀, he₀, δ, hδ, hchart⟩ := unitGeodesic_common_chart g o c e he
  let p := frameCoordinateState g c e
  obtain ⟨r, hr, hdomain⟩ := heatRadialCotangentState_common_domain g c p
    ((chartAt FourSpace c).map_source he) K.radius K.radius_pos
  have hcoord : {e' : FrameBundle g | frameCoordinateState g c e' ∈ ball p r} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g c e he).preimage_mem_nhds (ball_mem_nhds _ hr)
  have hsource : {e' : FrameBundle g | e'.base ∈ (chartAt FourSpace c).source} ∈ 𝓝 e :=
    (continuous_frameBase g).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds he)
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU₀.mem_nhds he₀) (Filter.inter_mem hcoord hsource))
  let ε := min r (δ / (K.time + 1))
  have htpos : 0 < K.time + 1 := by linarith [K.time_pos]
  have hε : 0 < ε := lt_min hr (div_pos hδ htpos)
  refine ⟨U, hU, heU, ε, hε, ?_⟩
  intro e' he'
  obtain ⟨he'₀, hq, he'c⟩ := hsub he'
  refine ⟨he'c, ?_⟩
  intro v hv t ht ht0
  have hinit : (chartAt FourSpace c e'.base, frameMomentumMap g c e' v) ∈
      ball (chartAt FourSpace c e.base, 0) K.radius := by
    have hh := hdomain v (hv.trans_le (min_le_left _ _)) (frameCoordinateState g c e') hq
    rw [heatRadialCotangentState_frame g c e' he'c v] at hh
    exact hh
  by_cases hv0 : v = 0
  · subst v
    have hbase : chartAt FourSpace c e'.base ∈ (chartAt FourSpace c).target :=
      (chartAt FourSpace c).map_source he'c
    have heq := K.eq_on _ (by simpa only [map_zero] using hinit)
      (fun _ => (chartAt FourSpace c e'.base, (0 : FourSpace))) rfl
      (fun s _ => by
        rw [kineticHamiltonianField_zero_momentum g c _ hbase]
        exact hasDerivAt_const s _)
    simpa only [map_zero, smul_zero, frameExponential_zero] using congrArg Prod.fst (heq ht)
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv0⟩
    let q := (euclideanPolarHomeomorph w).1
    let ρ := (euclideanPolarHomeomorph w).2
    have hρ : 0 < ρ.val := ρ.property
    have hρnorm : ρ.val = ‖v‖ := homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    have hvr : ρ.val • q.val = v := congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
    have hsmall : ρ.val * (K.time + 1) < δ := by
      rw [hρnorm]
      exact (lt_div_iff₀ htpos).mp (hv.trans_le (min_le_right _ _))
    have hstay (s : ℝ) (hs : s ∈ Ioo (-K.time) K.time) :
        unitGeodesic g o (unitTangentTurn e' q) (ρ.val * s) ∈ (chartAt FourSpace c).source := by
      apply hchart e' he'₀ q (ρ.val * s)
      have hsabs : |s| < K.time := abs_lt.mpr hs
      apply abs_lt.mp
      rw [abs_mul, abs_of_pos hρ]
      nlinarith [abs_nonneg s]
    have hsol (s : ℝ) (hs : s ∈ Ioo (-K.time) K.time) :=
      hasDerivAt_unitTangentRadial_cotangent g o c
        (⟨ρ.val, hρ⟩, unitTangentTurn e' q) s (hstay s hs)
    have heq := K.eq_on _ hinit
      (fun s => unitCotangentState g c ρ.val (unitTangentFlowMap g o (ρ.val * s) (unitTangentTurn e' q)))
      (by simpa only [mul_zero, unitTangentFlowMap_zero, hvr] using
        unitCotangentState_turn g c e' he'c ρ.val q) hsol
    have hexp : frameExponential g o e' (t • v) =
        unitGeodesic g o (unitTangentTurn e' q) (ρ.val * t) := by
      rw [← hvr, smul_smul]
      simpa only [mul_comm] using frameExponential_radial g o e' q ⟨t * ρ.val, mul_pos ht0 hρ⟩
    rw [hexp]
    exact congrArg Prod.fst (heq ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Common geometric domain for normal-frame slices over an open set of
actual frames. Exponential agreement holds throughout the same ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_heatRadialFrameCommonDomain (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, e'.base ∈ (chartAt FourSpace c).source ∧
          ∀ v ∈ ball (0 : FourSpace) r,
            ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (v, frameCoordinateState g c e') ∧
            (t⁻¹ • v, frameCoordinateState g c e') ∈ closedBall (0, frameCoordinateState g c e) F.radius ∧
            (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1 ∈ (chartAt FourSpace c).target ∧
            (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).2ᵀ *
              metricInChart g c (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1 *
                (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).2 = 1 ∧
            (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1 =
              chartAt FourSpace c (frameExponential g o e' v) := by
  let p := frameCoordinateState g c e
  have hp : p.1 ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source he
  obtain ⟨F₀⟩ := exists_heatRadialFrameFlow g c p hp
  obtain ⟨K₀⟩ := exists_kineticLocalFlow g c (p.1, 0) hp
  let δ := min F₀.time K₀.time
  have hδ : 0 < δ := lt_min F₀.time_pos K₀.time_pos
  let F := F₀.restrictTime δ hδ (min_le_left _ _)
  let K := K₀.restrictTime δ hδ (min_le_right _ _)
  obtain ⟨t, ht, htI, R, hR, hfamily⟩ := F.exists_joint_frame_family
  obtain ⟨V, hV, heV, ε, hε, hendpoint⟩ := K.common_exponential_endpoint g o c e he
  obtain ⟨S, hS, hdomain⟩ := heatRadialCotangentState_common_domain g c p hp K.radius K.radius_pos
  have hcoord : {e' : FrameBundle g | frameCoordinateState g c e' ∈ ball p (min R S)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g c e he).preimage_mem_nhds
      (ball_mem_nhds _ (lt_min hR hS))
  obtain ⟨U, hUV, hU, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hV.mem_nhds heV) hcoord)
  let r := min R (t * min ε S) / 2
  have hr : 0 < r := half_pos (lt_min hR (mul_pos ht (lt_min hε hS)))
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hR (mul_pos ht (lt_min hε hS))))).trans
    (min_le_left _ _)
  have hrT : r ≤ t * min ε S := (half_le_self (le_of_lt (lt_min hR (mul_pos ht (lt_min hε hS))))).trans
    (min_le_right _ _)
  refine ⟨F, t, ht, htI, U, hU, heU, r, hr, ?_⟩
  intro e' he'
  obtain ⟨he'V, hclose⟩ := hUV he'
  obtain ⟨he'c, he'endpoint⟩ := hendpoint e' he'V
  refine ⟨he'c, ?_⟩
  intro v hv
  let q := frameCoordinateState g c e'
  have hvnorm : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hv
  have hzR : (v, q) ∈ ball (0, p) R := by
    change max (dist v 0) (dist q p) < R
    exact max_lt (by simpa only [dist_zero_right] using hvnorm.trans_le hrR)
      ((show dist q p < min R S from hclose).trans_le (min_le_left _ _))
  obtain ⟨hreg, hFinit, hc, hg⟩ := hfamily (v, q) hzR
  have hscaled : ‖t⁻¹ • v‖ < min ε S := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_lt_iff₀ ht).mpr (hvnorm.trans_le hrT)
  have hKinit : heatRadialCotangentState g c (t⁻¹ • v) q ∈ ball (p.1, 0) K.radius :=
    hdomain _ (hscaled.trans_le (min_le_right _ _)) q
      ((show dist q p < min R S from hclose).trans_le (min_le_right _ _))
  have hkin := congrArg Prod.fst (F.kinetic_eq_from K le_rfl (t⁻¹ • v) q hFinit hKinit t htI)
  have hexp := he'endpoint (t⁻¹ • v) (hscaled.trans_le (min_le_left _ _)) t htI ht
  rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at hexp
  rw [heatRadialCotangentState_frame g c e' he'c] at hkin
  refine ⟨hreg, hFinit, hc, hg.trans (frameChartMatrix_normalizes g c e' he'c), ?_⟩
  exact hkin.symm.trans hexp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial scaling identifies the endpoint derivative with the actual
horizontal frame field. This is the radial parallel-transport identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatRadialFrameEndpoint_radial_derivative {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (t : ℝ) (ht : 0 < t) (htF : t < F.time) (x : FourSpace)
    (hx : (t⁻¹ • x, p) ∈ ball (0, p) F.radius)
    (hP : DifferentiableAt ℝ (heatRadialFrameEndpoint F t) x) :
    fderiv ℝ (heatRadialFrameEndpoint F t) x x =
      (heatRadialFrameField g c (x, heatRadialFrameEndpoint F t x)).2 := by
  let v := t⁻¹ • x
  let q : HeatRadialFrameSpace := (v, p)
  have htI : t ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], htF⟩
  have heq : (fun r : ℝ => heatRadialFrameEndpoint F t (r • x)) =ᶠ[𝓝 1]
      (fun r => (F.map (q, r * t)).2) := by
    filter_upwards [F.scaling_eventually v hx t ht htF] with r hr
    have hi : t⁻¹ • (r • x) = r • v := by simp only [v, smul_smul, mul_comm]
    change (F.map ((t⁻¹ • (r • x), p), t)).2 = _
    rw [hi, hr]
    rfl
  have hs : HasDerivAt (fun r : ℝ => r • x) x 1 := by
    have h := (ContinuousLinearMap.toSpanSingleton ℝ x).hasFDerivAt.comp_hasDerivAt
      1 (hasDerivAt_id 1)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      Function.comp_def, id_eq] using! h
  have hleft : HasDerivAt (fun r : ℝ => heatRadialFrameEndpoint F t (r • x))
      (fderiv ℝ (heatRadialFrameEndpoint F t) x x) 1 := by
    have hPx : HasFDerivAt (heatRadialFrameEndpoint F t)
        (fderiv ℝ (heatRadialFrameEndpoint F t) x) ((1 : ℝ) • x) := by
      simpa only [one_smul] using hP.hasFDerivAt
    exact hPx.comp_hasDerivAt 1 hs
  have hright : HasDerivAt (fun r : ℝ => (F.map (q, r * t)).2)
      (t • (heatRadialFrameField g c (F.map (q, t))).2) 1 := by
    have hd : HasDerivAt (fun s => (F.map (q, s)).2)
        (heatRadialFrameField g c (F.map (q, t))).2 t :=
      (F.derivative q (ball_subset_closedBall hx) t htI).snd
    have hd' : HasDerivAt (fun s => (F.map (q, s)).2)
        (heatRadialFrameField g c (F.map (q, t))).2 (id 1 * t) := by
      simpa only [id_eq, one_mul] using hd
    have h := hd'.scomp 1
      ((hasDerivAt_id 1).mul_const t)
    simpa only [one_mul, one_mul, id_eq, Function.comp_def] using! h
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  rw [hd]
  have hdir : (F.map (q, t)).1 = t⁻¹ • x := F.direction q (ball_subset_closedBall hx) t htI
  have hscale : heatRadialDirectionScale t (F.map (q, t)) =
      (x, heatRadialFrameEndpoint F t x) := by
    apply Prod.ext
    · change t • (F.map (q, t)).1 = x
      rw [hdir, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    · rfl
  exact (congrArg Prod.snd (heatRadialFrameField_scale g c t (F.map (q, t)))).symm.trans
    (congrArg (fun z => (heatRadialFrameField g c z).2) hscale)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal frame satisfies the radial horizontal equation
throughout a neighborhood of zero, with the finite regularity needed for
the heat coefficient construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_heatNormalFrame_transport (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ P : FourSpace → CoordinateFrameSpace,
      ContDiffAt ℝ 12 P 0 ∧ P 0 = frameCoordinateState g c e ∧
      ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
        (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
        (P x).1 ∈ (chartAt FourSpace c).target ∧
        (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
        DifferentiableAt ℝ P x ∧
        fderiv ℝ P x x = (heatRadialFrameField g c (x, P x)).2 := by
  obtain ⟨F, t, ht, htI, hreg, hbase, hgram⟩ :=
    exists_heatRadialNormalFrame_flow g o c e he 12
  let p := frameCoordinateState g c e
  let P := heatRadialFrameEndpoint F t
  let A : FourSpace → HeatRadialFrameSpace := fun x => (t⁻¹ • x, p)
  have hL : Continuous (fun x : FourSpace => t⁻¹ • x) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).continuous
  have hA : Continuous A := hL.prodMk continuous_const
  have hA0 : A 0 = (0, p) := by simp [A]
  have hinit : ∀ᶠ x in 𝓝 (0 : FourSpace), A x ∈ ball (0, p) F.radius :=
    hA.continuousAt.preimage_mem_nhds (by
      rw [hA0]
      exact ball_mem_nhds (0, p) F.radius_pos)
  have hdiff : ∀ᶠ x in 𝓝 (0 : FourSpace), DifferentiableAt ℝ P x := by
    have hh := (hreg.of_le (show (1 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by first | simp | exact_mod_cast le_top)
    filter_upwards [hh] with x hx
    exact hx.differentiableAt one_ne_zero
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
      (P x).1 ∈ (chartAt FourSpace c).target ∧
      (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
      DifferentiableAt ℝ P x ∧ A x ∈ ball (0, p) F.radius := by
    filter_upwards [hbase, hgram, hdiff, hinit] with x hb hg hd hi
    exact ⟨hb, hg.1, hg.2, hd, hi⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨P, hreg, heatRadialFrameEndpoint_zero F t htI, r, hr, ?_⟩
  intro x hx
  obtain ⟨hb, hc, hg, hd, hi⟩ := hball hx
  exact ⟨hb, hc, hg, hd, heatRadialFrameEndpoint_radial_derivative F t ht htI.2 x hi hd⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual pulled-back frame connection has zero radial contraction.
The connection uses the differential of the constructed frame and the
Levi-Civita connection of its base map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormalFrameConnection_radial (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : fderiv ℝ P x x = (heatRadialFrameField g c (x, P x)).2) :
    (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0 := by
  let D := fderiv ℝ P x
  let V := (P x).2 *ᵥ WithLp.ofLp x
  let C := ∑ r : Fin 4, V r • connectionMatrix g c r (P x).1
  have hdx : D x = (WithLp.toLp 2 V, -(C * (P x).2)) := hP
  have hlin : D x = ∑ i : Fin 4, x i • D (coordinateVector i) := by
    have hx : (∑ i : Fin 4, x i • coordinateVector i) = x :=
      sum_coordinateVector (WithLp.ofLp x)
    calc
      D x = D (∑ i : Fin 4, x i • coordinateVector i) := congrArg D hx.symm
      _ = _ := by rw [map_sum]; simp only [map_smul]
  have hbase : (∑ i : Fin 4, x i • (D (coordinateVector i)).1) = WithLp.toLp 2 V := by
    let L := ContinuousLinearMap.fst ℝ FourSpace Mat4
    have he := congrArg L (hlin.symm.trans hdx)
    simpa only [map_sum, map_smul] using! he
  have hframe : (∑ i : Fin 4, x i • (D (coordinateVector i)).2) = -(C * (P x).2) := by
    let L := ContinuousLinearMap.snd ℝ FourSpace Mat4
    have he := congrArg L (hlin.symm.trans hdx)
    simpa only [map_sum, map_smul] using! he
  have hcoordinate (r : Fin 4) : (∑ i : Fin 4, x i * (D (coordinateVector i)).1 r) = V r := by
    have h := congrArg (fun v : FourSpace => v r) hbase
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      WithLp.ofLp_toLp] using h
  let B := fun i : Fin 4 => ∑ r : Fin 4, (D (coordinateVector i)).1 r •
    connectionMatrix g c r (P x).1
  have hB : (∑ i : Fin 4, x i • B i) = C := by
    change (∑ i : Fin 4, x i • ∑ r : Fin 4, (D (coordinateVector i)).1 r •
      connectionMatrix g c r (P x).1) = _
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_smul, hcoordinate]
  change (∑ i : Fin 4, x i • ((P x).2⁻¹ *
    ((D (coordinateVector i)).2 + B i * (P x).2))) = 0
  calc
    _ = ∑ i : Fin 4, (P x).2⁻¹ *
        (x i • (D (coordinateVector i)).2 + (x i • B i) * (P x).2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_smul_comm, smul_add, smul_mul_assoc]
    _ = (P x).2⁻¹ * ((∑ i : Fin 4, x i • (D (coordinateVector i)).2) +
        (∑ i : Fin 4, x i • B i) * (P x).2) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add]
    _ = 0 := by rw [hframe, hB]; simp

variable [T2Space M] [CompactSpace M]

theorem exists_heatNormalFrame_radial_connection (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ P : FourSpace → CoordinateFrameSpace,
      ContDiffAt ℝ 12 P 0 ∧ P 0 = frameCoordinateState g c e ∧
      ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
        (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
        (P x).1 ∈ (chartAt FourSpace c).target ∧
        (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
        DifferentiableAt ℝ P x ∧
        (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0 := by
  obtain ⟨P, hP, hP0, r, hr, h⟩ := exists_heatNormalFrame_transport g o c e he
  refine ⟨P, hP, hP0, r, hr, ?_⟩
  intro x hx
  obtain ⟨hb, hc, hg, hd, hrad⟩ := h x hx
  exact ⟨hb, hc, hg, hd, heatNormalFrameConnection_radial g c P x hrad⟩

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The concrete normal-frame data used by the two-form heat construction.
Every field is obtained from the actual radial frame flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_heatNormalFrameData (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    Nonempty (HeatNormalFrameData g o c e) := by
  obtain ⟨P, hP, hP0, r, hr, h⟩ := exists_heatNormalFrame_radial_connection g o c e he
  obtain ⟨_, hc0, hG0, _, _⟩ := h 0 (mem_ball_self hr)
  have hdet : (P 0).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hG0
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  refine ⟨{
    point := P
    regular := hP
    initial := hP0
    radius := r
    radius_pos := hr
    exponential := fun x hx => (h x hx).1
    in_chart := fun x hx => (h x hx).2.1
    orthonormal := fun x hx => (h x hx).2.2.1
    differentiable := fun x hx => (h x hx).2.2.2.1
    radial_connection := fun x hx => (h x hx).2.2.2.2
    connection_regular := ?_ }⟩
  intro i j k
  exact heatNormalFrameConnection_contDiffAt 11 g c P 0 hP hc0 hdet i j k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The initial frame derivative gives a genuine joint inverse and a
common injectivity radius for the actual normal-coordinate family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyBaseAugment_actual_inverse (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 12 P (0, frameCoordinateState g e.base e))
    (hexp : (fun x => (P (x, frameCoordinateState g e.base e)).1) =ᶠ[𝓝 0]
      (fun x => chartAt FourSpace e.base (frameExponential g o e x))) :
    ∃ H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace,
      (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P ∧
      ((0 : FourSpace), frameCoordinateState g e.base e) ∈ H.source ∧
      ContDiffAt ℝ 12 H.symm
        (heatFamilyBaseAugment P (0, frameCoordinateState g e.base e)) := by
  have hL := frameMap_isUnit g e
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = e.frame.map.toContinuousLinearMap := hL.unit_spec
  have hd := (frameExponential_chart_strictDerivative_zero g o e.base e
    (mem_chart_source FourSpace e.base)).hasFDerivAt
  rw [chartForwardOperator_center, ContinuousLinearMap.id_comp] at hd
  have hs : HasFDerivAt (fun x => (P (x, frameCoordinateState g e.base e)).1)
      (A : FourSpace →L[ℝ] FourSpace) 0 := by
    rw [hA]
    exact hd.congr_of_eventuallyEq hexp
  exact heatFamilyBaseAugment_local_inverse P _ hP A hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The same positive radius supports actual normal-frame data for every
frame in one open neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalFrameCommonData (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, e'.base ∈ (chartAt FourSpace c).source ∧
          ∃ D : HeatNormalFrameData g o c e', D.radius = r ∧
            (D.point = fun v => heatRadialFrameFamily F t (v, frameCoordinateState g c e')) ∧
            ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (0, frameCoordinateState g c e') := by
  obtain ⟨F, t, ht, htI, U₀, hU₀, he₀, R, hR, hdata⟩ :=
    exists_heatRadialFrameCommonDomain g o c e he
  let p := frameCoordinateState g c e
  have hnear : {e' : FrameBundle g | frameCoordinateState g c e' ∈ ball p (F.radius / 2)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g c e he).preimage_mem_nhds
      (ball_mem_nhds _ (half_pos F.radius_pos))
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hnear)
  let r := min R (t * (F.radius / 4)) / 2
  have hr : 0 < r := half_pos (lt_min hR (mul_pos ht (by linarith [F.radius_pos])))
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hR
    (mul_pos ht (by linarith [F.radius_pos]))))).trans (min_le_left _ _)
  have hrt : r ≤ t * (F.radius / 4) := (half_le_self (le_of_lt (lt_min hR
    (mul_pos ht (by linarith [F.radius_pos]))))).trans (min_le_right _ _)
  refine ⟨F, t, ht, htI, U, hU, heU, r, hr, ?_⟩
  intro e' he'
  obtain ⟨he'₀, hqnear⟩ := hsub he'
  obtain ⟨he'c, hfields⟩ := hdata e' he'₀
  let q := frameCoordinateState g c e'
  let P := fun v => heatRadialFrameFamily F t (v, q)
  have hqdist : dist q p < F.radius / 2 := hqnear
  have hqF : ((0 : FourSpace), q) ∈ ball (0, p) F.radius := by
    change max (dist (0 : FourSpace) 0) (dist q p) < F.radius
    simpa only [dist_self, max_eq_right dist_nonneg] using
      hqdist.trans (by linarith [F.radius_pos])
  let G := F.recenter q hqF
  have hP0 : P 0 = q := heatRadialFrameFamily_zero F q (ball_subset_closedBall hqF) t htI
  have hP : ContDiffAt ℝ 12 P 0 := by
    have hh := (hfields 0 (mem_ball_self hR)).1
    exact ContDiffAt.comp (f := fun v : FourSpace => (v, q))
      (g := heatRadialFrameFamily F t) 0 hh (contDiffAt_id.prodMk contDiffAt_const)
  have hlocal (v : FourSpace) (hv : v ∈ ball 0 r) :
      (P v).1 ∈ (chartAt FourSpace c).target ∧
      (P v).2ᵀ * metricInChart g c (P v).1 * (P v).2 = 1 ∧
      DifferentiableAt ℝ P v ∧
      (∑ i : Fin 4, v i • heatNormalFrameConnection g c P i v) = 0 ∧
      (P v).1 = chartAt FourSpace c (frameExponential g o e' v) := by
    obtain ⟨hreg, _, hc, hg, hexp⟩ := hfields v (ball_subset_ball hrR hv)
    have hd : DifferentiableAt ℝ P v :=
      (ContDiffAt.comp (f := fun w : FourSpace => (w, q))
        (g := heatRadialFrameFamily F t) v hreg
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
    have hscaled : ‖t⁻¹ • v‖ < F.radius / 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      apply (inv_mul_lt_iff₀ ht).mpr
      exact (show ‖v‖ < r from by simpa only [mem_ball, dist_zero_right] using hv).trans_le hrt
    have hG : (t⁻¹ • v, q) ∈ ball (0, q) G.radius := by
      change max (dist (t⁻¹ • v) 0) (dist q q) < (F.radius - dist (0, q) (0, p)) / 2
      have hdq : dist ((0 : FourSpace), q) (0, p) = dist q p := by
        change max (dist (0 : FourSpace) 0) (dist q p) = dist q p
        simp only [dist_self, max_eq_right dist_nonneg]
      rw [hdq, dist_self, dist_zero_right, max_eq_left (norm_nonneg _)]
      linarith
    have hrad : fderiv ℝ P v v = (heatRadialFrameField g c (v, P v)).2 :=
      heatRadialFrameEndpoint_radial_derivative G t ht htI.2 v hG hd
    exact ⟨hc, hg, hd, heatNormalFrameConnection_radial g c P v hrad, hexp⟩
  have hc0 := (hlocal 0 (mem_ball_self hr)).1
  have hdet : (P 0).2.det ≠ 0 := by
    have hg := congrArg Matrix.det (hlocal 0 (mem_ball_self hr)).2.1
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  refine ⟨he'c, {
    point := P
    regular := hP
    initial := hP0
    radius := r
    radius_pos := hr
    exponential := fun v hv => (hlocal v hv).2.2.2.2
    in_chart := fun v hv => (hlocal v hv).1
    orthonormal := fun v hv => (hlocal v hv).2.1
    differentiable := fun v hv => (hlocal v hv).2.2.1
    radial_connection := fun v hv => (hlocal v hv).2.2.2.1
    connection_regular := fun i j k => heatNormalFrameConnection_contDiffAt 11 g c P 0 hP hc0 hdet i j k
  }, rfl, rfl, (hfields 0 (mem_ball_self hR)).1⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Nearby frames share a genuine normal chart radius, a jointly
regular parallel frame, and four derivatives of the inverse chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalCommonChart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ F : HeatRadialFrameFlow g e.base (frameCoordinateState g e.base e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (0, frameCoordinateState g e.base e) ∧
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, ∃ D : HeatNormalFrameData g o e.base e',
          ∃ C : OpenPartialHomeomorph FourSpace M,
            (D.point = fun x => heatRadialFrameFamily F t (x, frameCoordinateState g e.base e')) ∧
            C.source = ball 0 r ∧ EqOn C (frameExponential g o e') C.source ∧
            C.target ⊆ (chartAt FourSpace e.base).source ∧
            ContMDiffOn I4 I4 4 C.symm C.target ∧ r ≤ D.radius := by
  have he : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  obtain ⟨F, t, ht, htI, U₀, hU₀, he₀, R, hR, hD⟩ :=
    exists_heatNormalFrameCommonData g o e.base e he
  let p := frameCoordinateState g e.base e
  let P := heatRadialFrameFamily F t
  obtain ⟨_, D₀, hD₀R, hD₀P, hP⟩ := hD e he₀
  have hexp : (fun x => (P (x, p)).1) =ᶠ[𝓝 0]
      (fun x => chartAt FourSpace e.base (frameExponential g o e x)) := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D₀.radius_pos] with x hx
    simpa only [hD₀P] using D₀.exponential x hx
  obtain ⟨H, hH, hH0, hi⟩ := heatFamilyBaseAugment_actual_inverse g o e P hP hexp
  obtain ⟨S, hS, hslice⟩ := heatFamilySliceChart_uniform P p H hH hH0 hP hi
  obtain ⟨U₁, hU₁, he₁, T, hT, hsource⟩ := frameExponential_common_source g o e.base e he
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p S} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e he).preimage_mem_nhds (ball_mem_nhds _ hS)
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU₀.mem_nhds he₀) (Filter.inter_mem (hU₁.mem_nhds he₁) hcoord))
  let r := min R (min S T)
  have hr : 0 < r := lt_min hR (lt_min hS hT)
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r ≤ S := (min_le_right _ _).trans (min_le_left _ _)
  have hrT : r ≤ T := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨F, t, ht, htI, hP, U, hU, heU, r, hr, ?_⟩
  intro e' he'
  obtain ⟨he'₀, he'₁, hq⟩ := hsub he'
  obtain ⟨_, D, hDR, hDP, _⟩ := hD e' he'₀
  have hrD : r ≤ D.radius := hDR ▸ hrR
  have hs (x : FourSpace) (hx : x ∈ ball 0 r) :=
    hslice (frameCoordinateState g e.base e') hq x (ball_subset_ball hrS hx)
  obtain ⟨C, hC, hCE, hCt, hCi⟩ := heatFamily_manifold_chart D P hDP H hH r hr hrD
    (fun x hx => hsource e' he'₁ x (ball_subset_ball hrT hx))
    (fun x hx => (hs x hx).1) (fun x hx => (hs x hx).2)
  exact ⟨D, C, hDP, hC, hCE, hCt, hCi, hrD⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weitzenböck curvature potential in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.potential_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (k l : Fin 6) :
    ContDiffAt ℝ 12 (fun y => heatNormalPotential g c D.point y k l) 0 :=
  heatNormalPotential_contDiffAt 12 g c D.point 0 D.regular
    (D.in_chart 0 (Metric.mem_ball_self D.radius_pos)) k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint curvature and two-form connection coefficients of the actual
normal-frame family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyCurvature_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ n P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (v : Fin 4 → Fin 4) :
    ContDiffAt ℝ n (fun y => heatFamilyCurvature g c P y v) z := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hR (w : Fin 4 → Fin 4) :
      ContDiffAt ℝ n (fun y => curvatureCoordinates g c (P y).1 w) z := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun x => curvatureCoordinates g c x w) z
      ((curvatureCoordinates_contDiffAt g c (P z).1 hz
        (metricInChart_posDef g c (P z).1 hz).det_pos.ne' w).of_le (by first | simp | exact_mod_cast le_top)) hP.fst
  unfold heatFamilyCurvature frameTensor
  apply ContDiffAt.sum
  intro w _
  exact (contDiffAt_prod fun i _ => hE (w i) (v i)).mul (hR w)

theorem heatFamilyTwoFormConnection_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target) (hdet : (P z).2.det ≠ 0)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => heatFamilyTwoFormConnection g c P i y k l) z := by
  have hB : ContDiffAt ℝ n (heatFamilyConnection g c P i) z :=
    contDiffAt_pi.mpr (fun j => contDiffAt_pi.mpr
      (heatFamilyConnection_contDiffAt n g c P z hP hz hdet i j))
  let L := (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).toContinuousLinearMap
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hc := π.contDiff.contDiffAt.comp z (L.contDiff.contDiffAt.comp z hB)
  change ContDiffAt ℝ n
    (fun y => heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)
      (heatFamilyConnection g c P i y) k) z at hc
  simpa only [heatConnectionActionLinear_apply, heatFamilyTwoFormConnection,
    heatTwoFormConnectionMatrix] using hc

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The critical Euclidean H1-to-L4 estimate needed by the compact
four-dimensional scalar minimization. The constant here is not sharp;
sharpness on the manifold comes from the nonlinear rigidity argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal NNReal

noncomputable section

namespace ScalarEuclideanSobolev

local notation "V" => FourSpace

theorem critical_estimate {f : V → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    eLpNorm f 4 volume ≤ constant * eLpNorm (fderiv ℝ f) 2 volume := by
  simpa [constant] using
    (eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure V) hf hc
      (p := 2) (p' := 4) (by norm_num) (by simp [FourSpace]) (by
        norm_num [FourSpace]))

theorem toL4_coe (f : ↥(Euclidean.C1c (E := V))) :
    (toL4 f : V → ℝ) =ᵐ[volume] f.val :=
  MemLp.coeFn_toLp _

def toL4Linear : ↥(Euclidean.C1c (E := V)) →ₗ[ℝ] Lp ℝ 4 (volume : Measure V) where
  toFun := toL4
  map_add' f h := by
    apply Lp.ext
    filter_upwards [toL4_coe (f + h), toL4_coe f, toL4_coe h,
      Lp.coeFn_add (toL4 f) (toL4 h)] with x hsum hf hh hLp
    rw [hsum, hLp]
    change f.val x + h.val x = (toL4 f : V → ℝ) x + (toL4 h : V → ℝ) x
    rw [hf, hh]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [toL4_coe (r • f), toL4_coe f,
      Lp.coeFn_smul r (toL4 f)] with x hrf hf hLp
    simp only [RingHom.id_apply]
    rw [hrf, hLp]
    change r * f.val x = r * (toL4 f : V → ℝ) x
    rw [hf]

theorem toL4_bound (f : ↥(Euclidean.C1c (E := V))) :
    ‖toL4Linear f‖ ≤ (constant : ℝ) * ‖gradientL2 f‖ := by
  change ‖toL4 f‖ ≤ (constant : ℝ) * ‖gradientL2 f‖
  have h := critical_estimate f.property.1 f.property.2
  rw [← gradient_eLpNorm f.property.1] at h
  have ht : constant * eLpNorm (Euclidean.grad f.val) 2 volume ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (((Euclidean.continuous_grad f.property.1).memLp_of_hasCompactSupport
        (Euclidean.hasCompactSupport_grad f.property.2)) :
          MemLp (Euclidean.grad f.val) 2 volume).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono ht h
  simpa only [toL4, gradientL2, Lp.norm_toLp,
    ENNReal.toReal_mul, ENNReal.coe_toReal] using hr

end ScalarEuclideanSobolev

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate form of the Euclidean Sobolev estimate. The finite sum of
the four partial L² norms controls the gradient L² norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal

noncomputable section

namespace ScalarEuclideanSobolev

theorem toL4_bound_partials (f : ↥(Euclidean.C1c (E := FourSpace))) :
    ‖toL4Linear f‖ ≤ (constant : ℝ) * ∑ i : Fin 4, ‖partialL2 f i‖ :=
  (toL4_bound f).trans (mul_le_mul_of_nonneg_left (gradientL2_norm_le_sum f)
    (NNReal.coe_nonneg _))

end ScalarEuclideanSobolev

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

/-! The scalar cutoff commutator for the local heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatLocalOperator_cutoff (a : Mat4) (b : Fin 4 → ℝ)
    (f u : FourSpace → ℝ) (x : FourSpace)
    (ha : ∀ i j, a i j = a j i) (hf : ContDiffAt ℝ 2 f x) (hu : ContDiffAt ℝ 2 u x) :
    fourHeatLocalOperator a b 0 (fun y => f y * u y) x =
      f x * fourHeatLocalOperator a b 0 u x +
      fourHeatLocalOperator a b 0 f x * u x -
      2 * ∑ i, ∑ j, a i j * partialDeriv f i x * partialDeriv u j x := by
  have hswap : (∑ i, ∑ j, a i j * partialDeriv f j x * partialDeriv u i x) =
      ∑ i, ∑ j, a i j * partialDeriv f i x * partialDeriv u j x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  have hsecond : (∑ i, ∑ j, a i j *
      partialDeriv (partialDeriv (fun y => f y * u y) i) j x) =
      u x * (∑ i, ∑ j, a i j * partialDeriv (partialDeriv f i) j x) +
      2 * (∑ i, ∑ j, a i j * partialDeriv f i x * partialDeriv u j x) +
      f x * (∑ i, ∑ j, a i j * partialDeriv (partialDeriv u i) j x) := by
    simp_rw [scalar_partial_second_product_at f u x hf hu]
    have he (i j : Fin 4) : a i j *
        (partialDeriv (partialDeriv f i) j x * u x +
          partialDeriv f i x * partialDeriv u j x + partialDeriv f j x * partialDeriv u i x +
          f x * partialDeriv (partialDeriv u i) j x) =
        u x * (a i j * partialDeriv (partialDeriv f i) j x) +
          a i j * partialDeriv f i x * partialDeriv u j x +
          a i j * partialDeriv f j x * partialDeriv u i x +
          f x * (a i j * partialDeriv (partialDeriv u i) j x) := by ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
    ring
  have hfirst : (∑ i, b i * partialDeriv (fun y => f y * u y) i x) =
      u x * (∑ i, b i * partialDeriv f i x) + f x * (∑ i, b i * partialDeriv u i x) := by
    simp_rw [scalar_partial_product f u x (hf.differentiableAt (by norm_num))
      (hu.differentiableAt (by norm_num))]
    have he (i : Fin 4) : b i * (partialDeriv f i x * u x + f x * partialDeriv u i x) =
        u x * (b i * partialDeriv f i x) + f x * (b i * partialDeriv u i x) := by ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold fourHeatLocalOperator
  rw [hsecond, hfirst]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact cutoff commutator for the six-component parametrix operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleOperator_cutoff (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (f : FourSpace → ℝ)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (ha : ∀ i j, a i j = a j i) (hf : ContDiffAt ℝ 2 f x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 6) :
    fourHeatBundleOperator a b B C (fun y l => f y * u y l) x k =
      f x * fourHeatBundleOperator a b B C u x k +
      fourHeatLocalOperator a b 0 f x * u x k -
      2 * (∑ i, ∑ j, a i j * partialDeriv f i x * partialDeriv (fun y => u y k) j x) +
      ∑ i, ∑ l, B i k l * partialDeriv f i x * u x l := by
  have hfirst : fourHeatBundleFirst B (fun y l => f y * u y l) x k =
      f x * fourHeatBundleFirst B u x k +
        ∑ i, ∑ l, B i k l * partialDeriv f i x * u x l := by
    unfold fourHeatBundleFirst
    simp_rw [scalar_partial_product f (fun y => u y _) x
      (hf.differentiableAt (by norm_num)) ((hu _).differentiableAt (by norm_num))]
    have he (i : Fin 4) (l : Fin 6) :
        B i k l * (partialDeriv f i x * u x l + f x * partialDeriv (fun y => u y l) i x) =
        f x * (B i k l * partialDeriv (fun y => u y l) i x) +
          B i k l * partialDeriv f i x * u x l := by ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hzero : fourHeatBundleZero C (fun y l => f y * u y l) x k =
      f x * fourHeatBundleZero C u x k := by
    unfold fourHeatBundleZero
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  unfold fourHeatBundleOperator
  rw [fourHeatLocalOperator_cutoff a b f (fun y => u y k) x ha hf (hu k), hfirst, hzero]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal volume density and leading heat amplitude in a common
family, including their actual exponential identifications. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyLeading_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hdet : 0 < (heatFamilyMetric g c P z).det) :
    ContDiffAt ℝ n (heatFamilyLeading g c P) z := by
  have hJ : 0 < heatFamilyDensity g c P z := Real.sqrt_pos.mpr hdet
  exact ((heatFamilyDensity_contDiffAt n g c P z hP hz hdet.ne').sqrt hJ.ne').inv
    (Real.sqrt_pos.mpr hJ).ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar and matrix coefficients of the two-form heat
operator form one finite-regularity family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyFirst_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z).2.det ≠ 0) (hmetric : (heatFamilyMetric g c P z).det ≠ 0)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => heatFamilyFirst g c P y i k l) z := by
  change ContDiffAt ℝ n (fun y => (-2 : ℝ) * ∑ j : Fin 4,
    (heatFamilyMetric g c P y)⁻¹ i j * heatFamilyTwoFormConnection g c P j y k l) z
  exact contDiffAt_const.mul (ContDiffAt.sum (fun j _ =>
    (heatFamilyInverse_contDiffAt n g c P z hP hz hmetric i j).mul
      (heatFamilyTwoFormConnection_contDiffAt n g c P z hP hz hframe j k l)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar and matrix coefficients of the one-form heat
operator form one finite-regularity family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyOneFirst_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z).2.det ≠ 0) (hmetric : (heatFamilyMetric g c P z).det ≠ 0)
    (i : Fin 4) (k l : Fin 4) :
    ContDiffAt ℝ n (fun y => heatFamilyOneFirst g c P y i k l) z := by
  change ContDiffAt ℝ n (fun y => (-2 : ℝ) * ∑ j : Fin 4,
    (heatFamilyMetric g c P y)⁻¹ i j * heatFamilyConnection g c P j y k l) z
  exact contDiffAt_const.mul (ContDiffAt.sum (fun j _ =>
    (heatFamilyInverse_contDiffAt n g c P z hP hz hmetric i j).mul
      (heatFamilyConnection_contDiffAt n g c P z hP hz hframe j k l)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-regularity coefficients of the two-form operator in
normal coordinates and the radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.bundleFirst_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ 11 (fun x => heatNormalBundleFirst D x i k l) 0 := by
  apply fourHeatConnectionFirst_contDiffAt
  · intro i j
    exact (heatNormalInverse_smoothAt_zero g o e i j).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact D.twoForm_connection_regular

theorem HeatNormalFrameData.bundleZero_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (k l : Fin 6) : ContDiffAt ℝ 10 (fun x => heatNormalBundleZero D x k l) 0 := by
  apply fourHeatConnectionZero_contDiffAt
  · intro i j
    exact (heatNormalInverse_smoothAt_zero g o e i j).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · intro i
    exact (heatNormalDrift_smoothAt_zero g o e i).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact D.twoForm_connection_regular
  · intro k l
    exact (D.potential_regular k l).of_le (by norm_num)

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

theorem fourHeatPolynomial_partial (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ m, ContDiff ℝ 1 (u m)) (t : ℝ) (x : FourSpace) (i : Fin 4) :
    partialDeriv (fourHeatPolynomial u t) i x =
      fourHeatPolynomial (fun m => partialDeriv (u m) i) t x := by
  have h0 := (hu 0).differentiable one_ne_zero
  have h1 := (hu 1).differentiable one_ne_zero
  have h2 := (hu 2).differentiable one_ne_zero
  have h3 := (hu 3).differentiable one_ne_zero
  unfold fourHeatPolynomial
  rw [fourHeat_partial_add _ _ x (by fun_prop) (by fun_prop),
    fourHeat_partial_add _ _ x (by fun_prop) (by fun_prop),
    fourHeat_partial_add _ _ x h0.differentiableAt (by fun_prop)]
  simp only [fourHeat_partial_const_mul]

theorem fourHeatPolynomial_partial_joint_continuous (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ m, ContDiff ℝ 1 (u m)) (i : Fin 4) :
    Continuous (fun z : ℝ × FourSpace => partialDeriv (fourHeatPolynomial u z.1) i z.2) := by
  simp_rw [fourHeatPolynomial_partial u hu]
  exact fourHeatPolynomial_joint_continuous _
    (fun m => (fourHeat_partial_contDiff 0 (u m) (hu m) i).continuous)

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

theorem exists_heatNormalBundleExtension {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e) :
    Nonempty (HeatNormalBundleExtension D) := by
  obtain ⟨base⟩ := exists_heatNormalExtension 10 g o e
  choose B hB hBc hBe using fun i k l => heatScalar_extension 10
    (fun x => heatNormalBundleFirst D x i k l)
    ((D.bundleFirst_regular i k l).of_le (by norm_num))
  choose C hC hCc hCe using fun k l => heatScalar_extension 10
    (fun x => heatNormalBundleZero D x k l) (D.bundleZero_regular k l)
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

/-! Four-component cutoff commutator for the actual one-form heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology
noncomputable section

theorem fourHeatOneOperator_cutoff (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (f : FourSpace → ℝ)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (ha : ∀ i j, a i j = a j i) (hf : ContDiffAt ℝ 2 f x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 4) :
    fourHeatOneOperator a b B C (fun y l => f y * u y l) x k =
      f x * fourHeatOneOperator a b B C u x k +
      fourHeatLocalOperator a b 0 f x * u x k -
      2 * (∑ i, ∑ j, a i j * partialDeriv f i x * partialDeriv (fun y => u y k) j x) +
      ∑ i, ∑ l, B i k l * partialDeriv f i x * u x l := by
  have hfirst : fourHeatOneFirst B (fun y l => f y * u y l) x k =
      f x * fourHeatOneFirst B u x k +
        ∑ i, ∑ l, B i k l * partialDeriv f i x * u x l := by
    unfold fourHeatOneFirst
    simp_rw [scalar_partial_product f (fun y => u y _) x
      (hf.differentiableAt (by norm_num)) ((hu _).differentiableAt (by norm_num))]
    have he (i : Fin 4) (l : Fin 4) :
        B i k l * (partialDeriv f i x * u x l + f x * partialDeriv (fun y => u y l) i x) =
        f x * (B i k l * partialDeriv (fun y => u y l) i x) +
          B i k l * partialDeriv f i x * u x l := by ring
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hzero : fourHeatOneZero C (fun y l => f y * u y l) x k =
      f x * fourHeatOneZero C u x k := by
    unfold fourHeatOneZero
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  unfold fourHeatOneOperator
  rw [fourHeatLocalOperator_cutoff a b f (fun y => u y k) x ha hf (hu k), hfirst, hzero]
  ring
end
end PositiveEinsteinFour.Geometry
end


section

/-! At the center the first radial connection jet is one half of the
actual curvature endomorphism, with the derivative order explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.frame_connection_curvature_center
    (D : HeatNormalFrameData g o c e) (i j : Fin 4) :
    matrixPartial (heatNormalFrameConnection g c D.point j) i 0 -
        matrixPartial (heatNormalFrameConnection g c D.point i) j 0 =
      (D.point 0).2⁻¹ *
        (∑ a, ∑ b, (jacobianMatrix (fun z => (D.point z).1) 0 a i *
          jacobianMatrix (fun z => (D.point z).1) 0 b j) •
            coordinateCurvatureMatrix g c a b (D.point 0).1) * (D.point 0).2 := by
  have hdet : IsUnit (D.point 0).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal 0 (Metric.mem_ball_self D.radius_pos))
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have h := congrArg (fun A : Mat4 => (D.point 0).2⁻¹ * A)
    (D.connection_curvature_intertwining i j)
  simpa only [D.frame_connection_zero, zero_mul, add_zero, sub_zero,
    Matrix.nonsing_inv_mul_cancel_left _ _ hdet, Matrix.mul_assoc] using h

theorem HeatNormalFrameData.base_jacobian_center
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩) :
    jacobianMatrix (fun z => (D.point z).1) 0 = f.matrix := by
  have heq : (fun z => (D.point z).1) =ᶠ[𝓝 (0 : FourSpace)]
      (fun z => chartAt FourSpace c (frameExponential g o ⟨c, f⟩ z)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with z hz
    exact D.exponential z hz
  have h := (frameExponential_chart_strictDerivative_zero g o c ⟨c, f⟩
    (mem_chart_source FourSpace c)).hasFDerivAt.fderiv
  rw [chartForwardOperator_center, ContinuousLinearMap.id_comp] at h
  ext r i
  change (fderiv ℝ (fun z => (D.point z).1) 0 (coordinateVector i)) r = _
  rw [heq.fderiv_eq, h]
  change (f.map (coordinateVector i)) r = f.matrix r i
  simp [OrthonormalFrame.map, coordinateVector]

theorem HeatNormalFrameData.frame_connection_curvature_intrinsic
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩)
    (i j : Fin 4) :
    matrixPartial (heatNormalFrameConnection g c D.point j) i 0 -
        matrixPartial (heatNormalFrameConnection g c D.point i) j 0 =
      curvatureEndomorphism (frameCurvature g c f) i j := by
  rw [D.frame_connection_curvature_center, D.base_jacobian_center, D.initial]
  have hf : frameChartMatrix g c (⟨c, f⟩ : FrameBundle g) = f.matrix := by
    ext a b
    rw [frameChartMatrix_apply g c ⟨c, f⟩ (mem_chart_source FourSpace c)]
    change (chartForwardOperator c c (f.vector b)) a = f.matrix a b
    rw [chartForwardOperator_center]
    rfl
  simpa only [frameCoordinateState, hf, pulledCurvatureEndomorphism] using
    frame_curvatureEndomorphism f i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact support and the vanishing near the center turn the exact
cutoff commutator into a uniform small-time error. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatScaledCommutator_continuous (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) (k : Fin 6) :
    Continuous (fun z : ℝ × FourSpace => fourHeatScaledCommutator a b B χ u z.1 z.2 k) := by
  have hL : Continuous (fun x => fourHeatLocalOperator (a x) (b x) 0 χ x) :=
    (fourHeatLocalOperator_contDiff 0 a b (fun _ => 0) χ
      (fun i j => contDiff_zero.mpr (ha i j)) (fun i => contDiff_zero.mpr (hb i))
      contDiff_const hχ).continuous
  have hP (q : Fin 6) : Continuous (fun z : ℝ × FourSpace =>
      fourHeatBundlePolynomial u z.1 z.2 q) :=
    fourHeatPolynomial_joint_continuous _ (fun m => (hu m q).continuous)
  have hD (q : Fin 6) (j : Fin 4) : Continuous (fun z : ℝ × FourSpace =>
      partialDeriv (fun y => fourHeatBundlePolynomial u z.1 y q) j z.2) :=
    fourHeatPolynomial_partial_joint_continuous _
      (fun m => (hu m q).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × FourSpace => partialDeriv χ i z.2) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp continuous_snd
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × FourSpace => a z.2 i j) :=
    (ha i j).comp continuous_snd
  have hBB (i : Fin 4) (q : Fin 6) : Continuous (fun z : ℝ × FourSpace => B z.2 i k q) :=
    (hB i k q).comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × FourSpace => z.2 j) :=
    (EuclideanSpace.proj j).continuous.comp continuous_snd
  exact ((continuous_fst.mul (hL.comp continuous_snd)).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hBB i q).mul (hχi i)).mul (hP q)))))

theorem fourHeatScaledCommutator_zero_of_locally_const (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (t : ℝ) (x : FourSpace) (c : ℝ) (hc : χ =ᶠ[𝓝 x] fun _ => c) (k : Fin 6) :
    fourHeatScaledCommutator a b B χ u t x k = 0 := by
  have hp (i : Fin 4) : partialDeriv χ i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hc.eventuallyEq_nhds] with y hy
    rw [fourHeat_partial_germ hy]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  have hpp (i j : Fin 4) : partialDeriv (partialDeriv χ i) j x = 0 := by
    rw [fourHeat_partial_germ (hp i)]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatScaledCommutator, fourHeatLocalOperator, hpp,
    fun i => (hp i).self_of_nhds, mul_zero, zero_mul, Finset.sum_const_zero,
    neg_zero, add_zero, sub_zero]

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

/-! Uniform O(t) control of the cutoff error on all normal coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatScaledCommutator_bounded (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k,
      |fourHeatScaledCommutator a b B χ u t x k| ≤ C := by
  let S := fun z : ℝ × FourSpace => ∑ k : Fin 6,
    |fourHeatScaledCommutator a b B χ u z.1 z.2 k|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    (fourHeatScaledCommutator_continuous a b B χ u ha hb hB hχ hu k).abs)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hχc).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ tsupport χ
  · have hle : |fourHeatScaledCommutator a b B χ u t x k| ≤ S (t, x) :=
      Finset.single_le_sum (fun q _ => abs_nonneg
        (fourHeatScaledCommutator a b B χ u t x q)) (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx⟩)).trans (le_max_left _ _))
  · have hz := fourHeatScaledCommutator_zero_of_locally_const a b B χ u t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem fourHeatScaledCommutator_gaussian_bound (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q))
    (r : ℝ) (hr : 0 < r) (hinner : ∀ x ∈ ball 0 r, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k,
      |(fourHeatGaussian t x / t) * fourHeatScaledCommutator a b B χ u t x k| ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := fourHeatScaledCommutator_bounded a b B χ u ha hb hB hχ hχc hu
  refine ⟨C * (384 / (Real.pi ^ 2 * r ^ 8)), by positivity, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ ball 0 r
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    rw [fourHeatScaledCommutator_zero_of_locally_const a b B χ u t x 1 he k,
      mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hrx : r ≤ ‖x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩ x k)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * r ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time r t hr ht.1 x hrx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform compact bounds for the actual transport family and the
coefficient left by the third transport equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem HeatFamilySmoothCoefficients.amplitude_compact_bound (E : HeatFamilySmoothCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ∀ k l : Fin 6, ‖iteratedFDeriv ℝ n (fun y => E.amplitude m y k l) z‖ ≤ C := by
  have hb (i : Fin 4 × Fin 6 × Fin 6) : ∃ C ≥ (0 : ℝ), ∀ n : ℕ, n ≤ 4 →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ n (fun y => E.amplitude i.1.val y i.2.1 i.2.2) z‖ ≤ C :=
    heatFamilyScalar_compact_jet_bound _ (E.amplitude_regular i.1.val (by omega) i.2.1 i.2.2) K hK
  choose C hC hb using hb
  refine ⟨∑ i : Fin 4 × Fin 6 × Fin 6, C i,
    Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro m hm n hn z hz k l
  let i : Fin 4 × Fin 6 × Fin 6 := (⟨m, by omega⟩, k, l)
  exact (hb i n hn z hz).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing lower-order signed traces for the actual normal-frame
connection and first heat amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatTwoFormConnectionMatrix_signed_trace (B : Mat4) :
    (twoFormHodgeMatrix * heatTwoFormConnectionMatrix B).trace = 0 :=
  heat_signed_skew_trace _ (heatTwoFormConnectionMatrix_skew B)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Four-component cutoff commutator for the actual one-form heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology
noncomputable section

def fourHeatOneScaledCommutator (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (χ : FourSpace → ℝ)
    (u : Fin 4 → FourSpace → Fin 4 → ℝ) (t : ℝ) (x : FourSpace) (k : Fin 4) : ℝ :=
  t * fourHeatLocalOperator (a x) (b x) 0 χ x * fourHeatOnePolynomial u t x k -
  2 * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
    (t * partialDeriv (fun y => fourHeatOnePolynomial u t y k) j x -
      x j / 2 * fourHeatOnePolynomial u t x k)) +
  t * (∑ i, ∑ q, B x i k q * partialDeriv χ i x * fourHeatOnePolynomial u t x q)

theorem fourHeatOneScaledCommutator_zero_of_locally_const (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (t : ℝ) (x : FourSpace) (c : ℝ) (hc : χ =ᶠ[𝓝 x] fun _ => c) (k : Fin 4) :
    fourHeatOneScaledCommutator a b B χ u t x k = 0 := by
  have hp (i : Fin 4) : partialDeriv χ i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hc.eventuallyEq_nhds] with y hy
    rw [fourHeat_partial_germ hy]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  have hpp (i j : Fin 4) : partialDeriv (partialDeriv χ i) j x = 0 := by
    rw [fourHeat_partial_germ (hp i)]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatOneScaledCommutator, fourHeatLocalOperator, hpp,
    fun i => (hp i).self_of_nhds, mul_zero, zero_mul, Finset.sum_const_zero,
    neg_zero, add_zero, sub_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The polynomial and its first spatial derivatives are jointly
continuous in time, normal vector and initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyPolynomial_partial_continuous (u : Fin 4 → HeatRadialFrameSpace → ℝ)
    (hu : ∀ m, ContDiff ℝ 1 (u m)) (i : Fin 4) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fourHeatPolynomial (fun m x => u m (x, z.2.2)) z.1) i z.2.1) := by
  have hs (q : CoordinateFrameSpace) (m : Fin 4) :
      ContDiff ℝ 1 (fun x : FourSpace => u m (x, q)) :=
    (hu m).comp (contDiff_id.prodMk contDiff_const)
  have he (z : ℝ × HeatRadialFrameSpace) :
      partialDeriv (fourHeatPolynomial (fun m x => u m (x, z.2.2)) z.1) i z.2.1 =
      fourHeatPolynomial (fun m x => heatFamilyScalarPartial (u m) i (x, z.2.2)) z.1 z.2.1 := by
    rw [fourHeatPolynomial_partial _ (hs z.2.2)]
    unfold fourHeatPolynomial
    simp only [← heatFamilyScalarPartial_slice _ (z.2.1, z.2.2)
      ((hu _).differentiable one_ne_zero _) i]
  simp_rw [he]
  exact heatFamilyPolynomial_continuous _ (fun m =>
    (heatFamilyScalarPartial_contDiff 0 _ (hu m) i).continuous)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation and radial integration commute with the fixed
Hodge-signed trace on the six-dimensional two-form fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise Interval

noncomputable section

theorem heatSixPartial_eq_fderiv (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x) (i : Fin 4) :
    heatSixPartial A i x = fderiv ℝ A x (coordinateVector i) := by
  have hd : DifferentiableAt ℝ A x :=
    differentiableAt_pi.mpr (fun k => differentiableAt_pi.mpr (hA k))
  ext k l
  let L₁ : HeatMat6 →L[ℝ] (Fin 6 → ℝ) := ContinuousLinearMap.proj k
  let L₂ : (Fin 6 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj l
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector i))
    ((L₂.comp L₁).hasFDerivAt.comp x hd.hasFDerivAt).fderiv

theorem heatSignedTrace_partial (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x) (i : Fin 4) :
    partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i x =
      (twoFormHodgeMatrix * heatSixPartial A i x).trace := by
  have hd : DifferentiableAt ℝ A x :=
    differentiableAt_pi.mpr (fun k => differentiableAt_pi.mpr (hA k))
  let L := heatSignedTraceLinear.toContinuousLinearMap
  rw [heatSixPartial_eq_fderiv A x hA i]
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector i))
    (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness bounds the cutoff commutator simultaneously for nearby
initial frames. The Gaussian restores the small-time factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyCommutator (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) (k l : Fin 6) : ℝ :=
  fourHeatScaledCommutator (fun x => E.a (x, z.2)) (fun x => E.b (x, z.2))
    (fun x => E.B (x, z.2)) χ (fun m x q => E.amplitude m (x, z.2) q l) t z.1 k

theorem heatFamilyCommutator_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (k l : Fin 6) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyCommutator E χ z.1 z.2 k l) := by
  have hP (q : Fin 6) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatBundlePolynomial (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 z.2.1 q) :=
    heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) q l).continuous)
  have hD (q : Fin 6) (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fun y => fourHeatBundlePolynomial
        (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 y q) j z.2.1) :=
    heatFamilyPolynomial_partial_continuous _
      (fun m => (E.amplitude_regular m (by omega) q l).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => partialDeriv χ i z.2.1) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp (continuous_fst.comp continuous_snd)
  have hχij (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (partialDeriv χ i) j z.2.1) :=
    ((fourHeat_partial_contDiff 0 _ (fourHeat_partial_contDiff 1 χ hχ i) j).continuous).comp
      (continuous_fst.comp continuous_snd)
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.a z.2 i j) :=
    (E.a_regular i j).continuous.comp continuous_snd
  have hb (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.b z.2 i) :=
    (E.b_regular i).continuous.comp continuous_snd
  have hB (i : Fin 4) (q : Fin 6) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.B z.2 i k q) :=
    (E.B_regular i k q).continuous.comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2.1 j) :=
    (EuclideanSpace.proj j).continuous.comp (continuous_fst.comp continuous_snd)
  have hL : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatLocalOperator (E.a z.2) (E.b z.2) 0 χ z.2.1) := by
    have hn : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
        -(∑ i : Fin 4, ∑ j : Fin 4, E.a z.2 i j *
          partialDeriv (partialDeriv χ i) j z.2.1) +
        ∑ i : Fin 4, E.b z.2 i * partialDeriv χ i z.2.1) :=
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hA i j).mul (hχij i j)))).neg.add
          (continuous_finsetSum _ (fun i _ => (hb i).mul (hχi i)))
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [fourHeatLocalOperator, zero_mul, add_zero]
  exact ((continuous_fst.mul hL).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hB i q).mul (hχi i)).mul (hP q)))))

theorem heatFamilyCommutator_bounded (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k l,
      |heatFamilyCommutator E χ t (x, q) k l| ≤ C := by
  let S := fun z : ℝ × HeatRadialFrameSpace => ∑ k : Fin 6, ∑ l : Fin 6,
    |heatFamilyCommutator E χ z.1 z.2 k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (heatFamilyCommutator_continuous E χ hχ k l).abs))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ tsupport χ
  · have hle : |heatFamilyCommutator E χ t (x, q) k l| ≤ S (t, (x, q)) := by
      apply (Finset.single_le_sum (fun a _ => abs_nonneg
        (heatFamilyCommutator E χ t (x, q) k a)) (Finset.mem_univ l)).trans
      exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (heatFamilyCommutator E χ t (x, q) a b)))
        (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx, hq⟩)).trans (le_max_left _ _))
  · have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    change |fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem heatFamilyCommutator_gaussian_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
      |(fourHeatGaussian t x / t) * heatFamilyCommutator E χ t (x, q) k l| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := heatFamilyCommutator_bounded E χ hχ hc K hK
  refine ⟨C * (384 / (Real.pi ^ 2 * s ^ 8)), by positivity, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ ball 0 s
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 1 he k
    change |(fourHeatGaussian t x / t) * fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hsx : s ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hb q hq t ⟨ht.1.le, ht.2⟩ x k l)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * s ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time s t hs ht.1 x hsx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness bounds the one-form cutoff commutator over the common frame family. The Gaussian restores the small-time factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyOneCommutator (E : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) (k l : Fin 4) : ℝ :=
  fourHeatOneScaledCommutator (fun x => E.base.a (x, z.2)) (fun x => E.base.b (x, z.2))
    (fun x => E.B (x, z.2)) χ (fun m x q => E.amplitude m (x, z.2) q l) t z.1 k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed squared-Gaussian integral is bounded uniformly in time
once its first coefficient vanishes quadratically. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter

noncomputable section

theorem fourHeat_signed_gaussian_bound (f F : FourSpace → ℝ) (C B t : ℝ)
    (hC : 0 ≤ C) (_hB : 0 ≤ B) (ht : 0 < t)
    (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ 2) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖∫ x : FourSpace, fourHeatGaussian t x ^ 2 * (2 * t * f x + t ^ 2 * F x)‖ ≤
      (32 * C + B) / (64 * Real.pi ^ 2) := by
  let s := t / 2
  have hs : 0 < s := half_pos ht
  let A := 1 / (64 * Real.pi ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hid : (fun x : FourSpace => fourHeatGaussian t x ^ 2 * (2 * t * f x + t ^ 2 * F x)) =
      fun x => A * (fourHeatGaussian s x * ((2 / t) * f x + F x)) := by
    funext x
    have hh := fourHeatGaussian_square_half t ht x
    change t ^ 2 * fourHeatGaussian t x ^ 2 = A * fourHeatGaussian s x at hh
    calc
      _ = (t ^ 2 * fourHeatGaussian t x ^ 2) * ((2 / t) * f x + F x) := by
        field_simp [ht.ne']
      _ = _ := by rw [hh]; ring
  let Z := fun x : FourSpace => (2 * C / t) * (‖x‖ ^ 2 * fourHeatGaussian s x) +
    B * fourHeatGaussian s x
  have hZ : Integrable Z :=
    ((fourHeatGaussian_moment_integrable 1 s hs).const_mul (2 * C / t)).add
      ((fourHeatGaussian_integrable s hs).const_mul B)
  have hz (x : FourSpace) : ‖fourHeatGaussian s x * ((2 / t) * f x + F x)‖ ≤ Z x := by
    rw [norm_mul, Real.norm_of_nonneg (fourHeatGaussian_pos s hs x).le]
    calc
      _ ≤ fourHeatGaussian s x * (‖(2 / t) * f x‖ + ‖F x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (fourHeatGaussian_pos s hs x).le
      _ = fourHeatGaussian s x * ((2 / t) * ‖f x‖ + ‖F x‖) := by
        rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / t)]
      _ ≤ fourHeatGaussian s x * ((2 / t) * (C * ‖x‖ ^ 2) + B) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hf x) (by positivity)) (hF x))
          (fourHeatGaussian_pos s hs x).le
      _ = Z x := by dsimp [Z]; ring
  rw [hid, integral_const_mul, norm_mul, Real.norm_of_nonneg hA]
  calc
    _ ≤ A * ∫ x, Z x := mul_le_mul_of_nonneg_left
      (norm_integral_le_of_norm_le hZ (Eventually.of_forall hz)) hA
    _ = A * ((2 * C / t) * (∫ x : FourSpace, ‖x‖ ^ 2 * fourHeatGaussian s x) + B) := by
      rw [integral_add ((fourHeatGaussian_moment_integrable 1 s hs).const_mul _)
        ((fourHeatGaussian_integrable s hs).const_mul _), integral_const_mul,
        integral_const_mul, fourHeatGaussian_mass s hs]
      simp only [mul_one]
    _ ≤ A * ((2 * C / t) * (32 * s) + B) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hm := fourHeatGaussian_integral_moment_bound 1 s hs
      norm_num at hm
      nlinarith
    _ = _ := by dsimp [A, s]; field_simp [ht.ne']

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Degree-two de Rham cohomology of the actual smooth exterior complex,
and its harmonic representative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev smoothClosedTwoForms : Submodule ℝ (smoothTwoForms o) :=
  (smoothTwoFormExterior (o := o)).ker

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_1_rd0f954_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
def smoothExactTwoForms : Submodule ℝ (smoothClosedTwoForms (o := o)) :=
  (LinearMap.range (smoothOneFormExteriorLinear (o := o))).comap
    (smoothClosedTwoForms (o := o)).subtype

abbrev TwoFormDeRhamCohomology :=
  (smoothClosedTwoForms (o := o)) ⧸ (smoothExactTwoForms (o := o))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integral intersection pairing, its exact-form annihilator, and
its signs on the actual harmonic Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_3_rd0f954_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
def twoFormIntersection (u v : smoothTwoForms o) : ℝ :=
  smoothTwoFormL2Inner u (smoothTwoFormHodge o v)

theorem twoFormIntersection_comm (u v : smoothTwoForms o) :
    twoFormIntersection u v = twoFormIntersection v u := by
  unfold twoFormIntersection
  rw [← smoothTwoFormL2Inner_hodge_left, smoothTwoFormL2Inner_comm]

theorem twoFormIntersection_add_left (u v w : smoothTwoForms o) :
    twoFormIntersection (u + v) w = twoFormIntersection u w + twoFormIntersection v w :=
  smoothTwoFormL2Inner_add u v _

omit [CompactSpace M] [Nonempty M] in
theorem twoFormIntersection_smul_left (r : ℝ) (u v : smoothTwoForms o) :
    twoFormIntersection (r • u) v = r * twoFormIntersection u v :=
  smoothTwoFormL2Inner_smul r u _

theorem twoFormIntersection_add_right (u v w : smoothTwoForms o) :
    twoFormIntersection u (v + w) = twoFormIntersection u v + twoFormIntersection u w := by
  rw [twoFormIntersection_comm, twoFormIntersection_add_left,
    twoFormIntersection_comm v u, twoFormIntersection_comm w u]

theorem twoFormIntersection_smul_right (r : ℝ) (u v : smoothTwoForms o) :
    twoFormIntersection u (r • v) = r * twoFormIntersection u v := by
  rw [twoFormIntersection_comm, twoFormIntersection_smul_left, twoFormIntersection_comm v u]

def smoothHarmonicIntersection :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] smoothHarmonicTwoForms (o := o) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => twoFormIntersection u.val v.val
      map_add' := fun v w => twoFormIntersection_add_right u.val v.val w.val
      map_smul' := fun r v => twoFormIntersection_smul_right r u.val v.val }
  map_add' u v := by ext w; exact twoFormIntersection_add_left u.val v.val w.val
  map_smul' r u := by ext v; exact twoFormIntersection_smul_left r u.val v.val

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

/-! The inertia of the actual harmonic intersection form. The positive
and negative indices are the dimensions of the Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance harmonicSignatureAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def harmonicIntersectionQuadratic : QuadraticForm ℝ (smoothHarmonicTwoForms (o := o)) :=
  LinearMap.BilinMap.toQuadraticMap (smoothHarmonicIntersection (o := o))

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

local instance deRhamSignatureHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

local instance deRhamSignatureClosedAddGroup : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

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

local instance harmonicTraceAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

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

theorem HeatNormalFrameData.value_zero (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (u : M → TwoFormFour) :
    heatNormalTwoFormValue o c D.point u 0 = twoFormFrameValue o u e := by
  apply twoFormTensor_injective
  rw [heatNormalTwoFormValue_tensor, ← twoFormFramedValue_eq, D.initial]
  exact (heat_framedValue_chart o u c e he).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed zeroth-order coefficient is purely quadratic in the
connection: the potential and the linear connection terms have zero trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatConnectionZero_signed_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6) (x : FourSpace)
    (hV : (twoFormHodgeMatrix * V).trace = 0)
    (hA : ∀ i, (twoFormHodgeMatrix * A i x).trace = 0)
    (hD : ∀ i j, (twoFormHodgeMatrix * heatSixPartial (A i) j x).trace = 0) :
    (twoFormHodgeMatrix * fourHeatConnectionZero a b A V x).trace =
      -(∑ i, ∑ j, a i j * (twoFormHodgeMatrix * A j x * A i x).trace) := by
  let L := heatSignedTraceLinear
  have hV' : L V = 0 := hV
  have hA' (i : Fin 4) : L (A i x) = 0 := hA i
  have hD' (i j : Fin 4) : L (heatSixPartial (A i) j x) = 0 := hD i j
  change L (V + (∑ i, b i • A i x) -
    ∑ i, ∑ j, a i j • (heatSixPartial (A i) j x + A j x * A i x)) = _
  simp only [map_sub, map_add, map_sum, map_smul, hV', hA', hD',
    smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, zero_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg Matrix.trace (Matrix.mul_assoc twoFormHodgeMatrix (A j x) (A i x)).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.connection_partial_signed_trace
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (i j : Fin 4)
    (hA : ∀ k l, DifferentiableAt ℝ
      (fun y => heatTwoFormConnection g c D.point i y k l) x) :
    (twoFormHodgeMatrix * heatSixPartial (heatTwoFormConnection g c D.point i) j x).trace = 0 := by
  have heq : (fun y => (twoFormHodgeMatrix * heatTwoFormConnection g c D.point i y).trace) =
      fun _ => 0 := funext (fun y => heatTwoFormConnectionMatrix_signed_trace _)
  have h := heatSignedTrace_partial (heatTwoFormConnection g c D.point i) x hA j
  rw [heq] at h
  simpa only [partialDeriv, fderiv_const_apply, _root_.zero_apply] using h.symm

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

theorem fourHeat_leading_signed_source (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (U : FourSpace → ℝ) (x : FourSpace)
    (hB : ∀ i, (twoFormHodgeMatrix * B i).trace = 0) :
    (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
      -fourHeatBundleOperator a b B C
        (fun y q => U y * (if q = l then 1 else 0)) x k)).trace =
      -U x * (twoFormHodgeMatrix * C).trace := by
  have hm : (show HeatMat6 from fun k l =>
      -fourHeatBundleOperator a b B C
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
  simp only [Matrix.mul_neg, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sum,
    Matrix.trace_smul, twoFormHodgeMatrix_trace, hB, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, zero_add]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.B_signed_near (E : HeatNormalBundleExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i, (twoFormHodgeMatrix * E.B x i).trace = 0 := by
  filter_upwards [E.B_near] with x hx
  intro i
  rw [hx]
  simp only [heatNormalBundleFirst, fourHeatConnectionFirst, Matrix.mul_smul,
    Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum,
    heatTwoFormConnectionMatrix_signed_trace, heatTwoFormConnection, smul_eq_mul,
    mul_zero, Finset.sum_const_zero]

theorem HeatNormalBundleExtension.first_amplitude_signed_radial
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    (twoFormHodgeMatrix * E.amplitude 1 x).trace =
      fourHeatWeightedRadialAverage 0 E.base.U
        (fun y => (twoFormHodgeMatrix * E.firstSource y).trace) x := by
  change (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
    fourHeatWeightedRadialAverage 0 E.base.U (fun y => E.firstSource y k l) x)).trace = _
  apply heatSignedTrace_weightedRadial
  · exact E.base.U_regular.continuous
  · exact continuous_pi (fun k => continuous_pi (fun l => (E.firstSource_regular k l).continuous))
  · exact fun y => (E.base.U_pos y).ne'

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

theorem heatFamilyPolynomialColumn_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 6) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyPolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp (continuous_fst.comp continuous_snd)).mul
    (heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) k l).continuous))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal-frame signed polynomial and its first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.signed_amplitude_regular (E : HeatNormalBundleExtension D)
    (m : ℕ) (hm : m ≤ 3) :
    ContDiff ℝ 2 (fun x => (twoFormHodgeMatrix * E.amplitude m x).trace) :=
  heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
      (E.amplitude_regular m hm i j).of_le (by norm_num))))

theorem HeatNormalBundleExtension.signedFirst_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) : Continuous (E.signedFirst χ) :=
  (((frameExponentialJacobian_continuous g o e).mul (hχ.pow 2)).mul
    E.base.U_regular.continuous).mul (E.signed_amplitude_regular 1 (by norm_num)).continuous

theorem HeatNormalBundleExtension.signedFirst_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiffAt ℝ 2 χ 0) : ContDiffAt ℝ 2 (E.signedFirst χ) 0 :=
  ((((frameExponentialJacobian_smoothAt_zero g o e).of_le (by norm_num)).mul
    (hχ.pow 2)).mul (E.base.U_regular.of_le (by norm_num)).contDiffAt).mul
      (E.signed_amplitude_regular 1 (by norm_num)).contDiffAt

theorem HeatNormalBundleExtension.signedFirst_compact (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : HasCompactSupport χ) : HasCompactSupport (E.signedFirst χ) := by
  apply hχ.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [HeatNormalBundleExtension.signedFirst, hz])

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity and a compact uniform bound for the higher signed terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.signedTail_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × FourSpace => E.signedTail χ z.1 z.2) := by
  have hJ := (frameExponentialJacobian_continuous g o e).comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hU := E.base.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) := (E.signed_amplitude_regular m hm).continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :=
    (heatSignedGram_contDiff (E.amplitude m) (E.amplitude n)
      (fun i j => (E.amplitude_regular m hm i j).of_le (by norm_num))
      (fun i j => (E.amplitude_regular n hn i j).of_le (by norm_num))).continuous.comp
      (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have h2 := hS 2 (by norm_num)
  have h3 := hS 3 (by norm_num)
  have h11 := hG 1 1 (by norm_num) (by norm_num)
  have h12 := hG 1 2 (by norm_num) (by norm_num)
  have h13 := hG 1 3 (by norm_num) (by norm_num)
  have h22 := hG 2 2 (by norm_num) (by norm_num)
  have h23 := hG 2 3 (by norm_num) (by norm_num)
  have h33 := hG 3 3 (by norm_num) (by norm_num)
  have htwo : Continuous (fun _ : ℝ × FourSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul h2).add h11
  have h1 := ((htwo.mul hU).mul h3).add (htwo.mul h12)
  have ht2 := (htwo.mul h13).add h22
  unfold HeatNormalBundleExtension.signedTail
  exact (hJ.mul ((hχ.comp continuous_snd).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul ht2)).add
      ((continuous_fst.pow 3).mul (htwo.mul h23))).add
        ((continuous_fst.pow 4).mul h33))

theorem HeatNormalBundleExtension.signedTail_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖E.signedTail χ t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn
    (E.signedTail_continuous χ hχ).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · exact (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.signedTail, hz, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

theorem HeatNormalBundleExtension.signedTail_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : χ 0 = 1) :
    E.signedTail χ 0 0 = 2 * (twoFormHodgeMatrix * E.amplitude 2 0).trace +
      heatSignedGram (E.amplitude 1 0) (E.amplitude 1 0) := by
  have hU : E.base.U 0 = 1 := E.base.U_near.self_of_nhds.trans
    (heatNormalLeadingAmplitude_zero g o e)
  simp [HeatNormalBundleExtension.signedTail, frameExponentialJacobian_zero, hχ, hU]

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarGlobal_probability
omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.chart_zero (P : HeatScalarChartData D) :
    P.chart 0 = e.base := by
  have hz : (0 : FourSpace) ∈ P.chart.source := P.cutoff_support
    (subset_tsupport P.cutoff (by rw [Function.mem_support, P.cutoff_zero]; exact one_ne_zero))
  exact (P.exponential hz).trans (frameExponential_zero g o e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairing of two finite-regularity amplitudes
inside the actual two-form Hilbert space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.heatNormalInnerCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.heatNormalInnerProbability
omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem heatNormalAmplitudeTensor_inner
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source)
    (f : FrameBundle g) (hf : f.base ∈ C.target) :
    inner ℝ (heatNormalAmplitudeTensor D C hCt hP hD a ha hca hsa f)
      (heatNormalAmplitudeTensor D C hCt hP hD b hb hcb hsb f) =
      2 * inner ℝ (a (C.symm f.base)) (b (C.symm f.base)) := by
  let x := C.symm f.base
  have hx : x ∈ C.source := C.map_target hf
  have hxb := hD hx
  have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
    rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
  have hF := frameChartMatrix_normalizes g c f (hCt hf)
  rw [← hbase] at hF
  have hi : (D.point x).2⁻¹ * (D.point x).2 = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (heatNormalFrame_matrix_nondegenerate D hxb))
  have hback : frameTensor (D.point x).2 (heatNormalCoordinateTensor D b x) = twoFormTensor (b x) := by
    unfold heatNormalCoordinateTensor
    rw [← frameTensor_mul, hi, frameTensor_one]
  change inner ℝ (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f)
    : TwoTensorEuclidean) (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D b) f)) = _
  rw [heat_euclideanTensor_inner]
  simp only [heatNormalFrameTensorLift, ite_eq_left hf]
  change frameTensorPairing
    (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))))
    (frameTensor (frameChartMatrix g c f) (heatNormalCoordinateTensor D b x)) = _
  rw [heat_normal_frame_pairing _ _ _ (D.orthonormal x hxb) hF, hback, twoFormTensor_pairing]

theorem heatNormalAmplitudeL2_inner_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hca hsa)
      (heatNormalAmplitudeL2 D C hCt hP hD b hb hcb hsb) =
      (normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x * inner ℝ (a x) (b x) := by
  let A := heatNormalAmplitudeTensor D C hCt hP hD a ha hca hsa
  let B := heatNormalAmplitudeTensor D C hCt hP hD b hb hcb hsb
  let ψ := fun x => inner ℝ (a x) (b x)
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change inner ℝ (a x) (b x) = 0
    rw [hz, inner_zero_left]
  have hψc : HasCompactSupport ψ := hca.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.inner hb.continuous).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hsa)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : inner ℝ (A f) (B f) = 2 * heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalAmplitudeTensor_inner C hE hCt hP hD a b ha hb hca hcb hsa hsb f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : A f = 0 := by
        change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
        simp only [heatNormalFrameTensorLift, ite_eq_right hf]
        rfl
      rw [hz, inner_zero_left]
      simp only [heatNormalScalarLift, ite_eq_right hf, mul_zero]
  have hcalc : 2 * inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hca hsa)
      (heatNormalAmplitudeL2 D C hCt hP hD b hb hcb hsb) =
      2 * ((normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x * ψ x) := by
    rw [← twoFormTensorL2_inner,
      heatNormalAmplitudeTensor_L2_realization C hCt hP hD a ha hca hsa,
      heatNormalAmplitudeTensor_L2_realization C hCt hP hD b hb hcb hsb, L2.inner_def]
    change (∫ f, inner ℝ ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ A) f)
      ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ B) f) ∂canonicalFrameMeasure g o) = _
    have he : (∫ f, inner ℝ ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ A) f)
        ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ B) f) ∂canonicalFrameMeasure g o) =
        ∫ f, inner ℝ (A f) (B f) ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) A,
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) B] with f hA hB
      rw [hA, hB]
    rw [he]
    simp_rw [heq]
    rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi,
      heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hsa)]
  linarith

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

local instance scalarGaussian_probability_rd0f954_1 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.polynomial_weight_bound (P : HeatScalarChartData D) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2 ≤ B := by
  let W := fun z : ℝ × FourSpace => frameExponentialJacobian g o e z.2 *
    (P.polynomial z.1 z.2) ^ 2
  have hP : Continuous (fun z : ℝ × FourSpace => P.polynomial z.1 z.2) :=
    (P.cutoff_regular.continuous.comp continuous_snd).mul
      (fourHeatPolynomial_joint_continuous _
        (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous))
  have hW : Continuous W :=
    ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul (hP.pow 2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod P.cutoff_compact).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport P.cutoff
  · exact (hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hz : P.polynomial t x = 0 := by
      unfold polynomial
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.square_integral_bound (P : HeatScalarChartData D) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x *
        (P.extension.scalarCutoff P.cutoff t x) ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := P.polynomial_weight_bound
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro t ht
  have hp (x : FourSpace) : frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [P.cutoff_gaussian, mul_pow]
    calc
      _ = (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hc : Continuous (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t).continuous.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    hi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hp x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hp
    _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; ring

theorem HeatScalarChartData.column_growth (P : HeatScalarChartData D) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.column t‖ ≤ C / t := by
  obtain ⟨B, hB, hbound⟩ := P.square_integral_bound
  let K := (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro t ht
  have hn : ‖P.column t‖ ^ 2 ≤ K / t ^ 2 := by
    rw [P.column_norm_sq_integral]
    exact (mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)).trans_eq (by dsimp [K]; ring)
  have hs : (‖P.column t‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.column t‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.column t)]

theorem HeatScalarChartData.normalizedColumn_growth (P : HeatScalarChartData D) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.normalizedColumn t‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := P.column_growth
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative of the global scalar parametrix is a
compact C4 function, represented in the same scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatScalarChartData.timeAmplitude (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) : ℝ :=
  P.cutoff x * fourHeatGaussianPolynomialTime (fun m => P.extension.scalarAmplitude m) t x

theorem HeatScalarChartData.timeAmplitude_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContDiff ℝ 4 (P.timeAmplitude t) := by
  have hu (m : Fin 4) := P.extension.scalarAmplitude_regular m (by omega)
  have hQ : ContDiff ℝ 4 (fun x => fourHeatPolynomialTime
      (fun m => P.extension.scalarAmplitude m) t x) :=
    ((hu 1).add ((contDiff_const (c := 2 * t)).mul (hu 2))).add
      ((contDiff_const (c := 3 * t ^ 2)).mul (hu 3))
  have hF : ContDiff ℝ 4 (fourHeatGaussianTimeFactor t) :=
    ((contDiff_norm_sq ℝ).div_const (4 * t ^ 2)).sub contDiff_const
  have hG : ContDiff ℝ 4 (fourHeatGaussian t) := (fourHeatGaussian_smooth t).of_le (by norm_num)
  have hP : ContDiff ℝ 4 (fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t) :=
    (((hu 0).add (contDiff_const.mul (hu 1))).add
      (contDiff_const.mul (hu 2))).add (contDiff_const.mul (hu 3))
  exact P.cutoff_regular.mul (((hF.mul hG).mul hP).add (hG.mul hQ))

theorem HeatScalarChartData.timeAmplitude_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.timeAmplitude t) ⊆ tsupport P.cutoff := tsupport_mul_subset_left

theorem HeatScalarChartData.timeAmplitude_eq (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    P.timeAmplitude t x = deriv (fun s => P.extension.scalarCutoff P.cutoff s x) t :=
  ((fourHeatGaussianPolynomial_hasDerivAt (fun m => P.extension.scalarAmplitude m)
    t ht x).const_mul (P.cutoff x)).deriv.symm

def HeatScalarChartData.timeFunction (P : HeatScalarChartData D) (t : ℝ) : M → ℝ :=
  heatNormalScalarLift P.chart (P.timeAmplitude t)

theorem HeatScalarChartData.timeFunction_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (P.timeFunction t) :=
  heatNormalScalarLift_regular P.chart _ P.inverse_regular (P.timeAmplitude_regular t)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (P.timeAmplitude_support t))
    ((P.timeAmplitude_support t).trans P.cutoff_support)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarTime_probability
def HeatScalarChartData.timeColumn (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  scalarFiniteValueL2 g (P.timeFunction t) (P.timeFunction_regular t)

theorem HeatScalarChartData.timeColumn_pairing (P : HeatScalarChartData D)
    (t : ℝ) (f : C(M, ℝ)) :
    inner ℝ (P.timeColumn t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f) =
      (normalizedChartFactor g).toReal * ∫ x, P.timeAmplitude t x *
        (frameExponentialJacobian g o e x * f (P.chart x)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, P.timeFunction t y * f y ∂normalizedVolume g := by
      apply integral_congr_ae
      filter_upwards [scalarFiniteValueL2_coe g (P.timeFunction t) (P.timeFunction_regular t),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) f] with y hy hf
      simp only [RCLike.inner_apply', conj_trivial, HeatScalarChartData.timeColumn, hy, hf]
    _ = ∫ y, heatNormalScalarLift P.chart (fun x => P.timeAmplitude t x * f (P.chart x)) y
        ∂normalizedVolume g := by
      apply integral_congr_ae
      exact Eventually.of_forall (heatNormalScalarLift_mul P.chart _ f)
    _ = _ := by
      rw [heatNormalScalarLift_integral D P.chart P.exponential P.in_chart
        (P.point_regular.of_le (by norm_num)) P.inside_radius]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      · exact tsupport_mul_subset_left.trans ((P.timeAmplitude_support t).trans P.cutoff_support)

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

/-! Exact support control for the scalar cutoff and its Laplacian. This
allows the geometric operator identity to be used only on the cutoff support. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatScalarLift_tsupport {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : OpenPartialHomeomorph FourSpace X) (ψ : FourSpace → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    tsupport (heatNormalScalarLift C ψ) ⊆ C '' tsupport ψ := by
  have hK := hc.image_of_continuousOn (C.continuousOn.mono hs)
  exact closure_minimal (heatNormalScalarLift_support C ψ) hK.isClosed

theorem heatScalarOperator_tsupport (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (u : FourSpace → ℝ) :
    tsupport (fun x => fourHeatLocalOperator (a x) (b x) 0 u x) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro x hx
  by_contra hn
  have hz : u =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  change fourHeatLocalOperator (a x) (b x) 0 u x = 0
  rw [fourHeatLocalOperator_germ _ _ _ hz]
  have hp (i : Fin 4) : partialDeriv (fun _ : FourSpace => (0 : ℝ)) i = fun _ => 0 := by
    funext y
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatLocalOperator, hp, mul_zero, Finset.sum_const_zero, neg_zero, add_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.function_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.function t) ⊆ P.chart '' tsupport P.cutoff := by
  have hs := P.extension.scalarCutoff_support P.cutoff t
  exact (heatScalarLift_tsupport P.chart _
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans P.cutoff_support)).trans (image_mono hs)

theorem HeatScalarChartData.timeFunction_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.timeFunction t) ⊆ P.chart '' tsupport P.cutoff := by
  have hs := P.timeAmplitude_support t
  exact (heatScalarLift_tsupport P.chart _
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans P.cutoff_support)).trans (image_mono hs)

def HeatScalarChartData.residualAmplitude (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) : ℝ :=
  P.timeAmplitude t x + fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
    (P.extension.scalarCutoff P.cutoff t) x

theorem HeatScalarChartData.residualAmplitude_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContDiff ℝ 2 (P.residualAmplitude t) :=
  ((P.timeAmplitude_regular t).of_le (by norm_num)).add
    (fourHeatLocalOperator_contDiff 2 P.extension.a P.extension.b (fun _ => 0) _
      (fun i j => (P.extension.a_regular i j).of_le (by norm_num))
      (fun i => (P.extension.b_regular i).of_le (by norm_num)) contDiff_const
      (P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t))

theorem HeatScalarChartData.residualAmplitude_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.residualAmplitude t) ⊆ tsupport P.cutoff := by
  exact (tsupport_add _ _).trans (union_subset (P.timeAmplitude_support t)
    ((heatScalarOperator_tsupport _ _ _).trans (P.extension.scalarCutoff_support P.cutoff t)))

def HeatScalarChartData.residualFunction (P : HeatScalarChartData D) (t : ℝ) : M → ℝ :=
  heatNormalScalarLift P.chart (P.residualAmplitude t)

theorem HeatScalarChartData.residualFunction_continuous (P : HeatScalarChartData D) (t : ℝ) :
    Continuous (P.residualFunction t) :=
  heatNormalScalarLift_continuous P.chart _ (P.residualAmplitude_regular t).continuous.continuousOn
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (P.residualAmplitude_support t))
    ((P.residualAmplitude_support t).trans P.cutoff_support)

theorem HeatScalarChartData.residualFunction_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.residualFunction t) ⊆ P.chart '' tsupport P.cutoff := by
  have hs := P.residualAmplitude_support t
  exact (heatScalarLift_tsupport P.chart _
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans P.cutoff_support)).trans (image_mono hs)

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

theorem heatFamilyEulerFirst_regular (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) : ContDiff ℝ 2 (heatFamilyEulerFirst F χ) := by
  have hs : ContDiff ℝ 2 (fun z => heatEulerTrace (F.eulerAmplitude 1 z)) := by
    unfold heatEulerTrace HeatFamilyOneCoefficients.eulerAmplitude Matrix.trace Matrix.diag
    exact ((contDiff_const.mul ((F.base.scalarAmplitude_regular 1 (by omega)).of_le (by norm_num))).sub
      (contDiff_const.mul (ContDiff.sum (fun k _ =>
        (F.amplitude_regular 1 (by omega) k k).of_le (by norm_num))))).add
      (ContDiff.sum (fun k _ => (F.base.amplitude_regular 1 (by omega) k k).of_le (by norm_num)))
  exact (((hχ.comp contDiff_fst).pow 2).div (F.base.U_regular.of_le (by norm_num))
    (fun z => (F.base.U_pos z).ne')).mul hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time continuity of the actual scalar cutoff and its residual
in the global scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.cutoff_joint_regular (P : HeatScalarChartData D)
    (z : ℝ × FourSpace) (hz : 0 < z.1) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace =>
      P.extension.scalarCutoff P.cutoff w.1 w.2) z := by
  exact ((P.cutoff_regular.of_le (by norm_num)).comp contDiff_snd).contDiffAt.mul
    ((fourHeatGaussian_joint_contDiffAt z hz).mul
      (fourHeatPolynomial_joint_contDiff _ (fun m =>
        (P.extension.scalarAmplitude_regular m (by omega)).of_le (by norm_num))).contDiffAt)

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

theorem heatFamilyOnePolynomialColumn_continuous (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 4) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyOnePolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp (continuous_fst.comp continuous_snd)).mul
    (heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatFamilyOnePolynomial_weight_bound (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      (E.base.U (x, q) ^ 2)⁻¹ * ‖heatFamilyOnePolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
  have hb (l : Fin 4) : ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      (E.base.U (x, q) ^ 2)⁻¹ * ‖heatFamilyOnePolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
    let W := fun z : ℝ × HeatRadialFrameSpace => (E.base.U z.2 ^ 2)⁻¹ *
      ‖heatFamilyOnePolynomialColumn E χ z.1 l z.2‖ ^ 2
    have hW : Continuous W :=
      (((E.base.U_regular.continuous.comp continuous_snd).pow 2).inv₀
        (fun z => pow_ne_zero 2 (E.base.U_pos z.2).ne')).mul
        ((heatFamilyOnePolynomialColumn_continuous E χ hχ l).norm.pow 2)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hW.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro q hq t ht x
    by_cases hx : x ∈ tsupport χ
    · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
    · have hz : heatFamilyOnePolynomialColumn E χ t l (x, q) = 0 := by
        apply WithLp.ofLp_injective 2
        funext k
        change χ x * _ = 0
        rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      exact le_max_right _ _
  choose B hB hb using hb
  refine ⟨∑ l, B l, Finset.sum_nonneg (fun l _ => hB l), ?_⟩
  intro q hq t ht x l
  exact (hb l q hq t ht x).trans (Finset.single_le_sum (fun a _ => hB a) (Finset.mem_univ l))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform bounds for the remaining coefficients of the common Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def heatFamilyEulerTail (F : HeatFamilyOneCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  (F.base.U z ^ 2)⁻¹ * χ z.1 ^ 2 *
    (2 * F.base.U z * heatEulerTrace (F.eulerAmplitude 2 z) +
      heatEulerGram (F.eulerAmplitude 1 z) (F.eulerAmplitude 1 z) +
      t * (2 * F.base.U z * heatEulerTrace (F.eulerAmplitude 3 z) +
        2 * heatEulerGram (F.eulerAmplitude 1 z) (F.eulerAmplitude 2 z)) +
      t ^ 2 * (2 * heatEulerGram (F.eulerAmplitude 1 z) (F.eulerAmplitude 3 z) +
        heatEulerGram (F.eulerAmplitude 2 z) (F.eulerAmplitude 2 z)) +
      t ^ 3 * (2 * heatEulerGram (F.eulerAmplitude 2 z) (F.eulerAmplitude 3 z)) +
      t ^ 4 * heatEulerGram (F.eulerAmplitude 3 z) (F.eulerAmplitude 3 z))

theorem HeatFamilyOneCoefficients.eulerAmplitude_continuous (F : HeatFamilyOneCoefficients)
    (m : ℕ) (hm : m ≤ 3) : Continuous (F.eulerAmplitude m) :=
  (F.base.scalarAmplitude_regular m hm).continuous.prodMk
    ((continuous_pi (fun k => continuous_pi (fun l =>
      (F.amplitude_regular m hm k l).continuous))).prodMk
      (continuous_pi (fun k => continuous_pi (fun l =>
        (F.base.amplitude_regular m hm k l).continuous))))

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

theorem HeatNormalParametrixData.column_inner_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    inner ℝ (P.column E t l) (P.column E t m) = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalCutoffColumn E P.cutoff t l x) (heatNormalCutoffColumn E P.cutoff t m x) :=
  heatNormalAmplitudeL2_inner_integral P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalCutoffColumn E P.cutoff t l) (heatNormalCutoffColumn E P.cutoff t m)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t m)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E P.cutoff t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E P.cutoff t m))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
    ((heatNormalCutoffColumn_support E P.cutoff t m).trans P.cutoff_support)

theorem HeatNormalParametrixData.normalizedColumn_inner_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalCutoffColumn E P.cutoff t l x) (heatNormalCutoffColumn E P.cutoff t m x) := by
  change inner ℝ (((normalizedChartFactor g).toReal)⁻¹ • P.column E t l)
    (((normalizedChartFactor g).toReal)⁻¹ • P.column E t m) = _
  rw [real_inner_smul_left, real_inner_smul_right, P.column_inner_integral E t l m]
  have hn := (normalizedChartFactor_toReal_pos g).ne'
  field_simp

theorem HeatNormalParametrixData.normalizedColumn_gaussian_inner
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) (l m : Fin 6) :
    inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 * (frameExponentialJacobian g o e x *
        inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x) (heatNormalPolynomialColumn E P.cutoff t m x)) := by
  rw [P.normalizedColumn_inner_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [heatNormalCutoffColumn_gaussian, heatNormalCutoffColumn_gaussian,
      real_inner_smul_left, real_inner_smul_right]
    ring

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

/-! A unit Weyl norm forces parallel Weyl curvature and maximal normalized
determinant. The proof differentiates its actual constant norm twice. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}
  {μ : Measure (FrameBundle g)}

theorem MetricGreenData.unit_norm_second_pairing (d : MetricGreenData g μ)
    (hflow : OrientationPreservingFlow d o) (hnorm : ∀ x, plusNorm o x = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (i : Fin 4) :
    matrixPairing (plusWeylGradient g e.base e.frame i) (plusWeylGradient g e.base e.frame i) +
      matrixPairing (plusWeyl g e.base e.frame) (plusWeylHessian g e.base e.frame i i) = 0 := by
  obtain ⟨f₀,hf₀⟩ := ((d.flow i).map 0).surjective e
  have hp : f₀ ∈ o.positive := (hflow i 0 f₀).mp (hf₀.symm ▸ he)
  have hd := hasDerivAt_pairing (d.derivativeWeyl i 0 f₀) (d.derivativeGradient i i 0 f₀)
  have hz : (fun s => matrixPairing (plusWeyl g ((d.flow i).map s f₀).base
      ((d.flow i).map s f₀).frame) (plusWeylGradient g ((d.flow i).map s f₀).base
      ((d.flow i).map s f₀).frame i)) = fun _ => (0 : ℝ) := by
    funext s
    exact d.unit_norm_first_pairing hflow hnorm _ ((hflow i s f₀).mpr hp) i
  rw [hz] at hd
  have h := hd.unique (hasDerivAt_const 0 (0 : ℝ))
  change matrixPairing (plusWeylGradient g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i)
    (plusWeylGradient g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i) +
    matrixPairing (plusWeyl g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame)
      (plusWeylHessian g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i i) = 0 at h
  rw [hf₀] at h
  exact h

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

theorem actual_unit_weyl_parallel (hRic : RicciThree g)
    (hnorm : ∀ x, plusNorm o x = 1) (e : FrameBundle g) (he : e ∈ o.positive) :
    (∀ i, plusWeylGradient g e.base e.frame i = 0) ∧
      normalizedDeterminantShape (plusWeyl g e.base e.frame) = 1 := by
  let p := canonicalParallelMetricData g o hRic
  let d := p.toMetricGreenData
  have hflow : OrientationPreservingFlow d o := canonicalParallelMetricData_orientation o hRic
  have hsecond := d.unit_norm_second_pairing hflow hnorm e he
  let A := plusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let X := plusWeylHessian g e.base e.frame
  have hlin : (∑ i, matrixPairing A (X i i)) = matrixPairing A (hessianTrace X) := by
    simp only [← inner_matrixVector]
    rw [← inner_sum]
    congr 1
  have hsum : (∑ i, matrixPairing (Z i) (Z i)) + matrixPairing A (weylLaplacian A) = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun i _ => hsecond i)
    rw [Finset.sum_add_distrib] at h
    change (∑ i, matrixPairing (Z i) (Z i)) + (∑ i, matrixPairing A (X i i)) = 0 at h
    rw [hlin, metric_weyl_trace g d.weyl] at h
    exact h
  have hA : normalizedBlockNorm A = 1 := by
    rw [← actual_plusNorm_frame o e he]
    exact hnorm e.base
  have hp := weylLaplacian_pairing A (d.weyl.symmetric e) (d.weyl.traceFree e)
  rw [hA] at hp
  have hs := normalizedDeterminantShape_le_one A (d.weyl.symmetric e) (d.weyl.traceFree e)
  have hnn (i : Fin 4) : 0 ≤ matrixPairing (Z i) (Z i) := by
    rw [matrixPairing_self_norm]
    positivity
  have hnonneg := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnn i)
  have hzero : (∑ i, matrixPairing (Z i) (Z i)) = 0 := by nlinarith
  constructor
  · intro i
    have hi : matrixPairing (Z i) (Z i) ≤ ∑ j, matrixPairing (Z j) (Z j) :=
      Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hn : normalizedBlockNorm (Z i) = 0 := by
      rw [matrixPairing_self_norm] at hi
      nlinarith [normalizedBlockNorm_nonneg (Z i)]
    exact (normalizedBlockNorm_eq_zero_iff _).mp hn
  · change normalizedDeterminantShape A = 1
    nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit-norm Weyl curvature yields the parallel rank-one orthogonal
projector (W+ + I)/3. The polynomial relation comes from the actual
second derivative and Weyl equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}
  {μ : Measure (FrameBundle g)}

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.projectorNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.projectorNormedSpace
theorem actual_unit_weyl_polynomial (hRic : RicciThree g)
    (hnorm : ∀ x, plusNorm o x = 1) (e : FrameBundle g) (he : e ∈ o.positive) :
    plusWeyl g e.base e.frame * plusWeyl g e.base e.frame =
      plusWeyl g e.base e.frame + (2 : ℝ) • (1 : Mat) := by
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hf : OrientationPreservingFlow d o := canonicalParallelMetricData_orientation o hRic
  have hg f hf' := (actual_unit_weyl_parallel hRic hnorm f hf').1
  have hx := d.hessian_zero_of_gradient_zero hf hg e he
  have hL : weylLaplacian (plusWeyl g e.base e.frame) = 0 := by
    rw [← metric_weyl_trace g d.weyl]
    simp only [hessianTrace, hx, Finset.sum_const_zero]
  have hn : normalizedBlockNorm (plusWeyl g e.base e.frame) = 1 := by
    rw [← actual_plusNorm_frame o e he, hnorm]
  have ht : Matrix.trace (plusWeyl g e.base e.frame * plusWeyl g e.base e.frame) = 6 := by
    rw [trace_square_eq_six_norm_sq _ (d.weyl.symmetric e), hn]
    norm_num
  ext i j
  have h := congrFun (congrFun hL i) j
  simp only [weylLaplacian, traceFreeSquare, Matrix.smul_apply, Matrix.sub_apply,
    ht, smul_eq_mul, Matrix.zero_apply] at h
  change (plusWeyl g e.base e.frame * plusWeyl g e.base e.frame) i j = _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature operator is at most three on self-dual forms when the
remaining Weyl block is bounded above by two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian
open scoped BigOperators
noncomputable section

theorem halfFlat_curvature_matrix_positive (T : Mat) (a : TwoFormFour)
    (ha : twoFormHodge a = a) :
    twoFormMatrixMul (twoFormCurvatureMatrix (fun v =>
      einsteinCurvatureTensor T 0 (v 0) (v 1) (v 2) (v 3))) a =
      WithLp.toLp 2 ![((1 + T) *ᵥ ![a 0,a 1,a 2]) 0,
        ((1 + T) *ᵥ ![a 0,a 1,a 2]) 1, ((1 + T) *ᵥ ![a 0,a 1,a 2]) 2,
        ((1 + T) *ᵥ ![a 0,a 1,a 2]) 2, -((1 + T) *ᵥ ![a 0,a 1,a 2]) 1,
        ((1 + T) *ᵥ ![a 0,a 1,a 2]) 0] := by
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  ext i
  fin_cases i <;>
    simp [twoFormMatrixMul, twoFormCurvatureMatrix, einsteinCurvatureTensor,
      blockTensor, twoFormProduct, quaternionMatrix, oppositeMatrix, oppositeQuaternion,
      AlgebraicCurvature.pair, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply,
      Fin.sum_univ_succ, h3, h4, h5] <;> ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


