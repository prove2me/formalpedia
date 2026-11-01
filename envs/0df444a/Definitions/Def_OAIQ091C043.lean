-- Prove2me | Definitions.Def_OAIQ091C043
-- name    : OAIQ091C043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:27:15.691134+00:00
-- url     : https://prove2.me/theorems/906a8add-4fb3-4762-ae95-a70f29cc22b4
-- title:
--   Definitions bundle OAIQ091C043 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 158 declarations of OpenAI's Lean: 29 definitions and 129 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.besselFirstL4Linear`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyBump`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyScalarCommutator`, `OAI.PositiveEinsteinFour.Geometry.hodgeComplexEuler`, `OAI.PositiveEinsteinFour.Geometry.hodgeIndexClosedAddGroup`, `OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms_1`, `OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms`, `OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_1`, `OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_2`, `OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_5`, `OAI.PositiveEinsteinFour.Geometry.localC1Bump`, `OAI.PositiveEinsteinFour.Geometry.localContinuousBump`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselFirstL4`, `OAI.PositiveEinsteinFour.Geometry.scalarConstantToDeRham`, `OAI.PositiveEinsteinFour.Geometry.scalarCriticalExponent`, `OAI.PositiveEinsteinFour.Geometry.scalarCutoffChartL4`, `OAI.PositiveEinsteinFour.Geometry.scalarL4ToL2`, `OAI.PositiveEinsteinFour.Geometry.scalarL4ToL2Linear`, `OAI.PositiveEinsteinFour.Geometry.scalarL4ToLp`, `OAI.PositiveEinsteinFour.Geometry.scalarL4ToLpLinear`, `OAI.PositiveEinsteinFour.Geometry.scalarRadialChartFunction`, `OAI.PositiveEinsteinFour.Geometry.scalarSubcriticalWeight`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicL2`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicL2ToHarmonic`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicToClosed`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicToDeRham`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarBaseL4`, `OAI.PositiveEinsteinFour.Geometry.twoFormL2Hodge`, `OAI.PositiveEinsteinFour.Geometry.unitFormHarmonicAddGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C028`, `OAIQ091C029`, `OAIQ091C044`, `OAIQ091C059`, `OAIQ091C061`, `OAIQ091C064`, `OAIQ091C065`, `OAIQ091C066`, `OAIQ091C067`, `OAIQ091C068`, `OAIQ091C069` and `OAIQ091C070`; the statements `OAI_PositiveEinsteinFour_Geometry_FrameReflectionData_jointHessianGreen` and `OAI_PositiveEinsteinFour_Geometry_smooth_weighted_variance_ae`; the proof of `OAI_PositiveEinsteinFour_Geometry_smooth_weighted_variance_ae`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C025

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Extension of the actual Hodge involution to the L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem smoothL2HodgeLinear_involutive : Function.Involutive (smoothL2HodgeLinear (o := o)) :=
  smoothTwoFormHodge_involutive o

def twoFormL2Hodge : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (smoothL2Hodge (o := o)).toContinuousLinearMap.completion

theorem twoFormL2Hodge_smooth (u : SmoothL2TwoForm o) :
    twoFormL2Hodge (smoothTwoFormToL2 u) = smoothTwoFormToL2 (smoothL2Hodge u) :=
  ContinuousLinearMap.completion_apply_coe _ u

end
end PositiveEinsteinFour.Geometry
end


section

/-! Einstein curvature preserves the actual Hodge splitting. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormMatrixMul_hodge (K : Matrix (Fin 6) (Fin 6) ℝ)
    (h : AlgebraicCurvature.EinsteinRelations K) (a : TwoFormFour) :
    twoFormMatrixMul K (twoFormHodge a) = twoFormHodge (twoFormMatrixMul K a) := by
  have hs10 : K 1 0 = K 0 1 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  ext i
  fin_cases i <;>
    simp [twoFormMatrixMul, Matrix.mulVec, dotProduct, twoFormHodge,
      twoFormHodgeLinear, Fin.sum_univ_succ,
      hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54, h.d0, h.d1, h.d2, h.a01, h.a02,
      h.a03, h.a04, h.a12, h.a13] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormMetricCurvatureAction_hodge (hRic : RicciThree g)
    (e : FrameBundle g) (a : TwoFormFour) :
    twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) (twoFormHodge a) =
      twoFormHodge (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) a) := by
  let R := frameCurvature g e.base e.frame
  let K := AlgebraicCurvature.matrixOf R
  have hl := frame_algebraic_lastSkew e.frame
  have hf := frame_algebraic_firstSkew e.frame
  have hp := frame_algebraic_pairSymmetric e.frame hl
  have hn : AlgebraicCurvature.tensorOf K = R := AlgebraicCurvature.tensorOf_matrixOf hf hl
  have hK : AlgebraicCurvature.EinsteinRelations K :=
    AlgebraicCurvature.einsteinRelations_of_ricci K (AlgebraicCurvature.matrixOf_symmetric hp)
      (by intro j k; rw [hn]; exact frame_algebraic_ricciThree e.frame hRic j k)
  have hlast : ∀ i j k l, twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    change frameTensor e.frame.matrix _ ![i,j,l,k] = -frameTensor e.frame.matrix _ ![i,j,k,l]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact hl i j k l
  have heq (b : TwoFormFour) : twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) b =
      -twoFormMatrixMul K b := by
    ext i
    rw [twoFormCurvatureAction_component _ hlast]
    change -(∑ j, twoFormMetricCurvatureTensor g e
      ![(AlgebraicCurvature.pair i).1,(AlgebraicCurvature.pair i).2,
        (AlgebraicCurvature.pair j).1,(AlgebraicCurvature.pair j).2] * b j) = -(∑ j, K i j * b j)
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change frameTensor e.frame.matrix _ _ * b j = _
    rw [frameTensor_curvatureCoordinates]
    rfl
  rw [heq, heq, map_neg, twoFormMatrixMul_hodge K hK]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Hodge star preserves covariant energy, hence the H1 norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_hodge_self (u : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormHodge o u) (smoothTwoFormHodge o u) =
      smoothTwoFormL2Inner u u := by
  rw [smoothTwoFormL2Inner_self, smoothTwoFormL2Inner_self]
  apply integral_congr_ae
  filter_upwards [] with x
  change ‖twoFormHodge (u.val x)‖ ^ 2 = ‖u.val x‖ ^ 2
  rw [twoFormHodge.norm_map]

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

theorem twoFormInfinitesimalMatrix_signed_square_trace (a : TwoFormFour) :
    (twoFormHodgeMatrix * twoFormInfinitesimalMatrix a * twoFormInfinitesimalMatrix a).trace =
      -4 * inner ℝ a (twoFormHodge a) := by
  change _ = -4 * ∑ i, twoFormHodge a i * a i
  simp [twoFormHodgeMatrix, twoFormInfinitesimalMatrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_succ, twoFormHodge, twoFormHodgeLinear]
  ring

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
theorem regularizedPlusWeylScalar_dirichlet (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o))
    (hflow : OrientationPreservingFlow p.toMetricGreenData o)
    (ε : ℝ) (hε : 0 < ε) :
    smoothScalarDirichlet p (regularizedPlusWeylScalar o ε hε)
      (regularizedPlusWeylScalar o ε hε) =
      ∫ e, ∑ i, p.toMetricGreenData.weylRootFirstField ε hε i e ^ 2
        ∂canonicalFrameMeasure g o := by
  rw [smoothScalarDirichlet_eq_integral]
  apply integral_congr_ae
  filter_upwards [canonicalFrameMeasure_supported g o] with e he
  apply Finset.sum_congr rfl
  intro i _
  rw [regularizedPlusWeylScalar_gradient p o hflow ε hε e he i, pow_two]

theorem sharpScalarSobolev_regularized (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o))
    (hflow : OrientationPreservingFlow p.toMetricGreenData o)
    (hsharp : SharpScalarSobolev o p) (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (∫ e, p.toMetricGreenData.weylRootField ε e ^ 4
      ∂canonicalFrameMeasure g o) ≤
      (∫ e, p.toMetricGreenData.weylRootField ε e ^ 2
        ∂canonicalFrameMeasure g o) +
      (∫ e, ∑ i, p.toMetricGreenData.weylRootFirstField ε hε i e ^ 2
        ∂canonicalFrameMeasure g o) / 2 := by
  rw [regularizedPlusWeylScalar_moment o p ε hε 4,
    regularizedPlusWeylScalar_moment o p ε hε 2,
    ← regularizedPlusWeylScalar_dirichlet o p hflow ε hε]
  exact hsharp (regularizedPlusWeylScalar o ε hε)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-zero differential as a linear map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem smoothScalarDifferential_const (c : ℝ) :
    smoothScalarDifferential g (smoothScalarConst c) = 0 := by
  apply Subtype.ext
  funext x a
  change covariantDerivative g x
    (covariantFieldCoordinates (smoothScalarCovariantField (smoothScalarConst c)).val x)
    (chartAt FourSpace x x) a = 0
  rw [smoothScalarCovariantField_coordinates]
  simp [covariantDerivative, scalarCoordinates, smoothScalarConst, partialDeriv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Sobolev energy as a genuine Hilbert norm.  Only the four
first-derivative coordinates are rescaled; the value coordinate is unchanged. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

section Canonical

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarWeighted_baseProbability
/-- On smooth scalars the Hilbert norm is exactly the Sobolev quotient denominator. -/
theorem smoothScalarToWeightedH1_norm_sq (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    ‖smoothScalarToWeightedH1 d a‖ ^ 2 =
      (∫ x, a.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet d a a / 2 := by
  rw [show smoothScalarToWeightedH1 d a =
    scalarWeightedH1Equiv d (smoothScalarToH1 d a) from rfl, scalarWeightedH1_norm_sq]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth]
  have hv : ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 =
      ∫ x, a.val x ^ 2 ∂normalizedVolume g := by
    rw [← scalarBasePullback_smooth g o a, (scalarBasePullback g o).norm_map,
      ← real_inner_self_eq_norm_sq]
    change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ)))
      (ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ))) = _
    rw [ContinuousMap.inner_toLp]
    simp only [conj_trivial, pow_two]
    rfl
  rw [hv]
  simp only [smoothScalarDirichlet, real_inner_self_eq_norm_sq]
  ring

end Canonical
end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive smooth approximations of the absolute value, with the exact
value error and contraction of the scalar Dirichlet energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarAbs_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarAbs_probability
theorem smoothScalarAbsRegularized_dirichlet_le {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    smoothScalarDirichlet d (smoothScalarAbsRegularized a ε hε)
      (smoothScalarAbsRegularized a ε hε) ≤ smoothScalarDirichlet d a a := by
  rw [smoothScalarDirichlet_eq_integral, smoothScalarDirichlet_eq_integral]
  apply integral_mono
  · exact (continuous_finsetSum _ (fun i _ =>
      (actual_scalarGradient_continuous g (smoothScalarAbsRegularized a ε hε).property i).mul
        (actual_scalarGradient_continuous g (smoothScalarAbsRegularized a ε hε).property i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ (fun i _ =>
      (actual_scalarGradient_continuous g a.property i).mul
        (actual_scalarGradient_continuous g a.property i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro e
    apply Finset.sum_le_sum
    intro i _
    simpa only [pow_two] using smoothScalarAbsRegularized_gradient_sq_le d a ε hε e i

theorem smoothScalarAbsRegularized_energy_le {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    ‖smoothScalarToWeightedH1 d (smoothScalarAbsRegularized a ε hε)‖ ^ 2 ≤
      ‖smoothScalarToWeightedH1 d a‖ ^ 2 + ε ^ 2 := by
  rw [smoothScalarToWeightedH1_norm_sq o d, smoothScalarToWeightedH1_norm_sq o d]
  have hi : Integrable (fun x : M => a.val x ^ 2) (normalizedVolume g) :=
    (a.property.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, (smoothScalarAbsRegularized a ε hε).val x ^ 2 ∂normalizedVolume g) =
      (∫ x, a.val x ^ 2 ∂normalizedVolume g) + ε ^ 2 := by
    simp only [smoothScalarAbsRegularized_sq]
    rw [integral_add hi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [he]
  linarith [smoothScalarAbsRegularized_dirichlet_le o d a ε hε]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact weak minimum principle in the actual H1 space. A smooth
bounded monotone test detects every negative value without presupposing
pointwise second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- Subtracting a smooth barrier preserves the weak equation, with its
actual geometric Laplacian subtracted from the source. -/
theorem scalarH1_sub_smooth_weak_equation (d : ParallelMetricData g μ)
    (u : scalarH1 d) (F : ScalarL2 g μ)
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (b : SmoothScalar (M := M)) (ε : ℝ) (v : scalarH1 d) :
    (∑ i : Fin 4, inner ℝ
      (scalarH1Gradient d i (u - ε • smoothScalarToH1 d b)) (scalarH1Gradient d i v)) =
        -(inner ℝ (F - ε • smoothScalarLaplacianL2 (μ := μ) b) (scalarH1Value d v)) := by
  have hb := scalarH1_green d v b
  simp only [map_sub, map_smul, scalarH1Gradient_smooth,
    inner_sub_left, real_inner_smul_left, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [heq]
  have hs : (∑ i : Fin 4, inner ℝ (smoothScalarGradientL2 d i b)
      (scalarH1Gradient d i v)) = -(inner ℝ (smoothScalarLaplacianL2 (μ := μ) b)
      (scalarH1Value d v)) := by
    simpa only [real_inner_comm] using hb
  rw [hs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Barrier comparison for the actual H1 solution with a continuous base
representative. Only the barrier is required to be smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weakBarrier_frameCompact
theorem scalarH1_barrier_comparison (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (b : SmoothScalar (M := M)) {ε c₀ : ℝ} (hε : 0 < ε) (hc₀ : 0 ≤ c₀)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ c₀ * f e.base)
    (hb : ∀ e : FrameBundle g, f e.base < ε * b.val e.base →
      c₀ * b.val e.base < scalarLaplacian g b.val e) :
    ∀ x, ε * b.val x ≤ f x := by
  let v := u - ε • smoothScalarToH1 d b
  let G := F - ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b
  have hv : scalarH1Value d v =ᵐ[canonicalFrameMeasure g o]
      fun e => f e.base - ε * b.val e.base := by
    dsimp only [v]
    rw [map_sub, map_smul, scalarH1Value_smooth]
    filter_upwards [Lp.coeFn_sub (scalarH1Value d u) (ε • smoothScalarValueL2 g
      (canonicalFrameMeasure g o) b),
      Lp.coeFn_smul ε (smoothScalarValueL2 g (canonicalFrameMeasure g o) b),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
        (smoothScalarValue g b), hrep] with e he hsm hbe hue
    change (ε • smoothScalarValueL2 g (canonicalFrameMeasure g o) b) e =
      ε * smoothScalarValueL2 g (canonicalFrameMeasure g o) b e at hsm
    change smoothScalarValueL2 g (canonicalFrameMeasure g o) b e = b.val e.base at hbe
    rw [he]
    change scalarH1Value d u e - (ε • smoothScalarValueL2 g
      (canonicalFrameMeasure g o) b) e = _
    rw [hsm, hbe, hue]
  have hG : G =ᵐ[canonicalFrameMeasure g o]
      fun e => F e - ε * scalarLaplacian g b.val e := by
    filter_upwards [Lp.coeFn_sub F (ε • smoothScalarLaplacianL2
      (μ := canonicalFrameMeasure g o) b),
      Lp.coeFn_smul ε (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
        (smoothScalarLaplacianField g b)] with e he hsm hbe
    change (F - ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b) e = _
    change (ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b) e =
      ε * smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b e at hsm
    change smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b e =
      scalarLaplacian g b.val e at hbe
    rw [he]
    change F e - (ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b) e = _
    rw [hsm, hbe]
  have hn : ∀ᵐ e ∂canonicalFrameMeasure g o, scalarH1Value d v e < 0 → G e < 0 := by
    filter_upwards [hv, hG, hsource] with e hve hGe he
    rw [hve, hGe]
    intro hn
    have hbar := mul_lt_mul_of_pos_left (hb e (sub_neg.mp hn)) hε
    have hcn := mul_nonpos_of_nonneg_of_nonpos hc₀ hn.le
    nlinarith
  have hae := scalarH1_nonneg_of_negative_source d v G
    (fun z => scalarH1_sub_smooth_weak_equation d u F heq b ε z) hn
  have ha : ∀ᵐ e ∂canonicalFrameMeasure g o, 0 ≤ f e.base - ε * b.val e.base := by
    filter_upwards [hae, hv] with e he hv
    rwa [hv] at he
  have hpoint := scalar_continuous_base_nonneg_of_frame_ae g o
    (fun x => f x - ε * b.val x) (hf.sub (continuous_const.mul b.property.continuous)) ha
  intro x
  exact sub_nonneg.mp (hpoint x)

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

/-! Joint continuity of the actual coordinate tensor reconstructed
from a time-dependent normal amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCoordinateTensor_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → TwoFormFour)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source)) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalCoordinateTensor D (A z.1) z.2)
      (Ioi 0 ×ˢ C.source) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hPx := hP.contDiffAt (C.open_source.mem_nhds hz.2)
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) z.2 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hPx.snd i) j
  have hEi (i j : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => (D.point w.2).2⁻¹ i j) z :=
    (heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) z.2 hE
      (heatNormalFrame_matrix_nondegenerate D (hD hz.2)) i j).continuousAt.comp continuousAt_snd
  have hAc := hA.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds hz)
  have hT : ContinuousAt (fun w : ℝ × FourSpace => twoFormTensor (A w.1 w.2)) z :=
    twoFormTensorLinear.toContinuousLinearMap.continuous.continuousAt.comp hAc
  apply continuousAt_pi.mpr
  intro v
  change ContinuousAt (fun w : ℝ × FourSpace =>
    ∑ b, (∏ k, (D.point w.2).2⁻¹ (b k) (v k)) * twoFormTensor (A w.1 w.2) b) z
  apply tendsto_finsetSum
  intro b _
  exact (tendsto_finsetProd _ (fun k _ => hEi (b k) (v k))).mul
    ((continuous_apply b).continuousAt.comp hT)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous family of normal tensors with one compact support
lifts to a jointly continuous family on the actual frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] {g : SmoothMetric M} {c : M}

theorem heatNormalFrameTensorLift_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : ℝ → FourSpace → CovariantCoordinates 2)
    (hT : ContinuousOn (fun z : ℝ × FourSpace => T z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hs : ∀ t > 0, tsupport (T t) ⊆ K) :
    ContinuousOn (fun z : ℝ × FrameBundle g => heatNormalFrameTensorLift g c C (T z.1) z.2)
      (Ioi 0 ×ˢ univ) := by
  have hCK : IsCompact (C '' K) := hK.image_of_continuousOn (C.continuousOn.mono hKC)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hbase : Continuous (fun w : ℝ × FrameBundle g => w.2.base) :=
    (continuous_frameBase g).comp continuous_snd
  by_cases he : z.2.base ∈ C.target
  · have hinv : ContinuousAt (fun w : ℝ × FrameBundle g => C.symm w.2.base) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2.base) (x := z)
        (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)) hbase.continuousAt
    have harg : ContinuousAt (fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base)) z :=
      continuousAt_fst.prodMk hinv
    have hTc : ContinuousAt (fun w : ℝ × FourSpace => T w.1 w.2) (z.1, C.symm z.2.base) :=
      hT.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds
        (show (z.1, C.symm z.2.base) ∈ Ioi (0 : ℝ) ×ˢ C.source from ⟨hz.1, C.map_target he⟩))
    have hval : ContinuousAt (fun w : ℝ × FrameBundle g => T w.1 (C.symm w.2.base)) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base))
        (x := z) hTc harg
    have hframe : ContinuousAt (fun w : ℝ × FrameBundle g =>
        frameTensor (frameChartMatrix g c w.2) (T w.1 (C.symm w.2.base))) z := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2) (x := z)
          (frameChartMatrix_continuousAt g c z.2 (hCt he) (b k) (a k)) continuousAt_snd)).mul
        ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (C.open_target.mem_nhds he)
    filter_upwards [hn] with w hw
    exact ite_eq_left hw
  · have hnot : z.2.base ∉ C '' K := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hKC hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 2))).congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (hCK.isClosed.isOpen_compl.mem_nhds hnot)
    have ht : ∀ᶠ w : ℝ × FrameBundle g in 𝓝 z, 0 < w.1 :=
      continuousAt_fst.eventually (Ioi_mem_nhds hz.1)
    filter_upwards [hn, ht] with w hw hwt
    apply not_ne_iff.mp
    intro hne
    obtain ⟨x, hx, hxe⟩ := heatNormalFrameTensorLift_support g c C (T w.1) hne
    exact hw ⟨x, hs w.1 hwt hx, hxe⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Additivity of the actual normal amplitude realization, needed to
retain cancellation in the heat residual before estimating its norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCoordinateTensor_add (a b : FourSpace → TwoFormFour) :
    heatNormalCoordinateTensor D (a + b) =
      heatNormalCoordinateTensor D a + heatNormalCoordinateTensor D b := by
  funext x v
  change frameTensor (D.point x).2⁻¹ (twoFormTensor (a x + b x)) v = _
  rw [show twoFormTensor (a x + b x) = twoFormTensor (a x) + twoFormTensor (b x) from
    twoFormTensorLinear.map_add _ _, frameTensor_add]
  rfl

omit [T3Space M] [CompactSpace M] in
theorem heatNormalFrameTensorLift_add (C : OpenPartialHomeomorph FourSpace M)
    (T U : FourSpace → CovariantCoordinates 2) :
    heatNormalFrameTensorLift g c C (T + U) =
      heatNormalFrameTensorLift g c C T + heatNormalFrameTensorLift g c C U := by
  classical
  funext f v
  by_cases hf : f.base ∈ C.target
  · simp only [heatNormalFrameTensorLift, ite_eq_left hf, Pi.add_apply, frameTensor_add]
  · simp only [heatNormalFrameTensorLift, ite_eq_right hf, Pi.add_apply, Pi.zero_apply, add_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatNormalAmplitudeL2_add
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source) :
    heatNormalAmplitudeL2 D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalAmplitudeL2 D C hCt hP hD a ha hca hsa +
        heatNormalAmplitudeL2 D C hCt hP hD b hb hcb hsb := by
  have hT : heatNormalAmplitudeTensor D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalAmplitudeTensor D C hCt hP hD a ha hca hsa +
        heatNormalAmplitudeTensor D C hCt hP hD b hb hcb hsb := by
    ext f v
    change heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D (a + b)) f v = _
    rw [heatNormalCoordinateTensor_add, heatNormalFrameTensorLift_add]
    rfl
  change twoFormFromContinuousTensor _ = twoFormFromContinuousTensor _ + twoFormFromContinuousTensor _
  rw [hT, map_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Jointly continuous compact normal amplitudes give continuous curves
in the actual global two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance instCompactSpaceFrameBundle_7_re05e1d_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
theorem heatNormalAmplitudeL2_continuous_family
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → TwoFormFour) (ha : ∀ t, ContDiff ℝ 2 (A t))
    (hc : ∀ t, HasCompactSupport (A t)) (hs : ∀ t, tsupport (A t) ⊆ C.source)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hsK : ∀ t > 0, tsupport (A t) ⊆ K) :
    ContinuousOn (fun t => heatNormalAmplitudeL2 D C hCt hP hD (A t) (ha t) (hc t) (hs t)) (Ioi 0) := by
  have hcoord := heatNormalCoordinateTensor_joint_continuous C hP hD A hA
  have hframe := heatNormalFrameTensorLift_joint_continuous (g := g) C hCt
    (fun t => heatNormalCoordinateTensor D (A t)) hcoord K hK hKC
    (fun t ht => (heatNormalCoordinateTensor_support D (A t)).trans (hsK t ht))
  have hTF : ContinuousOn (fun z : ℝ × FrameBundle g =>
      (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D (A z.1)) z.2)
        : TwoTensorEuclidean)) (Ioi 0 ×ˢ univ) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn hframe
  have hcurve : ContinuousOn (fun t => heatNormalAmplitudeTensor D C hCt hP hD
      (A t) (ha t) (hc t) (hs t)) (Ioi 0) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry _ hTF
  exact twoFormFromContinuousTensor.continuous.comp_continuousOn hcurve

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

theorem heatFamilyPotential_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ n P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (k l : Fin 6) : ContDiffAt ℝ n (fun y => heatFamilyPotential g c P y k l) z := by
  change ContDiffAt ℝ n (fun y =>
    6 * (1 : TwoFormMatrix) k l - 2 * -heatFamilyCurvature g c P y
      ![(AlgebraicCurvature.pair k).1, (AlgebraicCurvature.pair k).2,
        (AlgebraicCurvature.pair l).1, (AlgebraicCurvature.pair l).2]) z
  exact contDiffAt_const.sub (contDiffAt_const.mul
    (heatFamilyCurvature_contDiffAt n g c P z hP hz _).neg)

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

theorem scalarGradient_eq_zero_of_laplacian_eq_zero (g : SmoothMetric M)
    (o : FrameOrientation g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (d : MetricGreenData g (canonicalFrameMeasure g o))
    (s : ScalarCovariantData d a)
    (hLap : ∀ e : FrameBundle g, scalarLaplacian g a e = 0) :
    ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0 := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let := normalizedVolume_isOpenPosMeasure g
  have hE := scalarDirichletDensity_continuous g ha
  have hzero : (∫ e, scalarDirichletDensity g a e.base
      ∂canonicalFrameMeasure g o) = 0 := by
    have h := s.scalar_pairing_green s
    simp only [hLap, mul_zero, integral_zero, neg_zero] at h
    simpa only [scalarDirichletDensity_eq_frame, pow_two] using h
  have hbase : (∫ c, scalarDirichletDensity g a c ∂normalizedVolume g) = 0 := by
    rw [← (canonicalFrameMeasure_base g o).map_eq,
      integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable
        hE.aestronglyMeasurable]
    exact hzero
  have hInt : Integrable (scalarDirichletDensity g a) (normalizedVolume g) :=
    hE.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : scalarDirichletDensity g a =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg (scalarDirichletDensity_nonneg g a) hInt).mp hbase
  have hpoint : scalarDirichletDensity g a = 0 :=
    Measure.eq_of_ae_eq hae hE continuous_const
  intro e i
  have he : (∑ j, scalarGradient g a e j ^ 2) = 0 := by
    rw [← scalarDirichletDensity_eq_frame, hpoint]
    rfl
  have hle : scalarGradient g a e i ^ 2 ≤ ∑ j, scalarGradient g a e j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hs : scalarGradient g a e i ^ 2 = 0 := le_antisymm (he ▸ hle) (sq_nonneg _)
  exact sq_eq_zero_iff.mp hs

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalar_eq_on_exponential_of_gradient_eq_zero (g : SmoothMetric M)
    (o : FrameOrientation g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hgrad : ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) :
    a (frameExponential g o e v) = a e.base := by
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero]
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : FourSpace := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  let Q := directionOrientedMatrix ⟨w, hwn⟩
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (coordinateVector 0) = w :=
    directionRotation_first ⟨w, hwn⟩
  have hexp : frameExponential g o e v = (parallelFrameFlowMap g 0 ‖v‖ f).base := by
    rw [← frameExponential_first_ray g o f hf ‖v‖ hr,
      frameExponential_rotate, map_smul, hdir]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hexp]
  exact scalar_eq_along_parallelFlow_of_gradient_eq_zero g ha hgrad f 0 ‖v‖

end
end PositiveEinsteinFour.Geometry
end


section

/-! A vanishing positively weighted scalar energy has zero actual
differential. Full support is used only on the base manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem scalarGradient_zero_of_weighted_energy (g : SmoothMetric M)
    (o : FrameOrientation g) {a k : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (hk : Continuous k)
    (hpos : ∀ x, 0 < k x)
    (hzero : (∫ e, k e.base * (∑ i, scalarGradient g a e i ^ 2)
      ∂canonicalFrameMeasure g o) = 0) :
    ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0 := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let := normalizedVolume_isOpenPosMeasure g
  have hE : Continuous (fun x => k x * scalarDirichletDensity g a x) :=
    hk.mul (scalarDirichletDensity_continuous g ha)
  have hbase : (∫ c, k c * scalarDirichletDensity g a c ∂normalizedVolume g) = 0 := by
    rw [← (canonicalFrameMeasure_base g o).map_eq,
      integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable
        hE.aestronglyMeasurable]
    simpa only [scalarDirichletDensity_eq_frame] using hzero
  have hnonneg (x : M) : 0 ≤ k x * scalarDirichletDensity g a x :=
    mul_nonneg (hpos x).le (scalarDirichletDensity_nonneg g a x)
  have hInt : Integrable (fun x => k x * scalarDirichletDensity g a x)
      (normalizedVolume g) :=
    hE.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : (fun x => k x * scalarDirichletDensity g a x) =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hInt).mp hbase
  have hpoint : (fun x => k x * scalarDirichletDensity g a x) = 0 :=
    Measure.eq_of_ae_eq hae hE continuous_const
  intro e i
  have hv := congrFun hpoint e.base
  have hz : scalarDirichletDensity g a e.base = 0 :=
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hpos e.base))
  have hs : (∑ j, scalarGradient g a e j ^ 2) = 0 := by
    rwa [scalarDirichletDensity_eq_frame g a e] at hz
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => sq_nonneg (scalarGradient g a e j))
    (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp (le_antisymm (hs ▸ hle) (sq_nonneg _))

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

local instance instAddCommGroupSubtypeSmoothScalarMemSubmoduleRealZeroFormDeRhamCohomology_re05e1d_1 : AddCommGroup (ZeroFormDeRhamCohomology g) := Submodule.addCommGroup _
def scalarConstantToDeRham : ℝ →ₗ[ℝ] ZeroFormDeRhamCohomology g :=
  (scalarConstantLinear (M := M)).codRestrict (ZeroFormDeRhamCohomology g)
    (fun c => smoothScalarDifferential_const c)

variable [T3Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem scalarConstantToDeRham_injective :
    Function.Injective (scalarConstantToDeRham (g := g)) := by
  intro a b hab
  exact congrArg (fun f : ZeroFormDeRhamCohomology g => f.val.val (Classical.arbitrary M)) hab

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarCoordinateJet_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Pull almost-everywhere identities of the actual volume into a chart.
The strict positivity of the constructed metric density is used explicitly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalar_inverse_chart_ae_predicate (g : SmoothMetric M) (c : M)
    (P : M → Prop) (hP : ∀ᵐ x ∂normalizedVolume g, P x) :
    ∀ᵐ z ∂(volume : Measure FourSpace).restrict (chartAt FourSpace c).target,
      P ((chartAt FourSpace c).symm z) := by
  let e := chartAt FourSpace c
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let φ : ChartTarget c → M := fun z => e.symm z.val
  have he : MeasurableEmbedding φ := e.symm.isOpenEmbedding_restrict.measurableEmbedding
  have hsource := ae_restrict_of_ae hP (s := e.source)
  rw [normalizedVolume_restrict_chart g c] at hsource
  have hfactor : normalizedChartFactor g ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)).1.ne'
  have hm : ∀ᵐ x ∂Measure.map φ (μ.withDensity ρ), P x :=
    (Measure.ae_ennreal_smul_measure_iff hfactor).mp hsource
  have hw : ∀ᵐ z ∂μ.withDensity ρ, P (φ z) := he.ae_map_iff.mp hm
  have hd : Measurable ρ := by
    apply Measurable.ennreal_ofReal
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (chartVolumeDensity_contDiffAt g c z z.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hsub : ∀ᵐ z ∂μ, P (φ z) := by
    filter_upwards [(ae_withDensity_iff hd).mp hw] with z hz
    exact hz (ENNReal.ofReal_pos.mpr (chartVolumeDensity_pos g c z z.property)).ne'
  exact (ae_restrict_iff_subtype e.open_target.measurableSet).mpr hsub

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine smooth global radial function that agrees with squared
Euclidean chart distance on the inner ball. Outside that ball its value
stays above the inner squared radius, so it can localize a Hopf barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

def scalarRadialChartFunction (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) : SmoothScalar (M := M) :=
  ⟨fun x => χ.rOut ^ 2 + scalarChartLift c (scalarRadialChartCorrection y χ) x,
    by
    change ContMDiff I4 𝓘(ℝ, ℝ) ∞ _
    exact (contMDiff_const (c := χ.rOut ^ 2)).add (scalarChartLift_smooth c _
      (scalarRadialChartCorrection_smooth y χ) (scalarRadialChartCorrection_compact y χ)
      (scalarRadialChartCorrection_support c y χ hs))⟩

theorem scalarRadialChartFunction_on_source (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {x : M}
    (hx : x ∈ (chartAt FourSpace c).source) :
    (scalarRadialChartFunction c y χ hs).val x = χ.rOut ^ 2 +
      χ (chartAt FourSpace c x) * (‖chartAt FourSpace c x - y‖ ^ 2 - χ.rOut ^ 2) := by
  change χ.rOut ^ 2 + scalarChartLift c _ x = _
  rw [scalarChartLift_on_source c _ hx]
  rfl

theorem scalarRadialChartFunction_off_source (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {x : M}
    (hx : x ∉ (chartAt FourSpace c).source) :
    (scalarRadialChartFunction c y χ hs).val x = χ.rOut ^ 2 := by
  change χ.rOut ^ 2 + scalarChartLift c _ x = _
  simp only [scalarChartLift, ite_eq_right hx, add_zero]

theorem scalarRadialChartFunction_nonneg (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) (x : M) :
    0 ≤ (scalarRadialChartFunction c y χ hs).val x := by
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · rw [scalarRadialChartFunction_on_source c y χ hs hx]
    exact scalarRadialBlend_lower (sq_nonneg _) (sq_nonneg _) χ.nonneg χ.le_one
  · rw [scalarRadialChartFunction_off_source c y χ hs hx]
    exact sq_nonneg _

theorem scalarRadialChartFunction_on_inner (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ closedBall y χ.rIn) :
    (scalarRadialChartFunction c y χ hs).val ((chartAt FourSpace c).symm z) = ‖z - y‖ ^ 2 := by
  have hzt : z ∈ (chartAt FourSpace c).target :=
    hs (closedBall_subset_closedBall χ.rIn_lt_rOut.le hz)
  rw [scalarRadialChartFunction_on_source c y χ hs ((chartAt FourSpace c).map_target hzt),
    (chartAt FourSpace c).right_inv hzt, χ.one_of_mem_closedBall hz]
  ring

theorem scalarRadialChartFunction_small (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {x : M}
    (hx : (scalarRadialChartFunction c y χ hs).val x < χ.rIn ^ 2) :
    x ∈ (chartAt FourSpace c).source ∧ chartAt FourSpace c x ∈ ball y χ.rIn ∧
      (scalarRadialChartFunction c y χ hs).val x = ‖chartAt FourSpace c x - y‖ ^ 2 := by
  have hr : χ.rIn ^ 2 < χ.rOut ^ 2 :=
    (sq_lt_sq₀ χ.rIn_pos.le χ.rOut_pos.le).mpr χ.rIn_lt_rOut
  have hsource : x ∈ (chartAt FourSpace c).source := by
    by_contra hn
    rw [scalarRadialChartFunction_off_source c y χ hs hn] at hx
    exact (not_lt_of_ge hr.le) hx
  have hdist : ‖chartAt FourSpace c x - y‖ < χ.rIn := by
    by_contra hn
    have hsq : χ.rIn ^ 2 ≤ ‖chartAt FourSpace c x - y‖ ^ 2 :=
      (sq_le_sq₀ χ.rIn_pos.le (norm_nonneg _)).mpr (le_of_not_gt hn)
    have hlower := scalarRadialBlend_lower hsq hr.le
      (χ.nonneg (x := chartAt FourSpace c x)) (χ.le_one (x := chartAt FourSpace c x))
    rw [scalarRadialChartFunction_on_source c y χ hs hsource] at hx
    exact (not_lt_of_ge hlower) hx
  have hball : chartAt FourSpace c x ∈ ball y χ.rIn := by
    simpa only [mem_ball, dist_eq_norm] using hdist
  refine ⟨hsource, hball, ?_⟩
  rw [scalarRadialChartFunction_on_source c y χ hs hsource,
    χ.one_of_mem_closedBall (ball_subset_closedBall hball)]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous weak supersolution is positive inside a radial barrier.
The comparison barrier stays positive at the alleged zero, so no
pointwise derivative of the weak solution is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.continuousRadial_frameCompact
theorem scalarH1_no_zero_inside_radial_barrier (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (q : SmoothScalar (M := M)) {a r η B δ : ℝ}
    (hη : 0 < η) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hu : ∀ x, 0 ≤ f x) (hq : ∀ x, 0 ≤ q.val x)
    (hinner : ∀ x, q.val x ≤ a → δ ≤ f x)
    (hgrad : ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      η ≤ ∑ i, scalarGradient g q.val e i ^ 2)
    (hlap : ∀ e : FrameBundle g, scalarLaplacian g q.val e ≤ B)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (x₀ : M) (hqx : q.val x₀ < r) (hux : f x₀ = 0) : False := by
  obtain ⟨k, hk, hlarge⟩ := scalar_barrier_parameter hη hB (by norm_num : (0 : ℝ) ≤ 2)
  let c := Real.exp (-k * r)
  let b := smoothScalarExponentialBarrier q k c
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hble (x : M) : b.val x ≤ 1 := by
    change Real.exp (-k * q.val x) - c ≤ 1
    have he : Real.exp (-k * q.val x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (hq x))
    have hc : 0 ≤ c := (Real.exp_pos _).le
    linarith
  have hbstrict (e : FrameBundle g) (he : f e.base < ε * b.val e.base) :
      2 * b.val e.base < scalarLaplacian g b.val e := by
    have hbpos : 0 < b.val e.base :=
      (mul_pos_iff_of_pos_left hε).mp (lt_of_le_of_lt (hu e.base) he)
    have hqr : q.val e.base < r := by
      change 0 < Real.exp (-k * q.val e.base) - Real.exp (-k * r) at hbpos
      have ht := Real.exp_lt_exp.mp (sub_pos.mp hbpos)
      nlinarith
    have haq : a < q.val e.base := by
      by_contra hn
      have hi := hinner e.base (le_of_not_gt hn)
      have hbound := mul_le_mul_of_nonneg_left (hble e.base) hε.le
      dsimp only [ε] at he hbound
      linarith
    exact scalar_exponential_barrier_strict d q hk.le (Real.exp_pos _).le (by norm_num)
      e (hgrad e haq.le hqr.le) (hlap e) hlarge
  have hcompare : ∀ x, ε * b.val x ≤ f x :=
    scalarH1_barrier_comparison g o d u F heq f hf hrep b hε (by norm_num) hsource hbstrict
  have hbx : 0 < b.val x₀ := by
    change 0 < Real.exp (-k * q.val x₀) - Real.exp (-k * r)
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hc := hcompare x₀
  rw [hux] at hc
  exact (not_le_of_gt (mul_pos hε hbx)) hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! A coordinate bound for every orthonormal-frame gradient component.
This is the reverse estimate needed to transport local derivative integrability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_frame_gradient_sq_le_chart (g : SmoothMetric M) (a : SmoothScalar (M := M))
    (c : M) (z : ChartTarget c) (e : FrameBundle g)
    (he : e.base = (chartAt FourSpace c).symm z) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C) (i : Fin 4) :
    scalarGradient g a.val e i ^ 2 ≤ 16 * C ^ 2 *
      ∑ j, (partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z) ^ 2 := by
  let p := fun j => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z
  have hrow (k : Fin 4) : (∑ j, chartGramMatrix g c 1 z j k * p j) ^ 2 ≤
      (4 * C ^ 2) * ∑ j, p j ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => chartGramMatrix g c 1 z j k) p
    have hsum : (∑ j : Fin 4, chartGramMatrix g c 1 z j k ^ 2) ≤ 4 * C ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin 4, C ^ 2 := Finset.sum_le_sum fun j _ => by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hE j k)
        _ = _ := by simp
    exact hcs.trans (mul_le_mul_of_nonneg_right hsum
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    scalarGradient g a.val e i ^ 2 ≤ ∑ k, scalarGradient g a.val e k ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (scalarGradient g a.val e k)) (Finset.mem_univ i)
    _ = scalarDirichletDensity g a.val e.base := (scalarDirichletDensity_eq_frame g a.val e).symm
    _ = ∑ k, (∑ j, chartGramMatrix g c 1 z j k * p j) ^ 2 := by
      rw [he]
      have hden := scalarDirichletDensity_eq_frame g a.val (chartGramSection g c 1 (by simp) z)
      change scalarDirichletDensity g a.val ((chartAt FourSpace c).symm z) = _ at hden
      rw [hden]
      simp_rw [scalarGradient_chart g a.property c z]
      rfl
    _ ≤ ∑ _k : Fin 4, (4 * C ^ 2) * ∑ j, p j ^ 2 :=
      Finset.sum_le_sum (fun k _ => hrow k)
    _ = _ := by simp; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial chart function has a nonvanishing actual metric
differential on every punctured inner ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

theorem scalarRadialChartFunction_eventually (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ ball y χ.rIn) :
    (fun w => (scalarRadialChartFunction c y χ hs).val ((chartAt FourSpace c).symm w))
      =ᶠ[𝓝 z] fun w => ‖w - y‖ ^ 2 := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact scalarRadialChartFunction_on_inner c y χ hs (ball_subset_closedBall hw)

theorem scalarRadialChartFunction_partial (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ ball y χ.rIn) (i : Fin 4) :
    partialDeriv
      (fun w => (scalarRadialChartFunction c y χ hs).val ((chartAt FourSpace c).symm w)) i z =
        2 * (z i - y i) := by
  unfold partialDeriv
  rw [(scalarRadialChartFunction_eventually c y χ hs hz).fderiv_eq]
  have hd := ((hasFDerivAt_id z).sub_const y).norm_sq
  have hd' : fderiv ℝ (fun w : FourSpace => ‖w - y‖ ^ 2) z =
      2 • (innerSL ℝ (z - y)).comp (ContinuousLinearMap.id ℝ FourSpace) := by
    simpa only [id_eq] using hd.fderiv
  rw [hd']
  have hb : coordinateVector i = (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_apply, innerSL_apply_apply, nsmul_eq_mul, hb,
    EuclideanSpace.inner_basisFun_real]
  rfl

theorem scalarRadialChartFunction_density_pos (g : SmoothMetric M) (c : M)
    (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {z : FourSpace}
    (hz : z ∈ ball y χ.rIn) (hzy : z ≠ y) :
    0 < scalarDirichletDensity g (scalarRadialChartFunction c y χ hs).val
      ((chartAt FourSpace c).symm z) := by
  let a := scalarRadialChartFunction c y χ hs
  have hzt : z ∈ (chartAt FourSpace c).target :=
    hs (closedBall_subset_closedBall χ.rIn_lt_rOut.le (ball_subset_closedBall hz))
  by_contra hn
  have hzero : scalarDirichletDensity g a.val ((chartAt FourSpace c).symm z) = 0 :=
    le_antisymm (le_of_not_gt hn) (scalarDirichletDensity_nonneg g a.val _)
  apply hzy
  ext i
  have h := scalarCoordinate_gradient_sq_le g a.property c ⟨z, hzt⟩ i
  rw [hzero, mul_zero] at h
  have hp := scalarRadialChartFunction_partial c y χ hs hz i
  change partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z = _ at hp
  rw [hp] at h
  nlinarith [sq_nonneg (2 * (z i - y i))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute coordinate estimates for an arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_frame_gradient_abs_le_chart (g : SmoothMetric M)
    (a : SmoothScalar (M := M)) (c : M) (z : ChartTarget c) (e : FrameBundle g)
    (he : e.base = (chartAt FourSpace c).symm z) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C) (i : Fin 4) :
    |scalarGradient g a.val e i| ≤ 4 * C *
      ∑ j, |partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z| := by
  let p := fun j => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) j z
  have hp : 0 ≤ ∑ j, |p j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hC) hp)).mp
  rw [sq_abs]
  have hs : ∑ j, p j ^ 2 ≤ (∑ j, |p j|) ^ 2 := by
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (p j)))
  calc
    _ ≤ 16 * C ^ 2 * ∑ j, p j ^ 2 := scalar_frame_gradient_sq_le_chart g a c z e he C hC hE i
    _ ≤ 16 * C ^ 2 * (∑ j, |p j|) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact annular bounds for the actual smooth radial chart function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.radialAnnulus_frameCompact
omit [CompactSpace M] in
theorem scalar_radial_annulus_gradient_pos (g : SmoothMetric M)
    (c : M) (y : FourSpace) (χ : ContDiffBump y)
    (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) {a r : ℝ}
    (ha : 0 < a) (hr : r < χ.rIn ^ 2) (e : FrameBundle g)
    (he₁ : a ≤ (scalarRadialChartFunction c y χ hs).val e.base)
    (he₂ : (scalarRadialChartFunction c y χ hs).val e.base ≤ r) :
    0 < ∑ i, scalarGradient g (scalarRadialChartFunction c y χ hs).val e i ^ 2 := by
  obtain ⟨hsource, hball, heq⟩ := scalarRadialChartFunction_small c y χ hs (he₂.trans_lt hr)
  have hneq : chartAt FourSpace c e.base ≠ y := by
    intro hy
    rw [hy, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at heq
    linarith
  have hp := scalarRadialChartFunction_density_pos g c y χ hs hball hneq
  rw [(chartAt FourSpace c).left_inv hsource] at hp
  rwa [scalarDirichletDensity_eq_frame g _ e] at hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local strong minimum principle, using a Euclidean ball
inside one chart and the weak radial barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localContinuousPositive_frameCompact
theorem scalarH1_continuous_no_zero_with_nearby_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hn : ∀ x, 0 ≤ f x)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (c : M) (x y : FourSpace) {R : ℝ} (hR : 0 < R)
    (hchart : closedBall x R ⊆ (chartAt FourSpace c).target)
    (hx : f ((chartAt FourSpace c).symm x) = 0)
    (hy : dist y x < R / 4) (hfy : 0 < f ((chartAt FourSpace c).symm y)) : False := by
  let fc : FourSpace → ℝ := fun z => f ((chartAt FourSpace c).symm z)
  have hsmall : closedBall x (R / 2) ⊆ (chartAt FourSpace c).target :=
    (closedBall_subset_closedBall (by linarith)).trans hchart
  obtain ⟨r, z, hr, hrx, hzy, hfz, hball, hpositive⟩ :=
    scalar_euclidean_positive_contact_ball fc x y hR
      (hf.comp_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hsmall))
      (fun z _ => hn _) hx hy hfy
  let χ : ContDiffBump y :=
    { rIn := 2 * r
      rOut := 3 * r
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target := by
    intro w hw
    apply hchart
    apply mem_closedBall.mpr
    have hdist := dist_triangle w y x
    have hw' : dist w y ≤ 3 * r := mem_closedBall.mp hw
    linarith
  let q := scalarRadialChartFunction c y χ hs
  have hrr : r ^ 2 < χ.rIn ^ 2 := by
    change r ^ 2 < (2 * r) ^ 2
    nlinarith [sq_pos_of_pos hr]
  have hqr : q.val ((chartAt FourSpace c).symm z) = r ^ 2 := by
    have hz : z ∈ closedBall y χ.rIn := by
      apply mem_closedBall.mpr
      change dist z y ≤ 2 * r
      rw [hzy]
      linarith
    rw [scalarRadialChartFunction_on_inner c y χ hs hz]
    rw [← dist_eq_norm, hzy]
  let a := (r / 2) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r ^ 2 := by dsimp [a]; nlinarith [sq_pos_of_pos hr]
  have hqpositive (w : M) (hw : q.val w ≤ a) : 0 < f w := by
    obtain ⟨hwsource, hwball, hwq⟩ := scalarRadialChartFunction_small c y χ hs
      (hw.trans_lt (har.trans hrr))
    have hwinner : chartAt FourSpace c w ∈ ball y r := by
      apply mem_ball.mpr
      rw [dist_eq_norm]
      apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
      rw [← hwq]
      exact hw.trans_lt har
    have hp := hpositive (chartAt FourSpace c w) hwinner
    change 0 < f ((chartAt FourSpace c).symm (chartAt FourSpace c w)) at hp
    rwa [(chartAt FourSpace c).left_inv hwsource] at hp
  let K : Set M := {w | q.val w ≤ a}
  have hK : IsCompact K := (isClosed_le q.property.continuous continuous_const).isCompact
  have hyinner : y ∈ closedBall y χ.rIn := mem_closedBall_self χ.rIn_pos.le
  have hqcenter : q.val ((chartAt FourSpace c).symm y) = 0 := by
    rw [scalarRadialChartFunction_on_inner c y χ hs hyinner]
    simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hKne : K.Nonempty := ⟨(chartAt FourSpace c).symm y, by
    change q.val ((chartAt FourSpace c).symm y) ≤ a
    rw [hqcenter]
    exact ha.le⟩
  obtain ⟨w, hw, hwmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
  have hδ : 0 < f w := hqpositive w hw
  have hinner : ∀ v, q.val v ≤ a → f w ≤ f v := fun v hv => hwmin hv
  let R₁ := (3 * r / 2) ^ 2
  have hrR : r ^ 2 < R₁ := by dsimp [R₁]; nlinarith [sq_pos_of_pos hr]
  have hRr : R₁ < χ.rIn ^ 2 := by
    change (3 * r / 2) ^ 2 < (2 * r) ^ 2
    nlinarith [sq_pos_of_pos hr]
  obtain ⟨η, hη, hgrad⟩ : ∃ η : ℝ, 0 < η ∧ ∀ e : FrameBundle g,
      a ≤ q.val e.base → q.val e.base ≤ R₁ →
        η ≤ ∑ i, scalarGradient g q.val e i ^ 2 :=  scalar_positive_annular_gradient_bound g q
    ⟨frameAt g ((chartAt FourSpace c).symm z), by
      change a ≤ q.val ((chartAt FourSpace c).symm z) ∧
        q.val ((chartAt FourSpace c).symm z) ≤ R₁
      rw [hqr]
      exact ⟨har.le, hrR.le⟩⟩
    (fun e he₁ he₂ => scalar_radial_annulus_gradient_pos g c y χ hs ha hRr e he₁ he₂)
  obtain ⟨B, hB, hlap⟩ := scalar_laplacian_uniform_upper g q
  exact scalarH1_no_zero_inside_radial_barrier g o d u F heq f hf hrep q
    hη hB hδ hn (scalarRadialChartFunction_nonneg c y χ hs) hinner hgrad hlap hsource
    ((chartAt FourSpace c).symm z) (by rw [hqr]; exact hrR) hfz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strict positivity of a nonzero nonnegative weak supersolution on the
connected manifold, from the actual chart contact-ball argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.continuousStrongMin_frameCompact
theorem scalarH1_continuous_strong_minimum (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (hn : ∀ x, 0 ≤ f x)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ 2 * f e.base)
    (hne : ∃ x, 0 < f x) : ∀ x, 0 < f x := by
  let U := {x | 0 < f x}
  have hopen : IsOpen U := isOpen_lt continuous_const hf
  have hclosed : IsClosed U := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxzero : f x = 0 := le_antisymm (le_of_not_gt hx) (hn x)
    let c := chartAt FourSpace x
    let z := c x
    have hxs : x ∈ c.source := mem_chart_source FourSpace x
    have hzt : z ∈ c.target := c.map_source hxs
    obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp c.open_target z hzt
    have hRc : closedBall z (R / 2) ⊆ c.target := by
      intro y hy
      apply hRt
      apply mem_ball.mpr
      have := mem_closedBall.mp hy
      linarith
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ dist (c y) z < (R / 2) / 4 := by
      have hc := (c.continuousAt hxs).tendsto.eventually
        (ball_mem_nhds z (show 0 < (R / 2) / 4 by positivity))
      filter_upwards [c.open_source.mem_nhds hxs, hc] with y hy hz
      exact ⟨hy, hz⟩
    filter_upwards [hnear] with y hy
    change ¬ 0 < f y
    intro hfy
    apply scalarH1_continuous_no_zero_with_nearby_positive g o d u F heq f hf hrep hn hsource
      x z (c y) (half_pos hR) hRc
    · change f (c.symm (c x)) = 0
      rwa [c.left_inv hxs]
    · exact hy.2
    · change 0 < f (c.symm (c y))
      rwa [c.left_inv hy.1]
  have heqU : U = univ := (show IsClopen U from ⟨hclosed, hopen⟩).eq_univ hne
  intro x
  have hx : x ∈ U := heqU ▸ mem_univ x
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

/-- Every first derivative of an H2 distribution has an actual L4 representative. -/
theorem scalar_H2_first_L4 (u : 𝓢'(V, ℂ)) (hu : MemSobolev 2 2 u) (i : Fin 4) :
    ∃ g : L2, (g : 𝓢'(V, ℂ)) = scalarCoordinateDerivative i u ∧
      MemLp (g : V → ℂ) 4 volume := by
  obtain ⟨v, hv⟩ := hu
  have hu' : u = (scalarBesselInverseL2 v : 𝓢'(V, ℂ)) := by
    rw [scalarBesselInverseL2_distribution, ← hv,
      besselPotential_besselPotential_apply]
    norm_num
  refine ⟨scalarBesselFirstL2 i v, ?_, ?_⟩
  · rw [hu', scalarBesselFirstL2_distribution]
  have hdense := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ)
    (μ := (volume : Measure V)) (p := 2) (by norm_num)
  obtain ⟨vs, hvs, ht⟩ := mem_closure_iff_seq_limit.mp (hdense v)
  choose fs hfs using hvs
  have ht' : Tendsto (fun n => (fs n).toLp 2 volume) atTop (𝓝 v) := by
    have he : (fun n => (fs n).toLp 2 volume) = vs := funext (fun n => hfs n)
    rw [he]
    exact ht
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ ht').exists_norm_le
  have hB' (n : ℕ) : ‖(fs n).toLp 2 volume‖ ≤ B := hB _ (mem_range_self n)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  let K : ℝ≥0∞ := (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
    (ENNReal.ofReal h2BumpDerivativeBound * ENNReal.ofReal ((2 * Real.pi) * B) +
      4 * ENNReal.ofReal ((2 * Real.pi) ^ 2 * B))
  have hbound (n : ℕ) : eLpNorm
      (fun x => (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (h2SchwartzInverse (fs n))) x)
      4 volume ≤ K := by
    apply (scalar_schwartz_L4_bound _).trans
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [h2_schwartz_eLpNorm, h2SchwartzInverse_first]
      exact ENNReal.ofReal_le_ofReal ((scalarBesselFirstL2_norm i _).trans
        (mul_le_mul_of_nonneg_left (hB' n) (by positivity)))
    · calc
        _ ≤ ∑ _j : Fin 4, ENNReal.ofReal ((2 * Real.pi) ^ 2 * B) := by
          apply Finset.sum_le_sum
          intro j _
          rw [h2_schwartz_eLpNorm, h2SchwartzInverse_second]
          exact ENNReal.ofReal_le_ofReal ((scalarBesselSecondL2_norm j i _).trans
            (mul_le_mul_of_nonneg_left (hB' n) (by positivity)))
        _ = _ := by simp
  have hconv := (scalarBesselFirstL2 i).continuous.continuousAt.tendsto.comp ht'
  have hconv' := tendstoInMeasure_of_tendsto_Lp hconv
  have hfn (n : ℕ) :
      (scalarBesselFirstL2 i ((fs n).toLp 2 volume) : V → ℂ) =ᵐ[volume]
        (fun x => (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (h2SchwartzInverse (fs n))) x) := by
    rw [← h2SchwartzInverse_first]
    exact SchwartzMap.coeFn_toLp _ _ _
  have hLpbound : ∀ᶠ n in atTop, eLpNorm
      (scalarBesselFirstL2 i ((fs n).toLp 2 volume) : V → ℂ) 4 volume ≤ K :=
    Eventually.of_forall (fun n => by rw [eLpNorm_congr_ae (hfn n)]; exact hbound n)
  exact ⟨Lp.aestronglyMeasurable _, (eLpNorm_le_of_tendstoInMeasure hLpbound hconv'
      (fun n => (Lp.memLp _).aestronglyMeasurable)).trans_lt (by
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
        ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top⟩))⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong L4 continuity of the first derivative of the Bessel inverse.
The existing H2 gradient estimate gives membership; the closed graph theorem
upgrades this to the strong convergence needed in nonlinear second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "L4" => Lp ℂ 4 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions
theorem scalarBesselFirstL2_memLp_four (i : Fin 4) (f : L2) :
    MemLp (scalarBesselFirstL2 i f : V → ℂ) 4 volume := by
  obtain ⟨v, hv, h4⟩ := scalar_H2_first_L4 (scalarBesselInverseL2 f : T)
    (scalarBesselInverseL2_memSobolev f) i
  have heq : v = scalarBesselFirstL2 i f := scalarL2_distribution_injective
    (hv.trans (scalarBesselFirstL2_distribution i f).symm)
  simpa only [heq] using h4

def besselFirstL4Linear (i : Fin 4) : L2 →ₗ[ℂ] L4 where
  toFun f := (scalarBesselFirstL2_memLp_four i f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(scalarBesselFirstL2_memLp_four i (f + g)).coeFn_toLp,
      (scalarBesselFirstL2_memLp_four i f).coeFn_toLp,
      (scalarBesselFirstL2_memLp_four i g).coeFn_toLp,
      Lp.coeFn_add (scalarBesselFirstL2 i f) (scalarBesselFirstL2 i g),
      Lp.coeFn_add ((scalarBesselFirstL2_memLp_four i f).toLp _)
        ((scalarBesselFirstL2_memLp_four i g).toLp _)] with x hfg hf hg h2 h4
    rw [hfg, h4, Pi.add_apply, hf, hg, map_add]
    exact h2
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(scalarBesselFirstL2_memLp_four i (c • f)).coeFn_toLp,
      (scalarBesselFirstL2_memLp_four i f).coeFn_toLp,
      Lp.coeFn_smul c (scalarBesselFirstL2 i f),
      Lp.coeFn_smul c ((scalarBesselFirstL2_memLp_four i f).toLp _)] with x hcf hf h2 h4
    rw [hcf, h4, Pi.smul_apply, hf, map_smul]
    exact h2

theorem besselFirstL4Linear_coe (i : Fin 4) (f : L2) :
    (besselFirstL4Linear i f : V → ℂ) =ᵐ[volume] scalarBesselFirstL2 i f :=
  (scalarBesselFirstL2_memLp_four i f).coeFn_toLp

/-- The first derivative of the inverse Bessel operator is a continuous map
from L2 to L4 in dimension four. -/
def scalarBesselFirstL4 (i : Fin 4) : L2 →L[ℂ] L4 where
  toLinearMap := besselFirstL4Linear i
  cont := (besselFirstL4Linear i).continuous_of_seq_closed_graph (by
    intro f x y hfx hfy
    have hlow := tendstoInMeasure_of_tendsto_Lp
      ((scalarBesselFirstL2 i).continuous.continuousAt.tendsto.comp hfx)
    have hhigh := tendstoInMeasure_of_tendsto_Lp hfy
    have hlow' : TendstoInMeasure volume
        (fun n => (besselFirstL4Linear i (f n) : V → ℂ)) atTop
        (scalarBesselFirstL2 i x : V → ℂ) :=
      hlow.congr (fun n => (besselFirstL4Linear_coe i (f n)).symm) Filter.EventuallyEq.rfl
    apply Lp.ext
    exact (tendstoInMeasure_ae_unique hhigh hlow').trans
      (besselFirstL4Linear_coe i x).symm)

theorem scalarBesselFirstL4_coe (i : Fin 4) (f : L2) :
    (scalarBesselFirstL4 i f : V → ℂ) =ᵐ[volume] scalarBesselFirstL2 i f :=
  besselFirstL4Linear_coe i f

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

/-! Smooth H2 approximation with strong L4 convergence of first derivatives.
This is the convergence required by the quadratic terms in the nonlinear
Hessian chain rule in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_2
theorem scalarSchwartzBesselInverse_first_four (f : S) (i : Fin 4) :
    (D i (scalarSchwartzBesselInverse f)).toLp 4 volume =
      scalarBesselFirstL4 i (f.toLp 2 volume) := by
  apply Lp.ext
  have h2 := (D i (scalarSchwartzBesselInverse f)).coeFn_toLp 2 volume
  rw [scalarSchwartzBesselInverse_first] at h2
  filter_upwards [(D i (scalarSchwartzBesselInverse f)).coeFn_toLp 4 volume,
    scalarBesselFirstL4_coe i (f.toLp 2 volume), h2] with x hx h4 h2
  exact hx.trans (h2.symm.trans h4.symm)

/-- Approximation of an H2 function controls values, first derivatives in
both L2 and L4, and second derivatives in L2 along the same sequence. -/
theorem scalar_H2_schwartz_approximation (u : L2) (hu : MemSobolev 2 2 (u : T)) :
    ∃ (v : L2) (f : ℕ → S),
      u = scalarBesselInverseL2 v ∧
      Tendsto (fun n => (f n).toLp 2 volume) atTop (𝓝 u) ∧
      (∀ i, Tendsto (fun n => (D i (f n)).toLp 2 volume) atTop
        (𝓝 (scalarBesselFirstL2 i v))) ∧
      (∀ i, Tendsto (fun n => (D i (f n)).toLp 4 volume) atTop
        (𝓝 (scalarBesselFirstL4 i v))) ∧
      (∀ i j, Tendsto (fun n => (D i (D j (f n))).toLp 2 volume) atTop
        (𝓝 (scalarBesselSecondL2 i j v))) := by
  obtain ⟨v, hv⟩ := hu
  have hu' : u = scalarBesselInverseL2 v := by
    apply scalarL2_distribution_injective
    change (u : T) = (scalarBesselInverseL2 v : T)
    rw [scalarBesselInverseL2_distribution, ← hv, besselPotential_besselPotential_apply]
    norm_num
  have hdense := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ)
    (μ := (volume : Measure V)) (p := 2) (by norm_num)
  obtain ⟨vs, hvs, ht⟩ := mem_closure_iff_seq_limit.mp (hdense v)
  choose fs hfs using hvs
  have ht' : Tendsto (fun n => (fs n).toLp 2 volume) atTop (𝓝 v) := by
    have he : (fun n => (fs n).toLp 2 volume) = vs := funext (fun n => hfs n)
    rwa [he]
  refine ⟨v, fun n => scalarSchwartzBesselInverse (fs n), hu', ?_, ?_, ?_, ?_⟩
  · simp only [scalarSchwartzBesselInverse_toLp, hu']
    exact (scalarBesselInverseL2.continuous.continuousAt.tendsto).comp ht'
  · intro i
    simp only [scalarSchwartzBesselInverse_first]
    exact ((scalarBesselFirstL2 i).continuous.continuousAt.tendsto).comp ht'
  · intro i
    simp only [scalarSchwartzBesselInverse_first_four]
    exact ((scalarBesselFirstL4 i).continuous.continuousAt.tendsto).comp ht'
  · intro i j
    simp only [scalarSchwartzBesselInverse_second]
    exact ((scalarBesselSecondL2 i j).continuous.continuousAt.tendsto).comp ht'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local division by a smooth positive density at Sobolev order two. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric Filter
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem densityCutoffL2_distribution (φ : S) (w : L2) :
    (densityCutoffL2 φ w : T) = smulLeftCLM ℂ φ (w : T) := by
  unfold densityCutoffL2
  rw [SchwartzMap.toLp]
  exact scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp ∞ volume) w

theorem densityCutoffL2_coe (φ : S) (w : L2) :
    (densityCutoffL2 φ w : V → ℂ) =ᵐ[volume] fun y => φ y * w y := by
  change (((φ.toLp ∞ volume) • w : L2) : V → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp ∞ volume) w,
    φ.coeFn_toLp ∞ volume] with y hy hφ
  simpa only [smul_eq_mul, Pi.mul_apply, hφ] using hy

theorem densityCutoff_support (χ ρ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hρ : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y) :
    tsupport ((scalarCutoffSchwartz χ (fun y => (ρ y)⁻¹) hχ hc hρ) : V → ℂ) ⊆
      tsupport χ :=
  (tsupport_comp_subset (g := Complex.ofReal) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    (fun y => χ y * (ρ y)⁻¹)).trans tsupport_mul_subset_left

theorem scalar_H2_density_division (ρ b : V → ℝ) (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => ρ y * b y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ closedBall (0 : V) (1 / 2))
    (hρ : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y)
    (hρ0 : ∀ y ∈ tsupport χ, ρ y ≠ 0) :
    ∃ v : L2, MemSobolev 2 2 (v : T) ∧
      (v : V → ℂ) =ᵐ[volume] fun y => (χ y * b y : ℝ) := by
  let φ := scalarCutoffSchwartz χ (fun y => (ρ y)⁻¹) hχ hc hρ
  have hφχ : tsupport (φ : V → ℂ) ⊆ tsupport χ := densityCutoff_support χ ρ hχ hc hρ
  have hφc : HasCompactSupport (φ : V → ℂ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hφχ
  have hφs : tsupport (φ : V → ℂ) ⊆ closedBall (0 : V) (1 / 2) :=
    hφχ.trans hs
  refine ⟨densityCutoffL2 φ (scalarComplexL2 w), ?_, ?_⟩
  · rw [densityCutoffL2_distribution]
    exact hreg φ hφc hφs
  have hglob := (ae_restrict_iff' isOpen_ball.measurableSet).mp heq
  filter_upwards [densityCutoffL2_coe φ (scalarComplexL2 w), scalarComplexL2_coe w,
    hglob] with y hv hw hy
  rw [hv, hw]
  change ((χ y * (ρ y)⁻¹ : ℝ) : ℂ) * (w y : ℂ) = _
  by_cases hz : χ y = 0
  · simp only [hz, zero_mul, Complex.ofReal_zero]
  · have ht : y ∈ tsupport χ := subset_tsupport χ hz
    have hin : y ∈ ball (0 : V) 1 := closedBall_subset_ball (by norm_num) (hs ht)
    rw [← hy hin, ← Complex.ofReal_mul]
    congr 1
    calc
      χ y * (ρ y)⁻¹ * (ρ y * b y) = χ y * ((ρ y)⁻¹ * ρ y) * b y := by ring
      _ = χ y * b y := by rw [inv_mul_cancel₀ (hρ0 y ht), mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Extract a C1 representative on a fixed smaller ball from actual local
H4 regularity. The cutoff and its L2 realization are constructed here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff _root_.Topology

noncomputable section

local notation "V" => FourSpace

def localC1Bump : ContDiffBump (0 : V) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! Extract a continuous representative on a fixed smaller ball from actual local
H3 regularity. The cutoff and its L2 realization are constructed here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff _root_.Topology

noncomputable section

local notation "V" => FourSpace

def localContinuousBump : ContDiffBump (0 : V) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded localization of the intrinsic scalar H¹ space into Euclidean
L⁴. The construction uses the actual chart representative and its four
weak derivatives, with a compact smooth cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instFactLeENNRealOfNat_solutions_3_re05e1d_1 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localSobolev_frameCompact
def scalarCutoffChartL4 (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) : SmoothScalar (M := M) →ₗ[ℝ] Lp ℝ 4 (volume : Measure FourSpace) :=
  ScalarEuclideanSobolev.toL4Linear.comp (scalarCutoffChartC1 c hKt χ hχ hc hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real smooth approximation preserving the L2 second derivatives and
L4 first derivatives of the same real H2 function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "L4" => Lp ℝ 4 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_4
/-- A real H2 function has one smooth approximating sequence controlling
all derivatives needed by the second-order nonlinear chain rule. -/
theorem scalar_real_H2_approximation (u : L2) (hu : MemSobolev 2 2 (scalarComplexL2 u : T)) :
    ∃ (f : ℕ → S) (G : Fin 4 → L2) (G4 : Fin 4 → L4) (H : Fin 4 → Fin 4 → L2),
      (∀ i, (G i : V → ℝ) =ᵐ[volume] G4 i) ∧
      Tendsto (fun n => (f n).toLp 2 volume) atTop (𝓝 u) ∧
      (∀ i, Tendsto (fun n => (D i (f n)).toLp 2 volume) atTop (𝓝 (G i))) ∧
      (∀ i, Tendsto (fun n => (D i (f n)).toLp 4 volume) atTop (𝓝 (G4 i))) ∧
      (∀ i j, Tendsto (fun n => (D i (D j (f n))).toLp 2 volume) atTop (𝓝 (H i j))) := by
  obtain ⟨v, f, _, hv, hG, hG4, hH⟩ := scalar_H2_schwartz_approximation (scalarComplexL2 u) hu
  let R2 := Complex.reCLM.compLpL 2 (volume : Measure V)
  let R4 := Complex.reCLM.compLpL 4 (volume : Measure V)
  have hRu : R2 (scalarComplexL2 u) = u := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLp (scalarComplexL2 u), scalarComplexL2_coe u]
      with x hr hu
    change Complex.reCLM.compLp (scalarComplexL2 u) x = u x
    rw [hr, hu]
    rfl
  refine ⟨fun n => (f n).postcompCLM Complex.reCLM,
    fun i => R2 (scalarBesselFirstL2 i v), fun i => R4 (scalarBesselFirstL4 i v),
    fun i j => R2 (scalarBesselSecondL2 i j v), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [Complex.reCLM.coeFn_compLp (scalarBesselFirstL2 i v),
      Complex.reCLM.coeFn_compLp (scalarBesselFirstL4 i v), scalarBesselFirstL4_coe i v]
      with x h2 h4 he
    change Complex.reCLM.compLp (scalarBesselFirstL2 i v) x =
      Complex.reCLM.compLp (scalarBesselFirstL4 i v) x
    rw [h2, h4, he]
  · simp only [scalarSchwartz_re_toLp]
    have ht := R2.continuous.continuousAt.tendsto.comp hv
    simpa only [Function.comp_def, hRu] using! ht
  · intro i
    simp only [scalarSchwartz_re_derivative, scalarSchwartz_re_toLp]
    exact R2.continuous.continuousAt.tendsto.comp (hG i)
  · intro i
    simp only [scalarSchwartz_re_derivative, scalarSchwartz_re_toLp]
    exact R4.continuous.continuousAt.tendsto.comp (hG4 i)
  · intro i j
    simp only [scalarSchwartz_re_derivative, scalarSchwartz_re_toLp]
    exact R2.continuous.continuousAt.tendsto.comp (hH i j)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Second-order Sobolev regularity under the actual affine chart rescaling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

theorem scalarAffineDistribution_memSobolev_two (A : V ≃L[ℝ] V) (q : V)
    (u : T) (hu : MemSobolev 2 2 u) :
    MemSobolev 2 2 (scalarAffineDistribution A q u) := by
  have hcrit := scalar_memSobolev_succ_iff 1 (scalarAffineDistribution A q u)
  norm_num at hcrit
  apply hcrit.mpr
  refine ⟨scalarAffineDistribution_memSobolev_one A q u (hu.mono (by norm_num)), ?_⟩
  intro i
  change MemSobolev 1 2
    (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (scalarAffineDistribution A q u))
  rw [scalarAffineDistribution_derivative]
  have hd := hu.lineDerivOp (m := A (EuclideanSpace.basisFun (Fin 4) ℝ i))
  norm_num at hd
  apply scalarAffineDistribution_memSobolev_one A q
  simpa only [EuclideanSpace.basisFun_apply] using hd

theorem scalarComplexAffinePullbackL2_memSobolev_two (A : V ≃L[ℝ] V) (q : V)
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 2 2 (u : T)) :
    MemSobolev 2 2 (scalarComplexAffinePullbackL2 A q u : T) := by
  rw [← scalarAffineDistribution_L2]
  exact scalarAffineDistribution_memSobolev_two A q u hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single H2 approximation sequence with pointwise convergence as well
as all the strong derivative convergences needed in scalar composition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "L4" => Lp ℝ 4 (volume : Measure V)
local notation "S" => 𝓢(V, ℝ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_5
theorem scalar_real_H2_approximation_ae (u : L2) (hu : MemSobolev 2 2 (scalarComplexL2 u : T)) :
    ∃ (f : ℕ → S) (G : Fin 4 → L2) (G4 : Fin 4 → L4) (H : Fin 4 → Fin 4 → L2),
      (∀ᵐ x ∂(volume : Measure V), Tendsto (fun n => f n x) atTop (𝓝 (u x))) ∧
      Tendsto (fun n => (f n).toLp 2 volume) atTop (𝓝 u) ∧
      (∀ i, Tendsto (fun n => (D i (f n)).toLp 2 volume) atTop (𝓝 (G i))) ∧
      (∀ i, Tendsto (fun n => (D i (f n)).toLp 4 volume) atTop (𝓝 (G4 i))) ∧
      (∀ i j, Tendsto (fun n => (D i (D j (f n))).toLp 2 volume) atTop (𝓝 (H i j))) := by
  obtain ⟨f, G, G4, H, _, hf, hG, hG4, hH⟩ := scalar_real_H2_approximation u hu
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  refine ⟨fun n => f (ns n), G, G4, H, ?_, hf.comp hns.tendsto_atTop,
    fun i => (hG i).comp hns.tendsto_atTop, fun i => (hG4 i).comp hns.tendsto_atTop,
    fun i j => (hH i j).comp hns.tendsto_atTop⟩
  have hco : ∀ᵐ x ∂(volume : Measure V), ∀ n, (f (ns n)).toLp 2 volume x = f (ns n) x :=
    ae_all_iff.mpr (fun n => (f (ns n)).coeFn_toLp 2 volume)
  filter_upwards [hAE, hco] with x hx he
  simpa only [he] using hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closure of the real H2 jet, using actual derivatives of real Schwartz
approximants and the complex distributional Sobolev space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

theorem scalarSchwartz_ofReal_weak_derivative (f : S) (i : Fin 4) :
    scalarCoordinateDerivative i (scalarComplexL2 (f.toLp 2 volume) : T) =
      (scalarComplexL2 ((D i f).toLp 2 volume) : T) := by
  rw [← scalarSchwartz_ofReal_toLp, Lp.toTemperedDistribution_toLp_eq,
    ← scalarSchwartz_ofReal_toLp, Lp.toTemperedDistribution_toLp_eq]
  change (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (f.postcompCLM Complex.ofRealCLM : T)) = _
  rw [lineDerivOp_toTemperedDistributionCLM_eq]
  exact congrArg (fun h : 𝓢(V, ℂ) => (h : T)) (scalarSchwartz_ofReal_derivative f i)

/-- Actual first and second derivative limits of one smooth real sequence
place its value limit in the real H2 Sobolev space. -/
theorem scalar_real_H2_of_strong_jets (f : ℕ → S) (u : L2)
    (g : Fin 4 → L2) (h : Fin 4 → Fin 4 → L2)
    (hf : Tendsto (fun n => (f n).toLp 2 volume) atTop (𝓝 u))
    (hg : ∀ i, Tendsto (fun n => (D i (f n)).toLp 2 volume) atTop (𝓝 (g i)))
    (hh : ∀ i j, Tendsto (fun n => (D i (D j (f n))).toLp 2 volume) atTop (𝓝 (h i j))) :
    MemSobolev 2 2 (scalarComplexL2 u : T) := by
  let C := Complex.ofRealCLM.compLpL 2 (volume : Measure V)
  apply scalar_H2_of_strong_jets (fun n => scalarComplexL2 ((f n).toLp 2 volume))
    (fun i n => scalarComplexL2 ((D i (f n)).toLp 2 volume))
    (fun i j n => scalarComplexL2 ((D i (D j (f n))).toLp 2 volume))
    (scalarComplexL2 u) (fun i => scalarComplexL2 (g i)) (fun i j => scalarComplexL2 (h i j))
  · exact C.continuous.continuousAt.tendsto.comp hf
  · intro i
    exact C.continuous.continuousAt.tendsto.comp (hg i)
  · intro i j
    exact C.continuous.continuousAt.tendsto.comp (hh i j)
  · intro n i
    exact scalarSchwartz_ofReal_weak_derivative (f n) i
  · intro n i j
    exact scalarSchwartz_ofReal_weak_derivative (D j (f n)) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual volume almost-everywhere statements in rescaled chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalar_rescaled_ae_predicate (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0)
    (P : M → Prop) (hP : ∀ᵐ x ∂normalizedVolume g, P x) :
    ∀ᵐ y ∂(volume : Measure FourSpace),
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target →
        P ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y)) := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr
  have hmp : Measure.QuasiMeasurePreserving (fun y : FourSpace => A y + z₀) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hp := hmp.ae ((ae_restrict_iff' (chartAt FourSpace c).open_target.measurableSet).mp
    (scalar_inverse_chart_ae_predicate g c P hP))
  simpa only [A, scalarRescalingLinearEquiv_apply] using hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Open manifold neighborhoods whose smooth cutoffs lie in the H2 chart region. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

omit [T3Space M] in
theorem scalar_elliptic_cutoff_neighborhood (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : 0 < r) :
    ∃ U : Set M, IsOpen U ∧ (chartAt FourSpace c).symm z₀ ∈ U ∧
      U ⊆ (chartAt FourSpace c).source ∧
      ∀ ρ : SmoothScalar (M := M), tsupport ρ.val ⊆ U →
        tsupport (scalarChartCutoff c ρ) ⊆
          (scalarRescaledPoint g c z₀ r) '' closedBall 0 (1 / 2) := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let P : FourSpace ≃ₜ FourSpace := A.toHomeomorph.trans (Homeomorph.addRight z₀.val)
  have hP (y : FourSpace) : P y = scalarRescaledPoint g c z₀ r y :=
    scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
  let V : Set FourSpace := P '' ball 0 (1 / 2)
  have hV : IsOpen V := P.isOpenMap _ isOpen_ball
  let U : Set M := (chartAt FourSpace c).source ∩ (chartAt FourSpace c) ⁻¹' V
  have hU : IsOpen U := (chartAt FourSpace c).isOpen_inter_preimage hV
  have hsub : U ⊆ (chartAt FourSpace c).source := inter_subset_left
  refine ⟨U, hU, ?_, hsub, ?_⟩
  · refine ⟨(chartAt FourSpace c).map_target z₀.property, ?_⟩
    change chartAt FourSpace c ((chartAt FourSpace c).symm z₀) ∈ V
    rw [(chartAt FourSpace c).right_inv z₀.property]
    exact ⟨0, by simp, by simp [P]⟩
  · intro ρ hρ z hz
    obtain ⟨x, hx, rfl⟩ := scalarChartCutoff_support c ρ (hρ.trans hsub) hz
    obtain ⟨y, hy, he⟩ := (hρ hx).2
    exact ⟨y, ball_subset_closedBall hy, (hP y).symm.trans he⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary continuous H¹-to-L⁴ embedding for the actual compact
four-manifold, assembled from compact chart cutoffs. No sharp constant is
asserted here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_6
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_probability
def smoothScalarBaseL4 (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] Lp ℝ 4 (normalizedVolume g) :=
  (ContinuousMap.toLp 4 (normalizedVolume g) ℝ).toLinearMap.comp smoothScalarContinuous

theorem smoothScalarBaseL4_coe (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    smoothScalarBaseL4 g a =ᵐ[normalizedVolume g] a.val :=
  ContinuousMap.coeFn_toLp (p := 4) (𝕜 := ℝ) (normalizedVolume g)
    (smoothScalarContinuous a)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Taking real parts preserves the actual second-order Sobolev space.
The proof transports a single smooth approximation and all its derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "C2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

 theorem scalar_realPart_memSobolev_two (u : C2) (hu : MemSobolev 2 2 (u : T)) :
    MemSobolev 2 2 (scalarComplexL2 (Complex.reCLM.compLp u) : T) := by
  obtain ⟨v, f, _, hf, hg, _, hh⟩ := scalar_H2_schwartz_approximation u hu
  let R := Complex.reCLM.compLpL 2 (volume : Measure V)
  apply scalar_real_H2_of_strong_jets (fun n => (f n).postcompCLM Complex.reCLM)
    (R u) (fun i => R (scalarBesselFirstL2 i v))
    (fun i j => R (scalarBesselSecondL2 i j v))
  · simp only [scalarSchwartz_re_toLp]
    exact R.continuous.continuousAt.tendsto.comp hf
  · intro i
    simp only [scalarSchwartz_re_derivative, scalarSchwartz_re_toLp]
    exact R.continuous.continuousAt.tendsto.comp (hg i)
  · intro i j
    simp only [scalarSchwartz_re_derivative, scalarSchwartz_re_toLp]
    exact R.continuous.continuousAt.tendsto.comp (hh i j)

theorem scalar_real_H2_realization (u : C2) (hu : MemSobolev 2 2 (u : T))
    (b : V → ℝ) (hb : (u : V → ℂ) =ᵐ[volume] fun x => (b x : ℂ)) :
    ∃ v : Lp ℝ 2 (volume : Measure V), MemSobolev 2 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] b := by
  refine ⟨Complex.reCLM.compLp u, scalar_realPart_memSobolev_two u hu, ?_⟩
  filter_upwards [Complex.reCLM.coeFn_compLp u, hb] with x hr hx
  rw [hr, hx]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth finite partitions subordinate to the actual small elliptic neighborhoods. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem scalarPartition_subordinate_neighborhoods (U : M → Set M)
    (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x, x ∈ U x)
    (hchart : ∀ x, U x ⊆ (chartAt FourSpace x).source) :
    ∃ P : ScalarPartition M, ∀ i : P.ι,
      tsupport (scalarPartitionFunction P i).val ⊆ U (P.center i) := by
  have hcover : (univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x _
    exact mem_iUnion_of_mem x (hxU x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have hfinite : (univ : Set M) ⊆ ⋃ x : {x : M // x ∈ s}, U x.val := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨c, hc⟩ hxc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ
    (fun x : {x : M // x ∈ s} => U x.val) (fun x => hU x.val) hfinite
  let P : ScalarPartition M := ⟨s, ρ, fun i => (hρ i).trans (hchart i.val)⟩
  exact ⟨P, hρ⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Returning an actual H2 scalar from normalized coordinates to its chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem scalar_H2_unscale (A : V ≃L[ℝ] V) (q : V) (b χ : V → ℝ)
    (v : L2) (hv2 : MemSobolev 2 2 (v : 𝓢'(V, ℂ)))
    (hv : (v : V → ℂ) =ᵐ[volume] fun y => (χ y * b (A y + q) : ℝ)) :
    ∃ w : L2, MemSobolev 2 2 (w : 𝓢'(V, ℂ)) ∧
      (w : V → ℂ) =ᵐ[volume] fun z => (χ (A.symm (z - q)) * b z : ℝ) := by
  let w := scalarComplexAffinePullbackL2 A.symm (-A.symm q) v
  refine ⟨w, scalarComplexAffinePullbackL2_memSobolev_two _ _ v hv2, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving (fun z : V => A.symm z + (-A.symm q))
      volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  filter_upwards [scalarComplexAffinePullbackL2_coe A.symm (-A.symm q) v,
    hmp.ae_eq_comp hv] with z hz he
  dsimp only [Function.comp_apply] at he
  rw [hz]
  change v (A.symm z + (-A.symm q)) = _ at he
  rw [he]
  simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, map_neg,
    neg_add_cancel_right]
  rw [map_sub]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L⁴ Sobolev representative is the same actual base function as its L² representative of the intrinsic first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

def scalarL4ToL2Linear {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] : Lp ℝ 4 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := ((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)),
      MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)),
      Lp.coeFn_add f g, Lp.coeFn_add
        (((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).toLp f)
        (((Lp.memLp g).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).toLp g)]
      with x hsum hf hg hsource htarget
    rw [hsum, hsource, htarget, Pi.add_apply, Pi.add_apply, hf, hg]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (r • f)).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)),
      Lp.coeFn_smul r f, Lp.coeFn_smul r
        (((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).toLp f)]
      with x hrf hf hsource htarget
    simp only [RingHom.id_apply]
    rw [hrf, hsource, htarget, Pi.smul_apply, Pi.smul_apply, hf]

theorem scalarL4ToL2Linear_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : Lp ℝ 4 μ) : ‖scalarL4ToL2Linear μ f‖ ≤ ‖f‖ := by
  have h := eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (μ := μ) (f := (f : X → ℝ))
    (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hr := ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) h
  change ‖((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  exact hr

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_7
def scalarL4ToL2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] : Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ :=
  (scalarL4ToL2Linear μ).mkContinuous 1 (fun f => by
    simpa only [one_mul] using scalarL4ToL2Linear_bound μ f)

theorem scalarL4ToL2_coe {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : Lp ℝ 4 μ) : scalarL4ToL2 μ f =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual base H1 value remains L4 on compact metric charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartValueL4_compact
theorem scalarLocalL2Product_memLp_four {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K))
    (hf : MemLp (f : FourSpace → ℝ) 4 (volume.restrict K)) :
    MemLp (scalarLocalL2Product hK χ hχ hc hs f : FourSpace → ℝ) 4 volume := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  have hp : MemLp (fun z => χ z * f z) 4 (volume.restrict K) := by
    apply hf.of_le_mul (c := C)
      (hχ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards with z
    first | rw [Pi.mul_apply, norm_mul] | rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _ (mem_range_self z)) (norm_nonneg _)
  have heq : K.indicator (fun z => χ z * f z) = (fun z => χ z * f z) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hs (subset_tsupport χ (left_ne_zero_of_mul hz))
  have hglob : MemLp (fun z => χ z * f z) 4 volume := by
    rw [← heq]
    exact (memLp_indicator_iff_restrict hK).mpr hp
  exact (memLp_congr_ae (scalarLocalL2Product_coe hK χ hχ hc hs f).symm).mp hglob

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and affine rescaling for a continuous
local representative of an actual base L2 scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]

theorem scalar_chart_continuous_unweight (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : 0 < r) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (b : Lp ℝ 2 (normalizedVolume g))
    (ht : ∀ y ∈ closedBall (0 : FourSpace) 1,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (F : FourSpace → ℝ) (hF : Continuous F)
    (heq : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      b ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
        volume.restrict (ball (0 : FourSpace) R)] F) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∃ H : FourSpace → ℝ, ContinuousOn H U ∧
        (fun z => b ((chartAt FourSpace c).symm z)) =ᵐ[volume.restrict U] H := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let U : Set FourSpace := {z | A.symm (z - z₀) ∈ ball (0 : FourSpace) R}
  have hU : IsOpen U := isOpen_ball.preimage (by fun_prop)
  have hz₀ : z₀.val ∈ U := by
    simp only [U, mem_ofPred_eq, sub_self, map_zero, mem_ball, dist_self]
    exact hR
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hUt : U ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have hy : A.symm (z - z₀) ∈ closedBall (0 : FourSpace) 1 :=
      ball_subset_closedBall (ball_subset_ball hR1 hz)
    have h := ht _ hy
    rwa [hinv] at h
  let H : FourSpace → ℝ := fun z => F (A.symm (z - z₀)) / chartVolumeDensity g c z
  have hH : ContinuousOn H U := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    exact (hF.continuousAt.comp (by fun_prop)).div
      (chartVolumeDensity_contDiffAt g c z (hUt hz)).continuousAt
      (chartVolumeDensity_pos g c z (hUt hz)).ne'
  refine ⟨U, hU, hz₀, hUt, H, hH, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving
      (fun z : FourSpace => A.symm (z - z₀)) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have hfun : (fun z : FourSpace => A.symm (z - z₀)) =
        (fun z => A.symm z + (-A.symm z₀)) := by
      funext z
      rw [map_sub, sub_eq_add_neg]
    rw [hfun, scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hglob := hmp.ae ((ae_restrict_iff' isOpen_ball.measurableSet).mp heq)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hglob] with z hz
  intro hzU
  have he := hz hzU
  rw [hinv] at he
  apply (eq_div_iff (chartVolumeDensity_pos g c z (hUt hzU)).ne').mpr
  simpa only [mul_comm] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and affine rescaling for a smooth
local representative of an actual base L2 scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]

theorem scalar_chart_smooth_unweight (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : 0 < r) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (b : Lp ℝ 2 (normalizedVolume g))
    (ht : ∀ y ∈ closedBall (0 : FourSpace) 1,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (F : FourSpace → ℝ) (hF : ContDiff ℝ ∞ F)
    (heq : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      b ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
        volume.restrict (ball (0 : FourSpace) R)] F) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∃ H : FourSpace → ℝ, ContDiffOn ℝ ∞ H U ∧
        (fun z => b ((chartAt FourSpace c).symm z)) =ᵐ[volume.restrict U] H := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let U : Set FourSpace := {z | A.symm (z - z₀) ∈ ball (0 : FourSpace) R}
  have hU : IsOpen U := isOpen_ball.preimage (by fun_prop)
  have hz₀ : z₀.val ∈ U := by
    simp only [U, mem_ofPred_eq, sub_self, map_zero, mem_ball, dist_self]
    exact hR
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hUt : U ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have hy : A.symm (z - z₀) ∈ closedBall (0 : FourSpace) 1 :=
      ball_subset_closedBall (ball_subset_ball hR1 hz)
    have h := ht _ hy
    rwa [hinv] at h
  let H : FourSpace → ℝ := fun z => F (A.symm (z - z₀)) / chartVolumeDensity g c z
  have hH : ContDiffOn ℝ ∞ H U := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    exact (hF.contDiffAt.comp z
      (A.symm.contDiff.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const))).div
      ((chartVolumeDensity_contDiffAt g c z (hUt hz)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (chartVolumeDensity_pos g c z (hUt hz)).ne'
  refine ⟨U, hU, hz₀, hUt, H, hH, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving
      (fun z : FourSpace => A.symm (z - z₀)) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have hfun : (fun z : FourSpace => A.symm (z - z₀)) =
        (fun z => A.symm z + (-A.symm z₀)) := by
      funext z
      rw [map_sub, sub_eq_add_neg]
    rw [hfun, scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hglob := hmp.ae ((ae_restrict_iff' isOpen_ball.measurableSet).mp heq)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hglob] with z hz
  intro hzU
  have he := hz hzU
  rw [hinv] at he
  apply (eq_div_iff (chartVolumeDensity_pos g c z (hUt hzU)).ne').mpr
  simpa only [mul_comm] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local H2 composition. Smooth approximation, bounded coefficient
convergence, L4 multiplication and the closed weak jet prove the chain rule;
no differentiability is assumed of the original L2 representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal ContDiff LineDeriv NNReal _root_.Topology

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℝ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

local instance instFactLeENNRealOfNat_solutions_10_re05e1d_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
theorem scalar_localized_H2_composition (u : L2)
    (hu : MemSobolev 2 2 (scalarComplexL2 u : T))
    (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0} (hLip : LipschitzWith C φ)
    (hzero : φ 0 = 0) {B₁ B₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ B₁)
    (h₂ : ∀ s, |deriv (deriv φ) s| ≤ B₂) :
    ∃ v : L2, MemSobolev 2 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] fun x => χ x * φ (u x) := by
  obtain ⟨fn, G, G4, H, hpoint, hf', hG, hG4, hH⟩ := scalar_real_H2_approximation_ae u hu
  let V₀ : L2 := hLip.compLp hzero u
  let Vn : ℕ → L2 := fun n => hLip.compLp hzero ((fn n).toLp 2 volume)
  have hV : Tendsto Vn atTop (𝓝 V₀) :=
    (hLip.continuous_compLp hzero).continuousAt.tendsto.comp hf'
  let T₀ : Fin 4 → L2 := fun i => scalarDerivativeMultiplier φ hφ h₁ u
    (Lp.aestronglyMeasurable u) (G i)
  have hT (i : Fin 4) := scalarDerivativeMultiplier_tendsto φ hφ h₁ (fun n x => fn n x) u
    (fun n => (fn n).continuous.aestronglyMeasurable) (Lp.aestronglyMeasurable u)
    hpoint (fun n => (D i (fn n)).toLp 2 volume) (G i) (hG i)
  let Q₀ : Fin 4 → Fin 4 → L2 := fun i j => scalarCompositionHessian φ hφ h₁ h₂
    u (Lp.aestronglyMeasurable u) (G4 i) (G4 j) (H i j)
  have hQ (i j : Fin 4) := scalarCompositionHessian_tendsto φ hφ h₁ h₂ (fun n x => fn n x) u
    (fun n => (fn n).continuous.aestronglyMeasurable) (Lp.aestronglyMeasurable u) hpoint
    (fun n => (D i (fn n)).toLp 4 volume) (fun n => (D j (fn n)).toLp 4 volume)
    (fun n => (D i (D j (fn n))).toLp 2 volume) (G4 i) (G4 j) (H i j)
    (hG4 i) (hG4 j) (hH i j)
  let v : L2 := scalarRealSchwartzMultiply χ V₀
  let g : Fin 4 → L2 := fun i => scalarRealSchwartzMultiply (D i χ) V₀ +
    scalarRealSchwartzMultiply χ (T₀ i)
  let h : Fin 4 → Fin 4 → L2 := fun i j =>
    scalarRealSchwartzMultiply (D i (D j χ)) V₀ +
    scalarRealSchwartzMultiply (D j χ) (T₀ i) +
    scalarRealSchwartzMultiply (D i χ) (T₀ j) +
    scalarRealSchwartzMultiply χ (Q₀ i j)
  refine ⟨v, ?_, ?_⟩
  · apply scalar_real_H2_of_strong_jets (fun n => scalarLocalizedCompose χ hc φ hφ (fn n)) v g h
    · simp only [scalarLocalizedCompose_valueLp χ hc φ hφ hLip hzero]
      exact (scalarRealSchwartzMultiply χ).continuous.continuousAt.tendsto.comp hV
    · intro i
      simp only [scalarLocalizedCompose_first_L2 χ hc φ hφ hLip hzero h₁]
      exact ((scalarRealSchwartzMultiply (D i χ)).continuous.continuousAt.tendsto.comp hV).add
        ((scalarRealSchwartzMultiply χ).continuous.continuousAt.tendsto.comp (hT i))
    · intro i j
      simp only [scalarLocalizedCompose_second_L2 χ hc φ hφ hLip hzero h₁ h₂]
      have h₀ := (scalarRealSchwartzMultiply (D i (D j χ))).continuous.continuousAt.tendsto.comp hV
      have h₁ := (scalarRealSchwartzMultiply (D j χ)).continuous.continuousAt.tendsto.comp (hT i)
      have h₂ := (scalarRealSchwartzMultiply (D i χ)).continuous.continuousAt.tendsto.comp (hT j)
      have h₃ := (scalarRealSchwartzMultiply χ).continuous.continuousAt.tendsto.comp (hQ i j)
      exact ((h₀.add h₁).add h₂).add h₃
  · filter_upwards [scalarRealSchwartzMultiply_coe χ V₀, hLip.coeFn_compLp hzero u] with x hv hφu
    rw [hv, hφu]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Lp representatives and convergence in the subcritical range.
The inclusion uses the same almost-everywhere function; the convergence
statement combines small L² norm with a bounded L⁴ norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

def scalarL4ToLpLinear {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) :
    Lp ℝ 4 μ →ₗ[ℝ] Lp ℝ p μ where
  toFun f := ⟨f.val, Lp.antitone hp f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem scalarL4ToLpLinear_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4)
    (f : Lp ℝ 4 μ) : ‖scalarL4ToLpLinear μ p hp f‖ ≤ ‖f‖ := by
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) hp)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_13
def scalarL4ToLp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) :
    Lp ℝ 4 μ →L[ℝ] Lp ℝ p μ :=
  (scalarL4ToLpLinear μ p hp).mkContinuous 1
    (fun f => by simpa only [one_mul] using scalarL4ToLpLinear_bound μ p hp f)

theorem scalarL4ToLp_coe {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4)
    (f : Lp ℝ 4 μ) : (scalarL4ToLp μ p hp f : X → ℝ) = f := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive power nonlinearity has local H2 regularity. Only the
range on the support of the localization matters; the original global
cutoff representative may vanish elsewhere. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal ContDiff NNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)

theorem scalar_localized_H2_positive_power (u : L2)
    (hu : MemSobolev 2 2 (scalarComplexL2 u : T)) (χ : S)
    (hc : HasCompactSupport (χ : V → ℝ)) (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hRange : ∀ᵐ x ∂(volume : Measure V), χ x ≠ 0 → u x ∈ Set.Icc a B) :
    ∃ v : L2, MemSobolev 2 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] fun x => χ x * (u x) ^ q := by
  obtain ⟨φ, hφ, hφc, hzero, ⟨D, hD⟩, hext⟩ := scalar_positive_power_extension a B q ha hB
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  obtain ⟨E, hE⟩ := (hφ'.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).bounded_above_of_compact_support hφc.deriv.deriv
  have h₂ (s : ℝ) : |deriv (deriv φ) s| ≤ E := by
    simpa only [Real.norm_eq_abs] using hE s
  have hLip : LipschitzWith D φ := lipschitzWith_of_nnnorm_deriv_le
    (hφ.differentiable (by simp)) (fun s => by
      exact_mod_cast (show ‖deriv φ s‖ ≤ (D : ℝ) by simpa only [Real.norm_eq_abs] using hD s))
  obtain ⟨v, hv, heq⟩ := scalar_localized_H2_composition u hu χ hc φ hφ hLip hzero hD h₂
  refine ⟨v, hv, ?_⟩
  filter_upwards [heq, hRange] with x hx hr
  rw [hx]
  by_cases hχ : χ x = 0
  · simp only [hχ, zero_mul]
  · rw [(hext _ (hr hχ)).1]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Fourth-power integrability transfers through compact chart reconstruction
and the closed coordinate-to-frame domination inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Function
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

theorem scalarBasePullback_memLp_four (g : SmoothMetric M) (o : FrameOrientation g)
    (f : Lp ℝ 2 (normalizedVolume g)) (hf : MemLp (f : M → ℝ) 4 (normalizedVolume g)) :
    MemLp (scalarBasePullback g o f : FrameBundle g → ℝ) 4 (canonicalFrameMeasure g o) := by
  have hc := hf.comp_measurePreserving (canonicalFrameMeasure_base g o)
  exact (memLp_congr_ae (Lp.coeFn_compMeasurePreserving f (canonicalFrameMeasure_base g o)).symm).mp hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong subcritical convergence for bounded intrinsic H¹ sequences,
using the actual manifold L² compactness and the L²/L⁴ interpolation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_15
theorem scalar_subcritical_cauchy_of_L2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (f : ℕ → Lp ℝ 4 μ) {B : ℝ} (hB : ∀ n, ‖f n‖ ≤ B)
    (h2 : CauchySeq (fun n => scalarL4ToLp μ 2 (by norm_num) (f n))) :
    CauchySeq (fun n => scalarL4ToLp μ (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) (f n)) := by
  let F : ℕ × ℕ → X → ℝ := fun nm x => f nm.1 x - f nm.2 x
  have hF (nm : ℕ × ℕ) : AEStronglyMeasurable (F nm) μ :=
    (Lp.aestronglyMeasurable (f nm.1)).sub (Lp.aestronglyMeasurable (f nm.2))
  have hfour (nm : ℕ × ℕ) : eLpNorm (F nm) 4 μ ≤ ENNReal.ofReal (2 * B) := by
    change eLpNorm ((f nm.1 : X → ℝ) - (f nm.2 : X → ℝ)) 4 μ ≤ _
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub (f nm.1) (f nm.2)),
      ← Lp.enorm_def, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (norm_sub_le _ _).trans (by linarith [hB nm.1, hB nm.2])
  have htwo : Tendsto (fun nm => eLpNorm (F nm) 2 μ) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (cauchySeq_iff_tendsto_dist_atTop_0.mp h2)
    simpa only [Function.comp_def, ENNReal.ofReal_zero, ← edist_dist,
      Lp.edist_def, scalarL4ToLp_coe, F, Pi.sub_def] using h
  have hnorm := scalar_subcritical_eLpNorm_tendsto_zero F hF hp hp4
    ENNReal.ofReal_ne_top hfour htwo
  have hreal := (ENNReal.continuousAt_toReal
    (by simp : (0 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))).tendsto.comp hnorm
  rw [ENNReal.toReal_zero] at hreal
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  convert hreal using 1
  all_goals try with_reducible_and_instances rfl
  funext nm
  rw [dist_eq_norm, Lp.norm_def,
    eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite smooth partition assembles local fourth-power weak gradient bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

omit [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] in
theorem scalarPartitionFunction_abs_le_one (P : ScalarPartition M) (j : P.ι) :
    ∀ x, |(scalarPartitionFunction P j).val x| ≤ (1 : ℝ) := by
  intro x
  change |P.ρ j x| ≤ 1
  rw [abs_of_nonneg (P.ρ.nonneg j x)]
  exact P.ρ.le_one j x

variable [Nonempty M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.gradientAssembly_compact
theorem scalarH1Gradient_memLp_four_of_partition
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (P : ScalarPartition M)
    (u : scalarH1 d) (i : Fin 4)
    (hpieces : ∀ j : P.ι, MemLp
      (scalarH1LocalizedFrame g o d (scalarPartitionFunction P j)
        (scalarPartitionFunction_abs_le_one P j) i u : FrameBundle g → ℝ)
      4 (canonicalFrameMeasure g o)) :
    MemLp (scalarH1Gradient d i u : FrameBundle g → ℝ) 4 (canonicalFrameMeasure g o) := by
  let A := fun j : P.ι => scalarH1LocalizedFrame g o d (scalarPartitionFunction P j)
    (scalarPartitionFunction_abs_le_one P j) i u
  have hs : MemLp (fun e => ∑ j : P.ι, A j e) 4 (canonicalFrameMeasure g o) := by
    simpa only [Finset.sum_apply] using
      (memLp_finsetSum Finset.univ (fun j _ => hpieces j))
  apply (memLp_congr_ae ?_).mp hs
  have hA : ∀ᵐ e ∂canonicalFrameMeasure g o, ∀ j : P.ι,
      A j e = (scalarPartitionFunction P j).val e.base * scalarH1Gradient d i u e := by
    apply eventually_all.mpr
    intro j
    exact scalarL2BoundedMultiplier_coe
      (fun e : FrameBundle g => (scalarPartitionFunction P j).val e.base)
      ((scalarPartitionFunction P j).property.continuous.comp
        (continuous_frameBase g)).aestronglyMeasurable
      (fun e => scalarPartitionFunction_abs_le_one P j e.base) (scalarH1Gradient d i u)
  filter_upwards [hA] with e he
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hsum : (∑ j : P.ι, (scalarPartitionFunction P j).val e.base) = 1 := by
    simpa only [scalarPartitionFunction, finsum_eq_sum_of_fintype] using
      P.ρ.sum_eq_one (mem_univ e.base)
  rw [hsum, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local Euler power is H2 after positivity. The density-weighted
weak solution is first divided by its actual smooth positive density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff NNReal

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)

theorem scalar_local_H2_power_source (ρ b : V → ℝ)
    (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => ρ y * b y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (hρ : ∀ y ∈ closedBall (0 : V) (1 / 2), ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y)
    (hρ0 : ∀ y ∈ closedBall (0 : V) (1 / 2), ρ y ≠ 0)
    (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hRange : ∀ x ∈ closedBall (0 : V) (1 / 2), b x ∈ Icc a B)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℝ))
    (hs : tsupport (ψ : V → ℝ) ⊆ ball 0 (1 / 2)) :
    ∃ v : Lp ℝ 2 (volume : Measure V), MemSobolev 2 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] fun y => ψ y * (b y) ^ q := by
  obtain ⟨χ, hχ, hχc, hχs, hone⟩ := scalar_half_ball_cutoff_of_compact hc hs
  obtain ⟨z, hz2, hz⟩ := scalar_H2_density_division ρ b w heq hreg χ hχ hχc
    (fun y hy => ball_subset_closedBall (hχs hy))
    (fun y hy => hρ y (ball_subset_closedBall (hχs hy)))
    (fun y hy => hρ0 y (ball_subset_closedBall (hχs hy)))
  obtain ⟨u, hu2, hu⟩ := scalar_real_H2_realization z hz2 (fun y => χ y * b y) hz
  have hru : ∀ᵐ x ∂(volume : Measure V), ψ x ≠ 0 → u x ∈ Icc a B := by
    filter_upwards [hu] with x hx hψ
    have hxs := subset_tsupport (ψ : V → ℝ) hψ
    rw [hx, hone x hxs, one_mul]
    exact hRange x (ball_subset_closedBall (hs hxs))
  obtain ⟨v, hv2, hv⟩ := scalar_localized_H2_positive_power u hu2 ψ hc a B q ha hB hru
  refine ⟨v, hv2, ?_⟩
  filter_upwards [hv, hu] with x hx hu
  rw [hx]
  by_cases hψ : ψ x = 0
  · simp only [hψ, zero_mul]
  · rw [hu, hone x (subset_tsupport (ψ : V → ℝ) hψ), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closedness of all finite real weak jets in the distributional Sobolev space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)

theorem scalar_real_integer_jets_closed (n : ℕ) (fs : ℕ → S) (u : L2)
    (G : List (Fin 4) → L2)
    (hf : Tendsto (fun k => (fs k).toLp 2 volume) atTop (𝓝 u))
    (hG : ∀ is, is.length ≤ n →
      Tendsto (fun k => (scalarRealSchwartzJet is (fs k)).toLp 2 volume) atTop (𝓝 (G is))) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 u : T) := by
  let C := Complex.ofRealCLM.compLpL 2 (volume : Measure V)
  apply scalar_integer_jets_closed n (scalarComplexL2 u)
    (fun k => scalarComplexL2 ((fs k).toLp 2 volume))
    (fun is => scalarComplexL2 (G is))
    (fun is k => scalarComplexL2 ((scalarRealSchwartzJet is (fs k)).toLp 2 volume))
  · exact C.continuous.continuousAt.tendsto.comp hf
  · intro is hs
    exact C.continuous.continuousAt.tendsto.comp (hG is hs)
  · intro is _ k
    exact scalarRealSchwartzJet_weak is (fs k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive Euler source, including its density and linear term,
has the local H2 regularity required by the elliptic gain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)
local notation "C2" => Lp ℂ 2 (volume : Measure V)

theorem scalar_local_H2_nonlinear_source (ρ b : V → ℝ)
    (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => ρ y * b y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (hρ : ∀ y ∈ closedBall (0 : V) (1 / 2), ContDiffAt ℝ ∞ ρ y)
    (hρ0 : ∀ y ∈ closedBall (0 : V) (1 / 2), ρ y ≠ 0)
    (a B q A C : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hRange : ∀ x ∈ closedBall (0 : V) (1 / 2), b x ∈ Icc a B)
    (F : C2)
    (hF : (F : V → ℂ) =ᵐ[volume.restrict (ball (0 : V) (1 / 2))]
      fun y => (ρ y * (A * b y + C * (b y) ^ q) : ℝ))
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) :
    MemSobolev 2 2 (smulLeftCLM ℂ ψ (F : T)) := by
  obtain ⟨η, hη, hηc, hηs, hone⟩ := scalar_half_ball_cutoff_of_compact hc hs
  have hinv (y : V) (hy : y ∈ closedBall (0 : V) (1 / 2)) :
      ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y := (hρ y hy).inv (hρ0 y hy)
  let ηS : 𝓢(V, ℝ) := hηc.toSchwartzMap hη
  have hηSs : tsupport (ηS : V → ℝ) ⊆ ball 0 (1 / 2) := hηs
  obtain ⟨v₁, hv₁, he₁⟩ := scalar_local_H2_power_source ρ b w heq hreg hinv hρ0
    a B 1 ha hB hRange ηS hηc hηSs
  obtain ⟨vq, hvq, heq'⟩ := scalar_local_H2_power_source ρ b w heq hreg hinv hρ0
    a B q ha hB hRange ηS hηc hηSs
  let z : C2 := (A : ℂ) • scalarComplexL2 v₁ + (C : ℂ) • scalarComplexL2 vq
  have hz : (z : T) = (A : ℂ) • (scalarComplexL2 v₁ : T) +
      (C : ℂ) • (scalarComplexL2 vq : T) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2) _ = _
    rw [map_add, map_smul, map_smul]
    rfl
  have hz2 : MemSobolev 2 2 (z : T) := by
    rw [hz]
    exact (hv₁.smul (A : ℂ)).add (hvq.smul (C : ℂ))
  let θ : S := scalarCutoffSchwartz η ρ hη hηc
    (fun y hy => hρ y (ball_subset_closedBall (hηs hy)))
  let Γ : S := SchwartzMap.smulLeftCLM ℂ θ ψ
  have hΓ (y : V) : Γ y = ((η y * ρ y : ℝ) : ℂ) * ψ y := by
    simp only [Γ, SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth, smul_eq_mul]
    rfl
  have hzeq : (z : V → ℂ) =ᵐ[volume] fun y =>
      (A * (η y * b y) + C * (η y * (b y) ^ q) : ℝ) := by
    filter_upwards [Lp.coeFn_add ((A : ℂ) • scalarComplexL2 v₁)
        ((C : ℂ) • scalarComplexL2 vq),
      Lp.coeFn_smul (A : ℂ) (scalarComplexL2 v₁),
      Lp.coeFn_smul (C : ℂ) (scalarComplexL2 vq),
      scalarComplexL2_coe v₁, scalarComplexL2_coe vq, he₁, heq']
      with y hz ha hc h₁ hq hv₁ hvq
    change ((A : ℂ) • scalarComplexL2 v₁ + (C : ℂ) • scalarComplexL2 vq) y = _
    rw [hz]
    simp only [Pi.add_apply]
    rw [ha, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h₁, hq, hv₁, hvq]
    simp only [ηS, Real.rpow_one, Complex.ofReal_add, Complex.ofReal_mul]
    rfl
  have hidentity : smulLeftCLM ℂ ψ (F : T) = smulLeftCLM ℂ Γ (z : T) := by
    ext φ
    simp only [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' isOpen_ball.measurableSet).mp hF, hzeq]
      with y hf hz
    simp only [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply Γ.hasTemperateGrowth, smul_eq_mul, hΓ, hz]
    by_cases hy : ψ y = 0
    · simp only [hy, mul_zero, zero_mul]
    · have hys := subset_tsupport (ψ : V → ℂ) hy
      rw [hf (hs hys), hone y hys]
      simp only [one_mul, Complex.ofReal_add, Complex.ofReal_mul]
      ring
  rw [hidentity]
  simpa only [Nat.cast_ofNat] using scalar_memSobolev_schwartz_multiplier 2 Γ (z : T)
    (by simpa only [Nat.cast_ofNat] using hz2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first distributional product rule from actual H2 approximations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

local instance instFactLeENNRealOfNat_solutions_17_re05e1d_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
theorem scalar_real_L2_distribution_injective :
    Function.Injective (fun f : L2 => (scalarComplexL2 f : T)) := by
  intro f g h
  have he := scalarL2_distribution_injective h
  apply Lp.ext
  filter_upwards [scalarComplexL2_coe f, scalarComplexL2_coe g] with x hf hg
  have hh : scalarComplexL2 f x = scalarComplexL2 g x := by rw [he]
  rw [hf, hg] at hh
  exact Complex.ofReal_injective hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual first weak derivative of the localized H2 composition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv ContDiff NNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (f : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f

theorem scalar_localized_H2_composition_derivative (u : L2)
    (hu : MemSobolev 2 2 (scalarComplexL2 u : T)) (Du : Fin 4 → L2)
    (hDu : ∀ i, scalarCoordinateDerivative i (scalarComplexL2 u : T) = (scalarComplexL2 (Du i) : T))
    (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0} (hLip : LipschitzWith C φ)
    (hzero : φ 0 = 0) {B₁ B₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ B₁)
    (h₂ : ∀ s, |deriv (deriv φ) s| ≤ B₂) :
    ∃ v : L2, MemSobolev 2 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] (fun x => χ x * φ (u x)) ∧
      ∀ i, scalarCoordinateDerivative i (scalarComplexL2 v : T) =
        (scalarComplexL2 (scalarRealSchwartzMultiply (D i χ) (hLip.compLp hzero u) +
          scalarRealSchwartzMultiply χ (scalarDerivativeMultiplier φ hφ h₁ u
            (Lp.aestronglyMeasurable u) (Du i))) : T) := by
  obtain ⟨v, hv, hve⟩ := scalar_localized_H2_composition u hu χ hc φ hφ hLip hzero h₁ h₂
  obtain ⟨fs, G, _, _, hpoint, hf, hG, _, _⟩ := scalar_real_H2_approximation_ae u hu
  let U₀ := hLip.compLp hzero u
  let Un : ℕ → L2 := fun k => hLip.compLp hzero ((fs k).toLp 2 volume)
  have hU : Tendsto Un atTop (𝓝 U₀) :=
    (hLip.continuous_compLp hzero).continuousAt.tendsto.comp hf
  have hvalue : scalarRealSchwartzMultiply χ U₀ = v := by
    apply Lp.ext
    filter_upwards [scalarRealSchwartzMultiply_coe χ U₀, hLip.coeFn_compLp hzero u, hve]
      with x hm hu' hv'
    rw [hm, hu', Function.comp_apply, hv']
  refine ⟨v, hv, hve, fun i => ?_⟩
  have hGi : G i = Du i := scalar_real_L2_distribution_injective
    ((scalar_real_jet_limit [i] fs u (G i) hf (hG i)).symm.trans (hDu i))
  have hT := scalarDerivativeMultiplier_tendsto φ hφ h₁ (fun k x => fs k x) u
    (fun k => (fs k).continuous.aestronglyMeasurable) (Lp.aestronglyMeasurable u)
    hpoint (fun k => (D i (fs k)).toLp 2 volume) (G i) (hG i)
  rw [hGi] at hT
  have hlocal : Tendsto (fun k => (scalarLocalizedCompose χ hc φ hφ (fs k)).toLp 2 volume)
      atTop (𝓝 v) := by
    simp only [scalarLocalizedCompose_valueLp χ hc φ hφ hLip hzero]
    rw [← hvalue]
    exact (scalarRealSchwartzMultiply χ).continuous.continuousAt.tendsto.comp hU
  have hfirst : Tendsto (fun k => (D i (scalarLocalizedCompose χ hc φ hφ (fs k))).toLp 2 volume)
      atTop (𝓝 (scalarRealSchwartzMultiply (D i χ) U₀ +
        scalarRealSchwartzMultiply χ (scalarDerivativeMultiplier φ hφ h₁ u
          (Lp.aestronglyMeasurable u) (Du i)))) := by
    simp only [scalarLocalizedCompose_first_L2 χ hc φ hφ hLip hzero h₁]
    exact ((scalarRealSchwartzMultiply (D i χ)).continuous.continuousAt.tendsto.comp hU).add
      ((scalarRealSchwartzMultiply χ).continuous.continuousAt.tendsto.comp hT)
  exact scalar_real_jet_limit [i] (fun k => scalarLocalizedCompose χ hc φ hφ (fs k)) v _ hlocal hfirst

end
end PositiveEinsteinFour.Geometry
end


section

/-! The H3 algebra in dimension four, using the actual H2-by-H3 product
and the first distributional Leibniz identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_real_sobolev_add (s : ℝ) (u v : L2)
    (hu : MemSobolev s 2 (scalarComplexL2 u : T))
    (hv : MemSobolev s 2 (scalarComplexL2 v : T)) :
    MemSobolev s 2 (scalarComplexL2 (u + v) : T) := by
  have he : (scalarComplexL2 (u + v) : T) = (scalarComplexL2 u : T) + (scalarComplexL2 v : T) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2)
      ((Complex.ofRealCLM.compLpL 2 (volume : Measure V)) (u + v)) = _
    rw [map_add, map_add]
    rfl
  rw [he]
  exact hu.add hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalization and the actual energy minimum for the subcritical scalar
Sobolev quotient.  The constant function gives the upper bound one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedMinimum_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedMinimum_probability
theorem smoothScalarToWeightedH1_one_norm_sq (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ‖smoothScalarToWeightedH1 d (smoothScalarConst 1)‖ ^ 2 = 1 := by
  rw [smoothScalarToWeightedH1_norm_sq o d]
  have hd : smoothScalarDirichlet d (smoothScalarConst 1) (smoothScalarConst 1) = 0 := by
    simp only [smoothScalarDirichlet, smoothScalarGradientL2, LinearMap.comp_apply,
      smoothScalarGradient_const, map_zero, inner_zero_left, Finset.sum_const_zero]
  rw [hd]
  change (∫ _ : M, (1 : ℝ) ^ 2 ∂normalizedVolume g) + 0 / 2 = 1
  simp only [one_pow, integral_const, probReal_univ, one_smul, zero_div, add_zero]

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

omit [SecondCountableTopology M] in
theorem scalarBaseHeatRate_eq_zero
    (μ : ScalarBaseEigenIndex g o d) : scalarBaseHeatRate g o d μ = 0 ↔ μ.1.val = 1 := by
  change μ.1.val⁻¹ - 1 = 0 ↔ _
  rw [sub_eq_zero, inv_eq_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical limit in the scalar Sobolev inequality.  The limit is
taken for each actual smooth test function under an integrable bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

def scalarCriticalExponent (n : ℕ) : ℝ := 4 - 1 / ((n : ℝ) + 1)

theorem scalarCriticalExponent_bounds (n : ℕ) :
    2 < scalarCriticalExponent n ∧ scalarCriticalExponent n < 4 := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hi : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hn
  have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
  dsimp [scalarCriticalExponent]
  constructor <;> linarith

theorem scalarCriticalExponent_tendsto :
    Tendsto scalarCriticalExponent atTop (𝓝 4) := by
  change Tendsto (fun n : ℕ => 4 - 1 / ((n : ℝ) + 1)) atTop (𝓝 4)
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := (4 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem scalar_moment_critical_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [TopologicalSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (f : C(X, ℝ)) :
    Tendsto (fun n => (∫ x, |f x| ^ scalarCriticalExponent n ∂μ) ^
      (2 / scalarCriticalExponent n)) atTop (𝓝 (Real.sqrt (∫ x, f x ^ 4 ∂μ))) := by
  have hb : Integrable (fun x => 1 + |f x| ^ 4) μ := by
    exact (continuous_const.add (f.continuous.abs.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => |f x| ^ scalarCriticalExponent n) μ := by
    exact (f.continuous.abs.rpow_const (fun _ => Or.inr
      (le_of_lt (lt_trans (by norm_num) (scalarCriticalExponent_bounds n).1)))).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖|f x| ^ scalarCriticalExponent n‖ ≤ 1 + |f x| ^ 4 := by
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    by_cases hsmall : |f x| ≤ 1
    · have h := Real.rpow_le_one (abs_nonneg (f x)) hsmall
        (le_of_lt (lt_trans (by norm_num) (scalarCriticalExponent_bounds n).1))
      exact h.trans (le_add_of_nonneg_right (pow_nonneg (abs_nonneg _) 4))
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hsmall)
        (scalarCriticalExponent_bounds n).2.le
      have h4 : |f x| ^ scalarCriticalExponent n ≤ |f x| ^ (4 : ℕ) := by
        simpa only [Real.rpow_ofNat] using h
      exact h4.trans (le_add_of_nonneg_left zero_le_one)
  have hpw (x : X) : Tendsto (fun n => |f x| ^ scalarCriticalExponent n)
      atTop (𝓝 (f x ^ 4)) := by
    have h := (tendsto_const_nhds (x := |f x|)).rpow scalarCriticalExponent_tendsto
      (Or.inr (by norm_num : (0 : ℝ) < 4))
    simpa only [Real.rpow_ofNat, (by decide : Even (4 : ℕ)).pow_abs] using h
  have hint := tendsto_integral_of_dominated_convergence (fun x => 1 + |f x| ^ 4)
    hm hb hbound (Filter.Eventually.of_forall hpw)
  have hpow : Tendsto (fun n => 2 / scalarCriticalExponent n) atTop (𝓝 (1 / 2 : ℝ)) := by
    convert tendsto_const_nhds.div scalarCriticalExponent_tendsto (by norm_num : (4 : ℝ) ≠ 0) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  simpa only [Real.sqrt_eq_rpow] using hint.rpow hpow (Or.inr (by norm_num : (0 : ℝ) < 1 / 2))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarCritical_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarCritical_probability
/-- Subcritical inequalities with the sharp constant pass to the exact
critical inequality used in the two Weyl-block gaps. -/
theorem sharpScalarSobolev_of_subcritical_moments (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (hsub : ∀ (p : ℝ), 2 < p → p < 4 → ∀ a : SmoothScalar (M := M),
      (∫ x, |a.val x| ^ p ∂normalizedVolume g) ^ (2 / p) ≤
        (∫ x, a.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet d a a / 2) :
    SharpScalarSobolev o d := by
  intro a
  apply le_of_tendsto (scalar_moment_critical_limit (normalizedVolume g)
    (⟨a.val, a.property.continuous⟩ : C(M, ℝ)))
  exact Eventually.of_forall fun n => hsub (scalarCriticalExponent n)
    (scalarCriticalExponent_bounds n).1 (scalarCriticalExponent_bounds n).2 a

end
end PositiveEinsteinFour.Geometry
end


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

def scalarSubcriticalWeight (p : ℝ) (a : M → ℝ) (x : M) : ℝ :=
  (3 / 2 : ℝ) / a x ^ 4 * (4 - p) * a x ^ (3 - p)

theorem scalar_inverse_hessian_divergence (s : ScalarCovariantData d a)
    (p : ℝ) (ha : ∀ x, 0 < a x)
    (v : ScalarCovariantData d (fun x => (a x ^ 3)⁻¹))
    (hEq : ∀ e : FrameBundle g,
      a e.base * scalarLaplacian g a e -
        2 * (∑ i, scalarGradient g a e i ^ 2) + 2 * a e.base ^ 2 =
          2 * (a e.base) ^ (4 - p))
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, scalarGradient g (fun x => (a x ^ 3)⁻¹) e i *
        scalarTraceFreeHessian g a e i j) +
      (3 / 4 : ℝ) * (a e.base ^ 3)⁻¹ *
        ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j) =
      scalarSubcriticalWeight p a e.base * scalarGradient g a e j := by
  simp_rw [scalar_inverse_cube_gradient s (fun x => ne_of_gt (ha x)) v]
  change (∑ i, ((-3 / a e.base ^ 4) * scalarGradient g a e i) *
      (scalarHessian g a e i j - if i = j then scalarLaplacian g a e / 4 else 0)) +
      (3 / 4 : ℝ) * (a e.base ^ 3)⁻¹ *
        ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j) = _
  rw [scalar_inverse_hessian_algebra (a e.base) (scalarLaplacian g a e)
    (∑ i, scalarThird g a e j i i) (ne_of_gt (ha e.base))
    (scalarGradient g a e) (scalarHessian g a e) j,
    scalar_reciprocal_equation_derivative s p ha hEq]
  unfold scalarSubcriticalWeight
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Localized powers on a positive range have the actual weak first derivative,
including the cutoff term. No smoothness of the original scalar is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal ContDiff NNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (f : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f

theorem scalar_localized_positive_power_weak_derivative (u : L2)
    (hu : MemSobolev 2 2 (scalarComplexL2 u : T)) (Du : Fin 4 → L2)
    (hDu : ∀ i, scalarCoordinateDerivative i (scalarComplexL2 u : T) = (scalarComplexL2 (Du i) : T))
    (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hrange : ∀ᵐ x ∂(volume : Measure V), x ∈ tsupport (χ : V → ℝ) → u x ∈ Icc a B) :
    ∃ v : L2, MemSobolev 2 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] (fun x => χ x * (u x) ^ q) ∧
      ∀ i, ∃ z : L2, scalarCoordinateDerivative i (scalarComplexL2 v : T) = (scalarComplexL2 z : T) ∧
        (z : V → ℝ) =ᵐ[volume] fun x => D i χ x * (u x) ^ q +
          q * (χ x * (u x) ^ (q - 1)) * Du i x := by
  obtain ⟨φ, hφ, hφc, hzero, ⟨C, hC⟩, hext⟩ := scalar_positive_power_extension a B q ha hB
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  obtain ⟨E, hE⟩ := (hφ'.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).bounded_above_of_compact_support hφc.deriv.deriv
  have h₂ (s : ℝ) : |deriv (deriv φ) s| ≤ E := by
    simpa only [Real.norm_eq_abs] using hE s
  have hLip : LipschitzWith C φ := lipschitzWith_of_nnnorm_deriv_le
    (hφ.differentiable (by simp)) (fun s => by
      exact_mod_cast (show ‖deriv φ s‖ ≤ (C : ℝ) by simpa only [Real.norm_eq_abs] using hC s))
  obtain ⟨v, hv, hve, hdv⟩ := scalar_localized_H2_composition_derivative u hu Du hDu χ hc
    φ hφ hLip hzero hC h₂
  refine ⟨v, hv, ?_, fun i => ?_⟩
  · filter_upwards [hve, hrange] with x hv hr
    rw [hv]
    by_cases hx : x ∈ tsupport (χ : V → ℝ)
    · rw [(hext _ (hr hx)).1]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  · let z : L2 := scalarRealSchwartzMultiply (D i χ) (hLip.compLp hzero u) +
      scalarRealSchwartzMultiply χ (scalarDerivativeMultiplier φ hφ hC u
        (Lp.aestronglyMeasurable u) (Du i))
    refine ⟨z, hdv i, ?_⟩
    filter_upwards [Lp.coeFn_add
        (scalarRealSchwartzMultiply (D i χ) (hLip.compLp hzero u))
        (scalarRealSchwartzMultiply χ (scalarDerivativeMultiplier φ hφ hC u
          (Lp.aestronglyMeasurable u) (Du i))),
      scalarRealSchwartzMultiply_coe (D i χ) (hLip.compLp hzero u),
      scalarRealSchwartzMultiply_coe χ (scalarDerivativeMultiplier φ hφ hC u
        (Lp.aestronglyMeasurable u) (Du i)), hLip.coeFn_compLp hzero u,
      scalarDerivativeMultiplier_coe φ hφ hC u (Lp.aestronglyMeasurable u) (Du i), hrange]
      with x hsum hfirst hsecond hvalue hderiv hr
    dsimp only [z]
    rw [hsum, Pi.add_apply, hfirst, hsecond, hvalue, Function.comp_apply, hderiv]
    by_cases hx : x ∈ tsupport (χ : V → ℝ)
    · rw [(hext _ (hr hx)).1, (hext _ (hr hx)).2]
      ring
    · have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hdχ : D i χ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (SchwartzMap.tsupport_lineDerivOp_subset
          (EuclideanSpace.basisFun (Fin 4) ℝ i) χ h))
      simp only [hχ, hdχ, zero_mul, mul_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rational Kato test is an admissible actual Sobolev variation of the
normalized minimum.  Its Euler identity is derived directly from that
minimum, with no additional extension of the weak equation assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoTesting_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoTesting_probability
/-- The actual base representative has the same composition law as its
frame pullback.  Membership in L² is the only integrability requirement. -/
theorem scalarH1_base_composition (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u v : scalarH1 d) (φ : ℝ → ℝ)
    (hv : scalarH1Value d v =ᵐ[canonicalFrameMeasure g o]
      fun e => φ (scalarH1Value d u e))
    (hmem : MemLp (fun x => φ (scalarH1BaseValue g o d u x)) 2 (normalizedVolume g)) :
    scalarH1BaseValue g o d v =ᵐ[normalizedVolume g]
      fun x => φ (scalarH1BaseValue g o d u x) := by
  let f : Lp ℝ 2 (normalizedVolume g) := hmem.toLp _
  have hf : f =ᵐ[normalizedVolume g] fun x => φ (scalarH1BaseValue g o d u x) :=
    MemLp.coeFn_toLp hmem
  have hpu : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o]
      fun e => scalarH1BaseValue g o d u e.base := by
    rw [← scalarH1BaseValue_spec g o d u]
    exact Lp.coeFn_compMeasurePreserving _ (canonicalFrameMeasure_base g o)
  have hpf : scalarBasePullback g o f = scalarH1Value d v := by
    apply Lp.ext
    have hf' := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hf
    filter_upwards [Lp.coeFn_compMeasurePreserving f (canonicalFrameMeasure_base g o),
      hf', hpu, hv] with e he hf heU heV
    change Lp.compMeasurePreserving FrameBundle.base (canonicalFrameMeasure_base g o) f e = _
    rw [he]
    change f e.base = _
    rw [hf, heV, heU]
  have hb : scalarH1BaseValue g o d v = f := by
    apply (scalarBasePullback g o).injective
    rw [scalarH1BaseValue_spec, hpf]
  rw [hb]
  exact hf

theorem scalarH1_katoTest_base_exists (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {lam : ℝ} (hlam : 0 < lam)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1BaseValue g o d v : M → ℝ) =ᵐ[normalizedVolume g]
        (fun x => scalarKatoTest lam (scalarH1BaseValue g o d u x)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[canonicalFrameMeasure g o]
        fun e => scalarKatoTestRate lam (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  obtain ⟨v, hv, hgrad⟩ := scalarH1_katoTest_exists d hlam u
  refine ⟨v, ?_, hgrad⟩
  apply scalarH1_base_composition g o d u v (scalarKatoTest lam)
    hv
  apply (Lp.memLp (scalarH1BaseValue g o d u)).of_le_mul
    ((scalarKatoTest_smooth hlam).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (scalarH1BaseValue g o d u)))
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using scalarKatoTest_abs_le hlam (scalarH1BaseValue g o d u x)

theorem scalarH1_katoSquare_base_exists (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {lam : ℝ} (hlam : 0 < lam)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1BaseValue g o d v : M → ℝ) =ᵐ[normalizedVolume g]
        (fun x => scalarKatoSquare lam (scalarH1BaseValue g o d u x)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[canonicalFrameMeasure g o]
        fun e => scalarKatoSquareRate lam (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  obtain ⟨v, hv, hgrad⟩ := scalarH1_katoSquare_exists d hlam u
  refine ⟨v, ?_, hgrad⟩
  apply scalarH1_base_composition g o d u v (scalarKatoSquare lam)
    hv
  have hLip : LipschitzWith (⟨6 / lam + 1, by positivity⟩ : ℝ≥0) (scalarKatoSquare lam) :=
    lipschitzWith_of_nnnorm_deriv_le ((scalarKatoSquare_smooth hlam).differentiable (by simp))
      (fun s => by
        have hb := scalarKatoSquareRate_abs_le hlam s
        rw [← scalarKatoSquare_deriv hlam s] at hb
        exact_mod_cast (show ‖deriv (scalarKatoSquare lam) s‖ ≤ 6 / lam + 1 by
          simpa only [Real.norm_eq_abs] using hb))
  exact hLip.comp_memLp (scalarKatoSquare_zero lam) (Lp.memLp (scalarH1BaseValue g o d u))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint finite smooth extensions for the normal coefficient family.
The leading amplitude remains strictly positive away from the chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyBump (z₀ : HeatRadialFrameSpace) (r : ℝ) (hr : 0 < r) :
    ContDiffBump z₀ where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem heatFamily_scalar_extension (n : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (z₀ : HeatRadialFrameSpace) (hf : ContDiffAt ℝ n f z₀) :
    ∃ F : HeatRadialFrameSpace → ℝ, ContDiff ℝ n F ∧ HasCompactSupport F ∧
      F =ᶠ[𝓝 z₀] f := by
  obtain ⟨r, hr, hreg⟩ := Metric.eventually_nhds_iff.mp (hf.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let χ := heatFamilyBump z₀ r hr
  have hs : tsupport χ ⊆ ball z₀ r := by
    calc
      tsupport χ = closedBall z₀ (r / 2) := χ.tsupport_eq
      _ ⊆ ball z₀ r := closedBall_subset_ball (by linarith)
  refine ⟨fun z => χ z * f z,
    heatFamilyCutoff_contDiff n χ f χ.contDiff (fun z hz => hreg (hs hz)),
    χ.hasCompactSupport.mul_right, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with z hz
  simp only [hz, Pi.one_apply, one_mul]

theorem heatFamily_positive_extension (n : ℕ) (f : HeatRadialFrameSpace → ℝ)
    (z₀ : HeatRadialFrameSpace) (hf : ContDiffAt ℝ n f z₀) (hpos : 0 < f z₀) :
    ∃ F : HeatRadialFrameSpace → ℝ, ContDiff ℝ n F ∧ (∀ z, 0 < F z) ∧
      F =ᶠ[𝓝 z₀] f := by
  have hp : ∀ᶠ z in 𝓝 z₀, 0 < f z :=
    hf.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨r, hr, hreg⟩ := Metric.eventually_nhds_iff.mp ((hf.eventually (by simp)).and hp)
  let χ := heatFamilyBump z₀ r hr
  have hs : tsupport χ ⊆ ball z₀ r := by
    calc
      tsupport χ = closedBall z₀ (r / 2) := χ.tsupport_eq
      _ ⊆ ball z₀ r := closedBall_subset_ball (by linarith)
  have hnear (z : HeatRadialFrameSpace) (hz : z ∈ tsupport χ) :
      ContDiffAt ℝ n f z ∧ 0 < f z := hreg (hs hz)
  refine ⟨fun z => χ z * f z + (1 - χ z),
    (heatFamilyCutoff_contDiff n χ f χ.contDiff (fun z hz => (hnear z hz).1)).add
      (contDiff_const.sub χ.contDiff), ?_, ?_⟩
  · intro z
    by_cases hz : χ z = 0
    · simp [hz]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne χ.nonneg (Ne.symm hz))
          (hnear z (subset_tsupport χ hz)).2) (sub_nonneg.mpr χ.le_one)
  · filter_upwards [χ.eventuallyEq_one] with z hz
    simp only [hz, Pi.one_apply, one_mul, sub_self, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Removing the smooth positive density from the actual local H2 solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric Filter
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_weighted_H2_unweight (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ)
    (ht : ∀ y ∈ closedBall (0 : V) 1,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (b : M → ℝ) (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      b ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
        volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ closedBall (0 : V) (1 / 2)) :
    ∃ v : Lp ℂ 2 (volume : Measure V), MemSobolev 2 2 (v : T) ∧
      (v : V → ℂ) =ᵐ[volume] fun y =>
        (χ y * b ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y)) : ℝ) := by
  let ρ : V → ℝ := fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y)
  have hρ (y : V) (hy : y ∈ tsupport χ) : ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y := by
    have hyt : scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
      ht y (closedBall_subset_closedBall (by norm_num) (hs hy))
    apply ContDiffAt.inv
    · exact (chartVolumeDensity_contDiffAt g c _ hyt).comp y (by
        unfold scalarRescaledPoint
        fun_prop)
    · exact (chartVolumeDensity_pos g c _ hyt).ne'
  exact scalar_H2_density_division ρ
    (fun y => b ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) w
    heq hreg χ hχ hc hs hρ (fun y hy =>
      (chartVolumeDensity_pos g c _
        (ht y (closedBall_subset_closedBall (by norm_num) (hs hy)))).ne')

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual unweighted H2 representatives in the original manifold chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric Filter
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_chart_H2_realization (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : 0 < r)
    (ht : ∀ y ∈ closedBall (0 : V) 1,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (b : M → ℝ) (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      b ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
        volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (scalarRescaledPoint g c z₀ r) '' closedBall 0 (1 / 2)) :
    ∃ v : Lp ℂ 2 (volume : Measure V), MemSobolev 2 2 (v : T) ∧
      (v : V → ℂ) =ᵐ[volume] fun z => (χ z * b ((chartAt FourSpace c).symm z) : ℝ) := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let P : V ≃ₜ V := A.toHomeomorph.trans (Homeomorph.addRight z₀.val)
  have hP (y : V) : P y = scalarRescaledPoint g c z₀ r y :=
    scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
  let σ : V → ℝ := χ ∘ P
  have hσ : ContDiff ℝ ∞ σ := hχ.comp (by
    change ContDiff ℝ ∞ (fun y : V => A y + z₀.val)
    fun_prop)
  have hσc : HasCompactSupport σ := hc.comp_homeomorph P
  have hσs : tsupport σ ⊆ closedBall (0 : V) (1 / 2) := by
    intro y hy
    have hp : P y ∈ tsupport χ := tsupport_comp_subset_preimage χ P.continuous hy
    obtain ⟨z, hz, hzy⟩ := hs hp
    have hyz : y = z := P.injective (by simpa only [hP] using hzy.symm)
    exact hyz ▸ hz
  obtain ⟨v, hv2, hv⟩ := scalar_weighted_H2_unweight g c z₀ r ht b w heq hreg σ hσ hσc hσs
  have hva : (v : V → ℂ) =ᵐ[volume]
      fun y => (σ y * b ((chartAt FourSpace c).symm (A y + z₀.val)) : ℝ) := by
    simpa only [A, scalarRescalingLinearEquiv_apply] using hv
  obtain ⟨v', hv'2, hv'⟩ := scalar_H2_unscale A z₀.val
    (fun z => b ((chartAt FourSpace c).symm z)) σ v hv2 hva
  refine ⟨v', hv'2, hv'.trans ?_⟩
  filter_upwards [] with z
  have hinv : P (A.symm (z - z₀.val)) = z := by
    change A (A.symm (z - z₀.val)) + z₀.val = z
    rw [A.apply_symm_apply, sub_add_cancel]
  change (((χ (P (A.symm (z - z₀.val))) * _) : ℝ) : ℂ) = _
  rw [hinv]

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

theorem heatTwoFormConnectionMatrix_partial (B : FourSpace → Mat4) (x : FourSpace)
    (hB : ∀ r s, DifferentiableAt ℝ (fun z => B z r s) x) (i : Fin 4) (k l : Fin 6) :
    partialDeriv (fun z => heatTwoFormConnectionMatrix (B z) k l) i x =
      heatTwoFormConnectionMatrix (matrixPartial B i x) k l := by
  have hd : DifferentiableAt ℝ B x :=
    differentiableAt_pi.mpr (fun r => differentiableAt_pi.mpr (hB r))
  let L : Mat4 →L[ℝ] ℝ := (ContinuousLinearMap.proj l).comp
    ((ContinuousLinearMap.proj k).comp heatConnectionMatrixLinear.toContinuousLinearMap)
  rw [heat_matrixPartial_eq_fderiv B x hB i]
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector i))
    (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

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

/-! The time derivative and exact cutoff residual of the actual normal
bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalBundleParametrix_time_differentiable {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (k l : Fin 6) : DifferentiableAt ℝ (fun s => heatNormalBundleParametrix E s x k l) t := by
  exact ((fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t x)).differentiableAt

theorem heatNormalCutoffParametrix_residual_identity {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (hχ : ContDiffAt ℝ 2 χ x) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (ha : ∀ i j, a i j = a j i) (k l : Fin 6) :
    deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
      fourHeatBundleOperator a b B C
        (fun y q => heatNormalCutoffParametrix E χ t y q l) x k =
    χ x * (deriv (fun s => heatNormalBundleParametrix E s x k l) t +
      fourHeatBundleOperator a b B C
        (fun y q => heatNormalBundleParametrix E t y q l) x k) +
      fourHeatLocalOperator a b 0 χ x * heatNormalBundleParametrix E t x k l -
      2 * (∑ i, ∑ j, a i j * partialDeriv χ i x *
        partialDeriv (fun y => heatNormalBundleParametrix E t y k l) j x) +
      ∑ i, ∑ q, B i k q * partialDeriv χ i x * heatNormalBundleParametrix E t x q l := by
  have hd := (heatNormalBundleParametrix_time_differentiable E t ht x k l).hasDerivAt.const_mul
    (χ x)
  change HasDerivAt (fun s => heatNormalCutoffParametrix E χ s x k l) _ t at hd
  rw [hd.deriv]
  unfold heatNormalCutoffParametrix
  rw [fourHeatBundleOperator_cutoff a b B C χ _ x ha hχ
    (fun q => (heatNormalBundleParametrix_space_regular E t q l).contDiffAt) k]
  ring

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heat_actual_potential_signed_trace (e : FrameBundle g) :
    (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace = 0 := by
  let R := twoFormMetricCurvatureTensor g e
  have hf (i j k l : Fin 4) : R ![j,i,k,l] = -R ![i,j,k,l] :=
    twoFormMetricCurvatureTensor_skew g e i j k l
  have hp (i j k l : Fin 4) : R ![k,l,i,j] = R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l
  have hb (i j k l : Fin 4) : R ![i,j,k,l] + R ![j,k,i,l] + R ![k,i,j,l] = 0 := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_firstBianchi e.frame i j k l
  change (twoFormHodgeMatrix * twoFormPotentialMatrix R).trace = 0
  rw [twoFormPotentialMatrix, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    twoFormHodgeMatrix_trace, twoFormCurvatureMatrix_signed_trace R hf hp hb]
  ring

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

theorem heat_partial_second_finite_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (x : FourSpace)
    (hF : ∀ k, ContDiffAt ℝ 2 (F k) x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => ∑ k, F k y) i) j x =
      ∑ k, partialDeriv (partialDeriv (F k) i) j x := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ k, DifferentiableAt ℝ (F k) y := by
    apply eventually_all.mpr
    intro k
    filter_upwards [(hF k).eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have he : partialDeriv (fun y => ∑ k, F k y) i =ᶠ[𝓝 x]
      (fun y => ∑ k, partialDeriv (F k) i y) := by
    filter_upwards [hn] with y hy
    exact heat_partial_finite_sum F y hy i
  rw [fourHeat_partial_germ he j]
  apply heat_partial_finite_sum
  intro k
  exact (((hF k).fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero

theorem heat_trace_product_second_zero (H : HeatMat6) (A B : FourSpace → HeatMat6)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun x => (H * A x * B x).trace) i) j 0 =
      (H * (heatSixPartial A i 0 * heatSixPartial B j 0 +
        heatSixPartial A j 0 * heatSixPartial B i 0)).trace := by
  have heq : (fun x => (H * A x * B x).trace) =
      (fun x => ∑ k, ∑ l, ∑ q, H k l * (A x l q * B x q k)) := by
    funext x
    calc
      (H * A x * B x).trace = (H * (A x * B x)).trace :=
        congrArg Matrix.trace (Matrix.mul_assoc H (A x) (B x))
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  have hreg (k l q : Fin 6) : ContDiffAt ℝ 2
      (fun x => H k l * (A x l q * B x q k)) 0 :=
    contDiffAt_const.mul ((hA l q).mul (hB q k))
  rw [heq, heat_partial_second_finite_sum _ 0
    (fun k => ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun q _ => hreg k l q))) i j]
  simp_rw [heat_partial_second_finite_sum _ 0
    (fun l => ContDiffAt.sum (fun q _ => hreg _ l q)) i j]
  simp_rw [heat_partial_second_finite_sum _ 0 (fun q => hreg _ _ q) i j]
  simp_rw [fourHeat_second_const_mul]
  have hp (k l q : Fin 6) :
      partialDeriv (partialDeriv (fun x => A x l q * B x q k) i) j 0 =
        partialDeriv (fun x => A x l q) i 0 * partialDeriv (fun x => B x q k) j 0 +
        partialDeriv (fun x => A x l q) j 0 * partialDeriv (fun x => B x q k) i 0 := by
    rw [scalar_partial_second_product_at _ _ 0 (hA l q) (hB q k) i j]
    simp only [hA0, hB0, Matrix.zero_apply, mul_zero, zero_mul, zero_add, add_zero]
  simp_rw [hp]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, heatSixPartial,
    Matrix.add_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib]

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

theorem heatSignedTrace_second (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun y => A y k l) x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i) j x =
      (twoFormHodgeMatrix * heatSixPartial (heatSixPartial A i) j x).trace := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ k l, DifferentiableAt ℝ (fun z => A z k l) y :=
    eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      ((hA k l).eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))))
  have he : partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i =ᶠ[𝓝 x]
      (fun y => (twoFormHodgeMatrix * heatSixPartial A i y).trace) :=
    hn.mono (fun y hy => heatSignedTrace_partial A y hy i)
  rw [fourHeat_partial_germ he j]
  apply heatSignedTrace_partial
  intro k l
  exact (((hA k l).fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth harmonic two-forms are preserved by Hodge star,
with finite positive and negative summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar cutoff commutator has one bound over a compact frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

def heatFamilyScalarCommutator (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  fourHeatScaledCommutator (fun x => E.a (x, z.2)) (fun x => E.b (x, z.2))
    (fun _ => 0) χ (fun m x _ => E.scalarAmplitude m (x, z.2)) t z.1 0

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported tests only require continuity on the normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_initial_local {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    {D : HeatNormalFrameData g o c e} (E : HeatNormalBundleExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (k l : Fin 6) :
    Tendsto (fun t => ∫ x, heatNormalCutoffParametrix E χ t x k l * f x)
      (𝓝[Ioi 0] 0) (𝓝 ((if k = l then 1 else 0) * f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => (χ x * f x) * E.amplitude m x k l
  have hu (m : Fin 4) : Continuous (u m) :=
    hχf.mul (E.amplitude_regular m (by omega) k l).continuous
  have huc (m : Fin 4) : HasCompactSupport (u m) := (hχc.mul_right).mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image
      continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hzero : u 0 0 = (if k = l then 1 else 0) * f 0 := by
    change (χ 0 * f 0) * E.amplitude 0 0 k l = _
    rw [hχ0, E.amplitude_zero, hU]
    simp only [one_smul, Matrix.one_apply, one_mul]
    ring
  rw [hzero] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [heatNormalCutoffParametrix, heatNormalBundleParametrix,
        fourHeatBundlePolynomial, fourHeatPolynomial, u]
      ring

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
omit [PreconnectedSpace M] in
theorem weylRoot_weighted_moment (hRic : RicciThree g) (ε : ℝ) (k n : ℕ) :
    (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ k *
      (canonicalParallelMetricData g o hRic).toMetricGreenData.weylRootField ε e ^ n
      ∂canonicalFrameMeasure g o) =
    ∫ x, plusNorm o x ^ k * (plusNorm o x ^ 2 + ε ^ 2) ^ ((n : ℝ) / 6)
      ∂normalizedVolume g := by
  let f : M → ℝ := fun x => plusNorm o x ^ k *
    (plusNorm o x ^ 2 + ε ^ 2) ^ ((n : ℝ) / 6)
  calc
    _ = ∫ e : FrameBundle g, f e.base ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      change normalizedBlockNorm _ ^ k * regularizedWeylRoot ε _ ^ n = _
      rw [regularizedWeylRoot_eq, ← actual_plusNorm_frame o e he,
        ← Real.rpow_mul_natCast (by positivity)]
      dsimp only [f]
      congr 2
      ring
    _ = _ := canonicalFrameMeasure_integral_base g o _ (by
      have hc : Continuous f := ((continuous_plusNorm g o).pow k).mul
        ((((continuous_plusNorm g o).pow 2).add continuous_const).rpow_const
          (fun _ => Or.inr (by positivity)))
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

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

/-! Orthogonal harmonic projection and smooth Poisson decomposition of
actual two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothHarmonicL2 : Submodule ℝ (SmoothL2TwoForm o) where
  carrier := {u | (u : smoothTwoForms o) ∈ smoothHarmonicTwoForms}
  zero_mem' := (smoothHarmonicTwoForms (o := o)).zero_mem
  add_mem' hu hv := (smoothHarmonicTwoForms (o := o)).add_mem hu hv
  smul_mem' r _ hu := (smoothHarmonicTwoForms (o := o)).smul_mem r hu

def smoothHarmonicL2ToHarmonic :
    smoothHarmonicL2 (o := o) →ₗ[ℝ] smoothHarmonicTwoForms (o := o) where
  toFun u := ⟨u.val, u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothHarmonicL2ToHarmonic_injective :
    Function.Injective (smoothHarmonicL2ToHarmonic (o := o)) := by
  intro u v h
  exact Subtype.ext (congrArg Subtype.val h)

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms
local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def smoothHarmonicToClosed :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] smoothClosedTwoForms (o := o) where
  toFun u := ⟨u.val, u.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def smoothHarmonicToDeRham :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] TwoFormDeRhamCohomology (o := o) :=
  (smoothExactTwoForms (o := o)).mkQ.comp smoothHarmonicToClosed

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

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_2 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact/coexact differential identities underlying cancellation of
the nonzero two-form spectrum in the signed trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormDDelta_add (u v : smoothTwoForms o) :
    smoothTwoFormDDelta (u + v) = smoothTwoFormDDelta u + smoothTwoFormDDelta v :=
  smoothTwoFormDDeltaLinear.map_add u v

theorem smoothTwoFormDDelta_smul (r : ℝ) (u : smoothTwoForms o) :
    smoothTwoFormDDelta (r • u) = r • smoothTwoFormDDelta u :=
  smoothTwoFormDDeltaLinear.map_smul r u

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

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_4_re05e1d_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms_1 : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

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

local instance hodgeIndexZeroAddGroup_re05e1d_1 : AddCommGroup (ZeroFormDeRhamCohomology g) :=
  Submodule.addCommGroup _
local instance hodgeIndexClosedAddGroup : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

def hodgeComplexEuler (g : SmoothMetric M) (o : FrameOrientation g) : ℤ :=
  (Module.finrank ℝ (ZeroFormDeRhamCohomology g) : ℤ) -
    (Module.finrank ℝ (OneFormDeRhamCohomology (o := o)) : ℤ) +
    (Module.finrank ℝ (TwoFormDeRhamCohomology (o := o)) : ℤ) -
    (Module.finrank ℝ (HodgeDualOneCohomology (o := o)) : ℤ) +
    (Module.finrank ℝ (DivergenceCokernel g) : ℤ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form reconstruction is contractive in the continuous norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_19
theorem oneFormFromFrameL2_norm_le (F : Lp FourSpace 2 (canonicalFrameMeasure g o)) :
    ‖oneFormFromFrameL2 F‖ ≤ ‖F‖ := by
  let w := oneFormFromFrameL2 F
  have hi := abs_real_inner_le_norm F (oneFormFrameL2 w)
  rw [oneFormFrameL2_norm] at hi
  have he : ‖w‖ ^ 2 = inner ℝ F (oneFormFrameL2 w) := by
    rw [← real_inner_self_eq_norm_sq]
    exact oneFormFromFrameL2_pairing F w
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ ‖F‖
    rw [hw]
    exact norm_nonneg _
  · have hp := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    change ‖w‖ ≤ ‖F‖
    nlinarith [le_abs_self (inner ℝ F (oneFormFrameL2 w))]

theorem oneFormFromContinuous_norm_le (F : C(FrameBundle g, FourSpace)) :
    ‖oneFormFromContinuous (o := o) F‖ ≤ ‖F‖ := by
  apply (oneFormFromFrameL2_norm_le _).trans
  have hnorm : ‖(ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ :
      C(FrameBundle g, FourSpace) →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o))‖ ≤ 1 := by
    simpa [measureUnivNNReal] using
      ContinuousMap.toLp_norm_le (𝕜 := ℝ) (E := FourSpace) (p := 2) (canonicalFrameMeasure g o)
  exact (ContinuousLinearMap.le_opNorm _ F).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg F)).trans_eq (one_mul _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform fiber bounds give actual global one-form L2 bounds. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
  {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

local instance instCompactSpaceFrameBundle_21_re05e1d_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
theorem heatNormalOneAmplitudeL2_norm_le
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖a x‖ ≤ B) :
    ‖heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs‖ ≤ B := by
  apply (oneFormFromContinuous_norm_le _).trans
  apply (ContinuousMap.norm_le _ hB).mpr
  intro f
  by_cases hf : f.base ∈ C.target
  · have heq := heatNormalOneAmplitude_norm_sq C hE hCt hP hD a ha hc hs f hf
    have hba := hb (C.symm f.base)
    nlinarith [norm_nonneg (a (C.symm f.base)),
      norm_nonneg (heatNormalOneAmplitude D C hCt hP hD a ha hc hs f)]
  · have hz : heatNormalOneAmplitude D C hCt hP hD a ha hc hs f = 0 := by
      change WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) = _
      simp only [heatNormalOneFrameLift, ite_eq_right hf]
      rfl
    rw [hz, norm_zero]
    exact hB

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

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_5 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

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

theorem heatNormalPolynomialColumn_weight_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) (l : Fin 6) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn E χ t l x‖ ^ 2 ≤ B := by
  let W := fun z : ℝ × FourSpace => frameExponentialJacobian g o e z.2 *
    ‖heatNormalPolynomialColumn E χ z.1 l z.2‖ ^ 2
  have hW : Continuous W := ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul
    ((heatNormalPolynomialColumn_continuous E χ hχ l).norm.pow 2)
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod hc).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hb ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hzero : heatNormalPolynomialColumn E χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! At the radial center, derivatives of the scalar metric weights do
not contribute to the quadratic connection trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_trace_product_partial_zero (H : HeatMat6) (A B : FourSpace → HeatMat6)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i : Fin 4) :
    partialDeriv (fun x => (H * A x * B x).trace) i 0 = 0 := by
  have hreg (k l q : Fin 6) : ContDiffAt ℝ 2
      (fun x => H k l * (A x l q * B x q k)) 0 :=
    contDiffAt_const.mul ((hA l q).mul (hB q k))
  simp_rw [heat_trace_product_expansion]
  rw [heat_partial_finite_sum _ 0 (fun k =>
    (ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun q _ => hreg k l q))).differentiableAt
      (by norm_num)) i]
  simp_rw [heat_partial_finite_sum _ 0 (fun l =>
    (ContDiffAt.sum (fun q _ => hreg _ l q)).differentiableAt (by norm_num)) i]
  simp_rw [heat_partial_finite_sum _ 0 (fun q => (hreg _ _ q).differentiableAt (by norm_num)) i]
  simp_rw [fourHeat_partial_const_mul]
  have hp (k l q : Fin 6) : partialDeriv (fun x => A x l q * B x q k) i 0 = 0 := by
    rw [scalar_partial_product _ _ 0 ((hA l q).differentiableAt (by norm_num))
      ((hB q k).differentiableAt (by norm_num)) i]
    simp only [hA0, hB0, Matrix.zero_apply, mul_zero, zero_mul, add_zero]
  simp only [hp, mul_zero, Finset.sum_const_zero]

theorem heat_weighted_trace_second_zero (H : HeatMat6) (a : FourSpace → ℝ)
    (A B : FourSpace → HeatMat6) (ha : ContDiffAt ℝ 2 a 0)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun x => a x * (H * A x * B x).trace) i) j 0 =
      a 0 * (H * (heatSixPartial A i 0 * heatSixPartial B j 0 +
        heatSixPartial A j 0 * heatSixPartial B i 0)).trace := by
  rw [scalar_partial_second_product_at a _ 0 ha (heat_trace_product_regular H A B hA hB) i j,
    heat_trace_product_partial_zero H A B hA hB hA0 hB0,
    heat_trace_product_partial_zero H A B hA hB hA0 hB0,
    heat_trace_product_second_zero H A B hA hB hA0 hB0]
  simp only [hA0, hB0, Matrix.trace_zero, mul_zero, add_zero, zero_add]

theorem heat_weighted_trace_partial_zero (H : HeatMat6) (a : FourSpace → ℝ)
    (A B : FourSpace → HeatMat6) (ha : ContDiffAt ℝ 2 a 0)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i : Fin 4) :
    partialDeriv (fun x => a x * (H * A x * B x).trace) i 0 = 0 := by
  rw [scalar_partial_product a _ 0 (ha.differentiableAt (by norm_num))
    ((heat_trace_product_regular H A B hA hB).differentiableAt (by norm_num)) i,
    heat_trace_product_partial_zero H A B hA hB hA0 hB0]
  simp only [hA0, hB0, Matrix.trace_zero, mul_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gaussian concentration gives the weighted square-integral growth t⁻². -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffColumn_square_integral_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (l : Fin 6) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x * ‖heatNormalCutoffColumn E χ t l x‖ ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hb⟩ := heatNormalPolynomialColumn_weight_bound E χ hχ.continuous hc l
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro t ht
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn E χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn E χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn E χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalCutoffColumn_regular E χ hχ t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn E χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
    _ = _ := by
      rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]
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

theorem heatFamilyPolynomial_weight_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      (E.U (x, q) ^ 2)⁻¹ * ‖heatFamilyPolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
  have hb (l : Fin 6) : ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      (E.U (x, q) ^ 2)⁻¹ * ‖heatFamilyPolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
    let W := fun z : ℝ × HeatRadialFrameSpace => (E.U z.2 ^ 2)⁻¹ *
      ‖heatFamilyPolynomialColumn E χ z.1 l z.2‖ ^ 2
    have hW : Continuous W :=
      (((E.U_regular.continuous.comp continuous_snd).pow 2).inv₀
        (fun z => pow_ne_zero 2 (E.U_pos z.2).ne')).mul
        ((heatFamilyPolynomialColumn_continuous E χ hχ l).norm.pow 2)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hW.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro q hq t ht x
    by_cases hx : x ∈ tsupport χ
    · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
    · have hz : heatFamilyPolynomialColumn E χ t l (x, q) = 0 := by
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}


theorem heatUniformPolynomial_weight_bound (E : HeatFamilySmoothCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn N.extension χ t l x‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := heatFamilyPolynomial_weight_bound E χ hχ hc K hK
  refine ⟨B, hB, ?_⟩
  intro e N hq t ht x l
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.metric_pos x (hχs hx)))
    rw [← (N.actual x (hχs hx)).2.2.2.2, N.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh, N.polynomialColumn_family]
    exact hb _ hq t ht x l
  · have hz : heatNormalPolynomialColumn N.extension χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed Hessian of the actual first heat amplitude at the center.
Only the curvature-square contribution survives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_partial_second_germ {f h : FourSpace → ℝ} {x : FourSpace}
    (he : f =ᶠ[𝓝 x] h) (i j : Fin 4) :
    partialDeriv (partialDeriv f i) j x = partialDeriv (partialDeriv h i) j x := by
  have hp : partialDeriv f i =ᶠ[𝓝 x] partialDeriv h i :=
    he.eventuallyEq_nhds.mono (fun _ h => fourHeat_partial_germ h i)
  exact fourHeat_partial_germ hp j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed second transport coefficient is the actual signature
curvature polynomial. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatMatrixScalarOperator_signed_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun y => A y k l) x) :
    (twoFormHodgeMatrix * heatMatrixScalarOperator a b A x).trace =
      fourHeatLocalOperator a b 0 (fun y => (twoFormHodgeMatrix * A y).trace) x := by
  have hm : heatMatrixScalarOperator a b A x =
      -(∑ i, ∑ j, a i j • heatSixPartial (heatSixPartial A i) j x) +
        ∑ i, b i • heatSixPartial A i x := by
    ext k l
    simp only [heatMatrixScalarOperator, fourHeatLocalOperator, Matrix.add_apply,
      Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, heatSixPartial,
      smul_eq_mul, zero_mul, add_zero]
  rw [hm]
  change heatSignedTraceLinear (-(∑ i, ∑ j, a i j • heatSixPartial (heatSixPartial A i) j x) +
    ∑ i, b i • heatSixPartial A i x) = _
  simp only [map_add, map_neg, map_sum, map_smul, smul_eq_mul]
  have hp (i : Fin 4) : heatSignedTraceLinear (heatSixPartial A i x) =
      partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i x :=
    (heatSignedTrace_partial A x (fun k l => (hA k l).differentiableAt (by norm_num)) i).symm
  have hpp (i j : Fin 4) : heatSignedTraceLinear (heatSixPartial (heatSixPartial A i) j x) =
      partialDeriv (partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i) j x :=
    (heatSignedTrace_second A x hA i j).symm
  simp only [hp, hpp, fourHeatLocalOperator, zero_mul, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed normal-parametrix Gaussian integral has the
signature curvature density as its limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalMatrixPolynomial_signed (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) :
    frameExponentialJacobian g o e x * χ x ^ 2 *
        heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x) =
      2 * t * E.signedFirst χ x + t ^ 2 * E.signedTail χ t x := by
  rw [heatNormalMatrixPolynomial, E.amplitude_zero, heatSignedGram_polynomial]
  unfold HeatNormalBundleExtension.signedFirst HeatNormalBundleExtension.signedTail
  ring

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

/-! The first Euler coefficient is a jointly C2 family with a uniform
quadratic zero at each actual normal center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem heatUniformEulerFirst_quadratic (F : HeatFamilyOneCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hχs : tsupport χ ⊆ ball 0 r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (_N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ x,
      ‖heatFamilyEulerFirst F χ (x, frameCoordinateState g c e)‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := heatFamily_quadratic_bound (heatFamilyEulerFirst F χ)
    (heatFamilyEulerFirst_regular F χ hχ) r K hK
  refine ⟨C, hC, ?_⟩
  intro e N hq x
  have hz := N.eulerFirst_zero_near hRic χ
  by_cases hx : x ∈ closedBall (0 : FourSpace) r
  · apply hb _ hq hz.self_of_nhds _ x hx
    rw [hz.fderiv_eq]
    exact fderiv_const_apply _
  · have hxs : x ∉ tsupport χ := fun hs => hx (ball_subset_closedBall (hχs hs))
    have hzero := image_eq_zero_of_notMem_tsupport hxs
    simp only [heatFamilyEulerFirst, hzero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, zero_mul, norm_zero]
    positivity

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

theorem heatNormalScalarLift_joint_continuous {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : OpenPartialHomeomorph FourSpace X) (A : ℝ → FourSpace → ℝ)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hs : ∀ t > 0, tsupport (A t) ⊆ K) :
    ContinuousOn (fun z : ℝ × X => heatNormalScalarLift C (A z.1) z.2) (Ioi 0 ×ˢ univ) := by
  have hCK := hK.image_of_continuousOn (C.continuousOn.mono hKC)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  by_cases hx : z.2 ∈ C.target
  · have hi : ContinuousAt (fun w : ℝ × X => C.symm w.2) z :=
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hx)).comp continuousAt_snd
    have hv : ContinuousAt (fun w : ℝ × X => A w.1 (C.symm w.2)) z :=
      (hA.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds
        ⟨hz.1, C.map_target hx⟩)).comp (continuousAt_fst.prodMk hi)
    apply hv.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (C.open_target.mem_nhds hx)] with w hw
    exact heatNormalScalarLift_on_target C _ hw
  · have hn : z.2 ∉ C '' K := by
      rintro ⟨x, hxK, hxe⟩
      exact hx (hxe ▸ C.map_source (hKC hxK))
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (hCK.isClosed.isOpen_compl.mem_nhds hn),
      continuousAt_fst.eventually (Ioi_mem_nhds hz.1)] with w hw hwt
    apply not_ne_iff.mp
    intro hne
    obtain ⟨x, hxA, hxe⟩ := heatNormalScalarLift_support C (A w.1) hne
    exact hw ⟨x, hs w.1 hwt hxA, hxe⟩

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}


theorem heatUniformOnePolynomial_weight_bound (E : HeatFamilyOneCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn N.one χ t l x‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := heatFamilyOnePolynomial_weight_bound E χ hχ hc K hK
  refine ⟨B, hB, ?_⟩
  intro e N hq t ht x l
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.normal.metric_pos x (hχs hx)))
    rw [← (N.normal.actual x (hχs hx)).2.2.2.2, N.normal.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh, N.onePolynomialColumn_family]
    exact hb _ hq t ht x l
  · have hz : heatNormalOnePolynomialColumn N.one χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal columns have a common L2 growth constant
for every initial frame in a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformOneColumn_growth (E : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖(N.normal.parametrixData hr).oneNormalizedColumn N.one t l‖ ≤ C / t := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformOnePolynomial_weight_bound (g := g) (o := o) (c := c) E r χ
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport hχs K hK
  let A := B / (64 * Real.pi ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := (normalizedChartFactor g).toReal * A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * (C + 1), by positivity, ?_⟩
  intro e N hq t ht l
  let P := N.normal.parametrixData hr
  have hcut : P.cutoff = χ := rfl
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalOneCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn N.one χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb e N hq t ⟨ht.1.le, ht.2⟩ x l) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalOneCutoffColumn_regular N.one χ
        (heatNormalChartBump r hr).contDiff t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  have hint : (∫ x, frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn N.one χ t l x‖ ^ 2) ≤ A / t ^ 2 := by
    calc
      _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
      _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; dsimp [A]; ring
  have hn := heatNormalOneAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalOneCutoffColumn N.one P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular N.one P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support N.one P.cutoff t l))
    ((heatNormalOneCutoffColumn_support N.one P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.oneColumn N.one t l‖ ^ 2 ≤ C / t ^ 2 := by
    have hint' : (∫ x, frameExponentialJacobian g o e x *
        ‖heatNormalOneCutoffColumn N.one P.cutoff t l x‖ ^ 2) ≤ A / t ^ 2 := by
      simpa only [hcut] using hint
    exact (le_of_eq hn).trans ((mul_le_mul_of_nonneg_left hint' (by positivity)).trans_eq (by dsimp [C]; ring))
  have hs : (‖P.oneColumn N.one t l‖ * t) ^ 2 ≤ C := by
    calc
      _ = ‖P.oneColumn N.one t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (C / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = C := by field_simp [ht.1.ne']
  have hcol : ‖P.oneColumn N.one t l‖ ≤ (C + 1) / t := by
    apply (le_div_iff₀ ht.1).mpr
    nlinarith [sq_nonneg C, norm_nonneg (P.oneColumn N.one t l)]
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn N.one t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hcol (norm_nonneg _)).trans_eq (by ring)

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

local instance unitFormHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature eigenvalue of an actual parallel two-form. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem parallel_twoForm_secondDerivative_zero (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) : twoFormFramedSecondDerivative o u.val e = 0 := by
  ext a
  let i := a 0
  let b : Fin 3 → Fin 4 := fun j => a j.succ
  have ha : Fin.cons i b = a := by
    ext j
    fin_cases j <;> rfl
  have hd := u.property.framedCovariant_parallel_derivative
    (fun t => parallelFrameFlowMap g i t e) 0 i
    (parallelFrameFlowMap_curve_continuous g i e).continuousAt
    (parallelFrameFlowMap_primitive g i e 0) b
  have hf : (fun t => twoFormFramedCovariantDerivative o u.val
      (parallelFrameFlowMap g i t e) b) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rw [hz]
    rfl
  rw [hf, parallelFrameFlowMap_zero, ha] at hd
  exact hd.unique (hasDerivAt_const 0 (0 : ℝ))

theorem parallel_twoForm_roughTrace_zero (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) : twoFormFramedRoughTrace o u.val e = 0 := by
  unfold twoFormFramedRoughTrace
  rw [parallel_twoForm_secondDerivative_zero u hz e]
  simp only [Pi.zero_apply, Finset.sum_const_zero]
  rfl

omit [T3Space M] [CompactSpace M] in
theorem parallel_twoForm_harmonic (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0) :
    u ∈ smoothHarmonicTwoForms := by
  apply (mem_smoothHarmonicTwoForms u).mpr
  constructor
  · intro e i j k
    change twoFormExteriorComponent
      (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) i j k = 0
    rw [hz]
    simp only [Pi.zero_apply, twoFormExteriorComponent, sub_self, add_zero]
  · intro e k
    change twoFormCodiffComponent
      (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) k = 0
    rw [hz]
    simp only [Pi.zero_apply, twoFormCodiffComponent, Finset.sum_const_zero, neg_zero]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


