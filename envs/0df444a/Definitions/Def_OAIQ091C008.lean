-- Prove2me | Definitions.Def_OAIQ091C008
-- name    : OAIQ091C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:53:19.408216+00:00
-- url     : https://prove2.me/theorems/9f545ad5-0801-48fe-b578-9273ef19b652
-- title:
--   Definitions bundle OAIQ091C008 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 366 declarations of OpenAI's Lean: 85 definitions, 1 inductive type or structure, 5 instances and 275 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.CotangentCoordinates`, `OAI.PositiveEinsteinFour.Geometry.DerdzinskiHitchinInput`, `OAI.PositiveEinsteinFour.Geometry.DirectionInvariant`, `OAI.PositiveEinsteinFour.Geometry.FinitePositiveVolume`, `OAI.PositiveEinsteinFour.Geometry.FrameOrientation.frame`, `OAI.PositiveEinsteinFour.Geometry.GurskyLeBrunSectionalInput`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.changeMatrix`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.reflect`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.ricci`, `OAI.PositiveEinsteinFour.Geometry.RicciThree`, `OAI.PositiveEinsteinFour.Geometry.blockCoordinates`, `OAI.PositiveEinsteinFour.Geometry.blockCoordinatesLinear`, `OAI.PositiveEinsteinFour.Geometry.bundleCurvatureDerivative`, `OAI.PositiveEinsteinFour.Geometry.canonicalFrame`, `OAI.PositiveEinsteinFour.Geometry.chartInverseMatrix`, `OAI.PositiveEinsteinFour.Geometry.chartVolumeDensity`, `OAI.PositiveEinsteinFour.Geometry.connectionMatrix`, `OAI.PositiveEinsteinFour.Geometry.coordinateCovariantCurvatureDerivative`, `OAI.PositiveEinsteinFour.Geometry.coordinateCurvatureMatrix`, `OAI.PositiveEinsteinFour.Geometry.cotangentBasis`, `OAI.PositiveEinsteinFour.Geometry.cotangentHamiltonianField`, `OAI.PositiveEinsteinFour.Geometry.covariantSlotAction`, `OAI.PositiveEinsteinFour.Geometry.curvatureArray`, `OAI.PositiveEinsteinFour.Geometry.curvatureCoordinates`, `OAI.PositiveEinsteinFour.Geometry.curvatureDerivativeArray`, `OAI.PositiveEinsteinFour.Geometry.curvatureEndomorphism`, `OAI.PositiveEinsteinFour.Geometry.curvatureFirstLinear`, `OAI.PositiveEinsteinFour.Geometry.curvatureHessianArray`, `OAI.PositiveEinsteinFour.Geometry.curvaturePairing`, `OAI.PositiveEinsteinFour.Geometry.directionFrameMatrix`, `OAI.PositiveEinsteinFour.Geometry.firstDirection`, `OAI.PositiveEinsteinFour.Geometry.fiveTensorMatrix`, `OAI.PositiveEinsteinFour.Geometry.frameAt`, `OAI.PositiveEinsteinFour.Geometry.frameCotangentMomentum`, `OAI.PositiveEinsteinFour.Geometry.frameCurvature`, `OAI.PositiveEinsteinFour.Geometry.frameReflection`, `OAI.PositiveEinsteinFour.Geometry.frameReflectionMatrix`, `OAI.PositiveEinsteinFour.Geometry.frameVariation`, `OAI.PositiveEinsteinFour.Geometry.gradientBlock`, `OAI.PositiveEinsteinFour.Geometry.gradientDivergence` and 46 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_ActualRicciContraction`, `EinsteinFour_ChartMetricNondegeneracy`, `EinsteinFour_ChartMetricSmoothness`, `EinsteinFour_ChartMetricTransition`, `EinsteinFour_ChartVolumeDensity`, `EinsteinFour_ConnectionPullback`, `EinsteinFour_CoordinateChangeCalculus`, `EinsteinFour_CoordinateConnectionUniqueness`, `EinsteinFour_CoordinateMetricCompatibility`, `EinsteinFour_CoordinateSecondBianchi`, `EinsteinFour_CotangentHamiltonian`, `EinsteinFour_CotangentJacobian`, `EinsteinFour_CotangentKineticEnergy`, `EinsteinFour_CurvatureCoordinateSmoothness`, `EinsteinFour_CurvatureFirstBianchi`, `EinsteinFour_CurvatureMetricSkew`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_FrameAverages`, `EinsteinFour_FrameBundle`, `EinsteinFour_FrameCurvature`, `EinsteinFour_FrameCurvatureMetricSkew`, `EinsteinFour_FrameOrientation`, `EinsteinFour_FrameOrientationContinuity`, `EinsteinFour_FrameRotation`, `EinsteinFour_HighestCoordinates`, `EinsteinFour_MetricBianchi`, `EinsteinFour_MetricContractionCalculus`, `EinsteinFour_MetricDistance`, `EinsteinFour_MetricInverseCalculus`, `EinsteinFour_MetricTensorCompatibility`, `EinsteinFour_ModelIdentification`, `EinsteinFour_OrthonormalFrame`, `EinsteinFour_QuaternionGenerators`, `EinsteinFour_RiemannianVolume`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_WeightedConnectionCurvature`, `EinsteinFour_WeylDerivative`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylGeometry`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C000` and `OAIQ091C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C013`, `OAIQ091C014` and `OAIQ091C015`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C000
import Definitions.Def_OAIQ091C001

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace OrthonormalFrame

variable {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)

/-- Pullback of the actual chart Ricci tensor. -/
def ricci : Mat4 := e.matrixᵀ * chartRicci g c * e.matrix

/-- Normalization of Ricci transfers to every orthonormal frame. -/
theorem ricci_eq_three_one
    (hRic : chartRicci g c = (3 : ℝ) • chartMetric g c) :
    e.ricci = (3 : ℝ) • (1 : Mat4) := by
  unfold ricci
  rw [hRic, mul_smul_comm, smul_mul_assoc, e.orthonormal]

end OrthonormalFrame

/-- The Riemann tensor evaluated on an actual orthonormal frame. Its slots
are `<R(e_i,e_j)e_k,e_l>`, matching `sectionalNumerator`. -/
def frameCurvature (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i j k l : Fin 4) : ℝ :=
  ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
    chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r *
      e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l

/-- Curvature as a bilinear form on two-form coordinates. -/
def curvaturePairing (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (p q : Fin 4 × Fin 4) : ℝ := frameCurvature g c e p.1 p.2 q.2 q.1

/-- The self-dual Weyl block in the normalized Ricci=3g convention. -/
def plusWeyl (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) : Mat3 :=
  curvatureBlock (curvaturePairing g c e) TraceHessian.quaternionMatrix - 1

/-- The anti-self-dual Weyl block in the same concrete frame. -/
def minusWeyl (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) : Mat3 :=
  curvatureBlock (curvaturePairing g c e) oppositeQuaternion - 1

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OrthonormalFrame
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of the concrete orthonormal frames used for the curvature
blocks. This is obtained from the actual positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff MatrixOrder

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartMetric_apply (g : SmoothMetric M) (c : M) (i j : Fin 4) :
    chartMetric g c i j = g.inner c (coordinateVector i) (coordinateVector j) := by
  have hd : mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c c) =
      ContinuousLinearMap.id ℝ FourSpace := by
    simpa [I4, extChartAt_coe_symm, extChartAt_coe, mfderivWithin_univ] using!
      (mfderivWithin_range_extChartAt_symm (I := I4) (x := c))
  simp only [chartMetric, metricInChart, hd]
  change g.inner ((chartAt FourSpace c).symm (chartAt FourSpace c c))
    (coordinateVector i) (coordinateVector j) = _
  rw [(chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)]

theorem sum_coordinateVector (u : Fin 4 → ℝ) :
    (∑ i, u i • coordinateVector i) = WithLp.toLp 2 u := by
  ext j
  simp [coordinateVector, Pi.single_apply]

theorem chartMetric_pairing (g : SmoothMetric M) (c : M) (u v : Fin 4 → ℝ) :
    u ⬝ᵥ (chartMetric g c *ᵥ v) =
      g.inner c (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [← sum_coordinateVector u, ← sum_coordinateVector v]
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner c
  change u ⬝ᵥ (chartMetric g c *ᵥ v) = B _ _
  have hB : B (∑ i, u i • coordinateVector i) (∑ j, v j • coordinateVector j) =
      ∑ i, ∑ j, u i * (v j * B (coordinateVector i) (coordinateVector j)) := by
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hB]
  simp only [dotProduct, mulVec, Finset.mul_sum, chartMetric_apply, B]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem chartMetric_posDef (g : SmoothMetric M) (c : M) :
    (chartMetric g c).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa [Matrix.conjTranspose_apply, chartMetric_apply] using
      g.symm c (coordinateVector j) (coordinateVector i)
  · intro u hu
    simp only [star_trivial]
    rw [chartMetric_pairing]
    apply g.pos
    intro hz
    apply hu
    exact (WithLp.toLp_injective 2) hz

/-- A fixed, canonical choice from the positive square root of the inverse
metric. No choice of curvature eigenvectors is needed for this frame. -/
def canonicalFrame (g : SmoothMetric M) (c : M) : OrthonormalFrame g c where
  matrix := Jacobi.scalarNormalizer (chartMetric g c)
  orthonormal := by
    have hsym := (Jacobi.scalarNormalizer_posSemidef (chartMetric g c)).isHermitian
    have ht : (Jacobi.scalarNormalizer (chartMetric g c))ᵀ =
        Jacobi.scalarNormalizer (chartMetric g c) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsym.eq
    rw [ht]
    exact Jacobi.scalarNormalizer_normalizes (chartMetric_posDef g c)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualRicciContraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction of the actual chart curvature in an orthonormal frame.
This is a finite change-of-basis calculation, used to discharge the Ricci
positivity needed by constant Einstein normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem OrthonormalFrame.inverse_contraction (e : OrthonormalFrame g c) (a p : Fin 4) :
    (∑ i, ∑ b, chartMetric g c a b * e.matrix p i * e.matrix b i) =
      if a = p then 1 else 0 := by
  have hi : e.matrix * (e.matrixᵀ * chartMetric g c) = 1 :=
    mul_eq_one_comm.mp e.orthonormal
  have hij := congrFun (congrFun hi p) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hij
  calc
    _ = ∑ i, ∑ b, e.matrix p i * (e.matrix b i * chartMetric g c b a) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      have hsym : chartMetric g c a b = chartMetric g c b a := by
        simpa only [Matrix.conjTranspose_apply, star_trivial] using
          congrFun (congrFun (chartMetric_posDef g c).isHermitian.eq b) a
      rw [hsym]
      ring
    _ = if p = a then 1 else 0 := by simpa only [Finset.mul_sum] using hij
    _ = _ := by simp only [eq_comm]

theorem frameCurvature_ricci (e : OrthonormalFrame g c) (j k : Fin 4) :
    (∑ i, frameCurvature g c e i j k i) = e.ricci j k := by
  change (∑ i, ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
    chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r *
      e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b i) = _
  rw [tensor_trace_basis_change _ _ _ e.inverse_contraction]
  change (∑ q, ∑ r, e.matrix q j *
    (∑ a, curvatureComponent g c (chartAt FourSpace c c) a a q r) * e.matrix r k) =
    ∑ r, (∑ q, e.matrix q j *
      (∑ a, curvatureComponent g c (chartAt FourSpace c c) a a q r)) * e.matrix r k
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

variable {g : SmoothMetric M} {c : M}

theorem curvatureComponent_first_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) :
    curvatureComponent g c z l i j k = -curvatureComponent g c z l j i k := by
  simp only [curvatureComponent, Finset.sum_sub_distrib]
  ring

theorem frameCurvature_first_skew (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l = -frameCurvature g c e j i k l := by
  unfold frameCurvature
  have hh (a b : Fin 4) :
      (∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l) =
      -(∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p j * e.matrix q i * e.matrix r k * e.matrix b l) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ p, ∑ q, ∑ r, -(chartMetric g c a b *
          curvatureComponent g c (chartAt FourSpace c c) a p q r *
          e.matrix p j * e.matrix q i * e.matrix r k * e.matrix b l) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        rw [curvatureComponent_first_skew]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  calc
    _ = ∑ a, ∑ b, -(∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p j * e.matrix q i * e.matrix r k * e.matrix b l) := by
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hh a b))
    _ = _ := by simp only [Finset.sum_neg_distrib]


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoordinateMetricCompatibility
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric-compatibility identity for the actual Christoffel formula.
This algebraic step needs only invertibility of the chart metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem lowered_christoffel (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) (i j k : Fin 4) :
    (∑ p, metricInChart g c z k p * christoffel g c z p i j) =
      (1 / 2 : ℝ) * (partialDeriv (fun w => metricInChart g c w j k) i z +
        partialDeriv (fun w => metricInChart g c w i k) j z -
        partialDeriv (fun w => metricInChart g c w i j) k z) := by
  exact matrix_lower_inverse (metricInChart g c z) hG _ k

theorem christoffel_metric_compatibility (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) (i j k : Fin 4) :
    (∑ p, (metricInChart g c z k p * christoffel g c z p i j +
      metricInChart g c z j p * christoffel g c z p i k)) =
      partialDeriv (fun w => metricInChart g c w j k) i z := by
  have hs (a b : Fin 4) : (fun w => metricInChart g c w a b) =
      (fun w => metricInChart g c w b a) := funext fun _ => g.symm _ _ _
  rw [Finset.sum_add_distrib, lowered_christoffel g c z hG,
    lowered_christoffel g c z hG, hs k j]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartMetricSmoothness
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual pulled-back metric in a chart. The tangent
vectors are transported by the derivative of the inverse chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_inverse_vector_smooth (c : M) (u : FourSpace) :
    ContMDiffOn I4 I4.tangent ∞
      (fun z => (⟨(chartAt FourSpace c).symm z,
        mfderiv I4 I4 (chartAt FourSpace c).symm z u⟩ : TangentBundle I4 M))
      (chartAt FourSpace c).target := by
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn
  have hv : ContMDiff I4 I4.tangent ∞
      (fun z => (⟨z, u⟩ : TangentBundle I4 FourSpace)) := by
    exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hcomp := ht.comp hv.contMDiffOn (fun z hz => hz)
  apply hcomp.congr
  intro z hz
  exact congrArg (fun L : TangentSpace I4 z →L[ℝ]
      TangentSpace I4 ((chartAt FourSpace c).symm z) =>
        (⟨(chartAt FourSpace c).symm z, L u⟩ : TangentBundle I4 M))
    (mfderivWithin_of_isOpen (chartAt FourSpace c).open_target hz).symm

theorem metricInChart_contDiffOn (g : SmoothMetric M) (c : M) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun z => metricInChart g c z i j) (chartAt FourSpace c).target := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hi := chart_inverse_vector_smooth c (coordinateVector i)
  have hj := chart_inverse_vector_smooth c (coordinateVector j)
  have hinner := hi.inner_bundle hj
  exact hinner.contDiffOn

theorem metricInChart_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => metricInChart g c w i j) z :=
  (metricInChart_contDiffOn g c i j).contDiffAt
    ((chartAt FourSpace c).open_target.mem_nhds hz)

theorem matrix_det_smooth_at (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun w => A w i j) z) :
    ContDiffAt ℝ ∞ (fun w => (A w).det) z := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

theorem matrix_inverse_entry_smooth_at (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => (A w)⁻¹ i j) z := by
  have hinv : ContDiffAt ℝ ∞ (fun w => ((A w).det)⁻¹) z :=
    (matrix_det_smooth_at A z hA).inv hdet
  have hadj : ContDiffAt ℝ ∞ (fun w => (A w).adjugate i j) z := by
    simp only [Matrix.adjugate_apply]
    apply matrix_det_smooth_at
    intro r t
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : FourSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) t) z)
    · simpa only [Matrix.updateRow_ne hr] using hA r t
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

theorem christoffel_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (k i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => christoffel g c w k i j) z := by
  have hm := metricInChart_contDiffAt g c z hz
  have hd (a b d : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => partialDeriv (fun v => metricInChart g c v a b) d w) z := by
    exact ((hm a b).fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply contDiffAt_const
  unfold christoffel
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro l _
  exact (matrix_inverse_entry_smooth_at (metricInChart g c) z hm hdet k l).mul
    (((hd j l i).add (hd i l j)).sub (hd i j l))

theorem metricInChart_inv_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => (metricInChart g c w)⁻¹ i j) z :=
  matrix_inverse_entry_smooth_at (metricInChart g c) z
    (metricInChart_contDiffAt g c z hz) hdet i j

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartMetricNondegeneracy
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pulled-back metric is positive definite everywhere in its chart,
not merely at the chart's center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff MatrixOrder

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_inverse_derivative_injective (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    Function.Injective (mfderiv I4 I4 (chartAt FourSpace c).symm z) := by
  exact (mdifferentiable_chart (I := I4) c).symm.mfderiv_injective hz

theorem metricInChart_pairing (g : SmoothMetric M) (c : M) (z : FourSpace)
    (u v : Fin 4 → ℝ) :
    u ⬝ᵥ (metricInChart g c z *ᵥ v) =
      g.inner ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (WithLp.toLp 2 u))
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (WithLp.toLp 2 v)) := by
  rw [← sum_coordinateVector u, ← sum_coordinateVector v]
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner ((chartAt FourSpace c).symm z)
  change u ⬝ᵥ (metricInChart g c z *ᵥ v) = B (D _) (D _)
  have hB : B (D (∑ i, u i • coordinateVector i))
      (D (∑ j, v j • coordinateVector j)) =
      ∑ i, ∑ j, u i * (v j * B (D (coordinateVector i)) (D (coordinateVector j))) := by
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hB]
  simp only [dotProduct, mulVec, Finset.mul_sum, metricInChart, B, D]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem metricInChart_posDef (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : (metricInChart g c z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    change metricInChart g c z j i = metricInChart g c z i j
    exact g.symm ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (coordinateVector j))
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (coordinateVector i))
  · intro u hu
    simp only [star_trivial]
    rw [metricInChart_pairing]
    apply g.pos
    intro hzero
    apply hu
    apply WithLp.toLp_injective 2
    change WithLp.toLp 2 u = (0 : FourSpace)
    apply chart_inverse_derivative_injective c z hz
    let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
    change D (WithLp.toLp 2 u) = D 0
    rw [map_zero]
    exact hzero

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartMetricTransition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric pullback matrix in a chart. The tangent coordinates
at the image point use its own centered chart, so this congruence is the
zeroth-order part of the curvature coordinate-change calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartInverseMatrix (c : M) (z : FourSpace) : Mat4 :=
  fun i j => (show FourSpace from
    mfderiv I4 I4 (chartAt FourSpace c).symm z (coordinateVector j)) i

theorem metricInChart_eq_center_congruence (g : SmoothMetric M) (c : M)
    (z : FourSpace) :
    metricInChart g c z = (chartInverseMatrix c z)ᵀ *
      (chartMetric g ((chartAt FourSpace c).symm z) * chartInverseMatrix c z) := by
  ext i j
  symm
  change (fun k => chartInverseMatrix c z k i) ⬝ᵥ
    (chartMetric g ((chartAt FourSpace c).symm z) *ᵥ
      (fun k => chartInverseMatrix c z k j)) = _
  rw [chartMetric_pairing]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartVolumeDensity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local metric volume density and its exact coordinate change law.
Identification with the metric Hausdorff measure is a separate step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartVolumeDensity (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  Real.sqrt (metricInChart g c z).det

theorem chartVolumeDensity_pos (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : 0 < chartVolumeDensity g c z :=
  Real.sqrt_pos.mpr (metricInChart_posDef g c z hz).det_pos

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureFirstBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first Bianchi identity follows directly from the symmetric
Levi-Civita Christoffel symbols and is preserved by frame contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricInChart_comm (g : SmoothMetric M) (c : M) (z : FourSpace)
    (i j : Fin 4) : metricInChart g c z i j = metricInChart g c z j i := by
  exact g.symm _ _ _

theorem christoffel_comm (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j : Fin 4) : christoffel g c z l i j = christoffel g c z l j i := by
  have hm : (fun w => metricInChart g c w i j) =
      (fun w => metricInChart g c w j i) := funext fun w => metricInChart_comm g c w i j
  unfold christoffel
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem curvatureComponent_first_bianchi (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) :
    curvatureComponent g c z l i j k + curvatureComponent g c z l j k i +
      curvatureComponent g c z l k i j = 0 := by
  have hji : (fun w => christoffel g c w l j i) =
      (fun w => christoffel g c w l i j) := funext fun w => christoffel_comm g c w l j i
  have hkj : (fun w => christoffel g c w l k j) =
      (fun w => christoffel g c w l j k) := funext fun w => christoffel_comm g c w l k j
  have hki : (fun w => christoffel g c w l k i) =
      (fun w => christoffel g c w l i k) := funext fun w => christoffel_comm g c w l k i
  have hc : (∑ p, (christoffel g c z l i p * christoffel g c z p j k -
      christoffel g c z l j p * christoffel g c z p i k)) +
      (∑ p, (christoffel g c z l j p * christoffel g c z p k i -
      christoffel g c z l k p * christoffel g c z p j i)) +
      (∑ p, (christoffel g c z l k p * christoffel g c z p i j -
      christoffel g c z l i p * christoffel g c z p k j)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [christoffel_comm g c z p k i, christoffel_comm g c z p j i,
      christoffel_comm g c z p k j]
    ring
  unfold curvatureComponent
  rw [hji, hkj, hki]
  linarith

theorem frameCurvature_first_bianchi {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l + frameCurvature g c e j k i l +
      frameCurvature g c e k i j l = 0 := by
  unfold frameCurvature
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  have h := contracted_bianchi
    (fun p q r => curvatureComponent g c (chartAt FourSpace c c) a p q r)
    (curvatureComponent_first_bianchi g c (chartAt FourSpace c c) a) e.matrix i j k
  have heq (i j k : Fin 4) :
      (∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l) =
      (chartMetric g c a b * e.matrix b l) *
        ∑ p, ∑ q, ∑ r, curvatureComponent g c (chartAt FourSpace c c) a p q r *
          e.matrix p i * e.matrix q j * e.matrix r k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq, heq, heq]
  linear_combination (chartMetric g c a b * e.matrix b l) * h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureMetricSkew
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiated metric compatibility gives skew-adjointness of actual
coordinate curvature, and hence the last-slot symmetry of frame curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def matrixPartial (A : FourSpace → Mat4) (i : Fin 4) (z : FourSpace) : Mat4 :=
  fun j k => partialDeriv (fun w => A w j k) i z

def connectionMatrix (g : SmoothMetric M) (c : M) (i : Fin 4) (z : FourSpace) : Mat4 :=
  fun j k => christoffel g c z j i k

theorem partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem matrixPartial_add (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) (i : Fin 4) :
    matrixPartial (fun w => A w + B w) i z = matrixPartial A i z + matrixPartial B i z := by
  ext j k
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_fun_add (hA j k) (hB j k))

theorem matrixPartial_mul (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) (i : Fin 4) :
    matrixPartial (fun w => A w * B w) i z =
      matrixPartial A i z * B z + A z * matrixPartial B i z := by
  ext j k
  change partialDeriv (fun w => ∑ p, A w j p * B w p k) i z = _
  unfold partialDeriv
  have hsum := fderiv_fun_sum (u := Finset.univ)
    (A := fun p w => A w j p * B w p k) (fun p _ => (hA j p).mul (hB p k))
  rw [hsum, _root_.sum_apply]
  change (∑ p, partialDeriv (fun w => A w j p * B w p k) i z) = _
  simp only [partial_mul (hA _ _) (hB _ _), Finset.sum_add_distrib,
    Matrix.add_apply, Matrix.mul_apply, matrixPartial]

theorem matrixPartial_transpose (A : FourSpace → Mat4) (i : Fin 4) (z : FourSpace) :
    matrixPartial (fun w => (A w)ᵀ) i z = (matrixPartial A i z)ᵀ := rfl

theorem matrixPartial_congr {A B : FourSpace → Mat4} {z : FourSpace}
    (h : A =ᶠ[𝓝 z] B) (i : Fin 4) : matrixPartial A i z = matrixPartial B i z := by
  ext j k
  have he : (fun w => A w j k) =ᶠ[𝓝 z] (fun w => B w j k) :=
    h.mono fun _ hw => congrFun (congrFun hw j) k
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq

theorem matrixPartial_comm (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, ContDiffAt ℝ ∞ (fun w => A w j k) z) (i j : Fin 4) :
    matrixPartial (matrixPartial A j) i z = matrixPartial (matrixPartial A i) j z := by
  ext k l
  have hd := ((hA k l).fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).differentiableAt (by first | simp | exact_mod_cast le_top)
  have he (r s : Fin 4) :
      partialDeriv (fun w => partialDeriv (fun y => A y k l) s w) r z =
        fderiv ℝ (fderiv ℝ (fun y => A y k l)) z (coordinateVector r) (coordinateVector s) := by
    unfold partialDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change partialDeriv (fun w => partialDeriv (fun y => A y k l) j w) i z =
    partialDeriv (fun w => partialDeriv (fun y => A y k l) i w) j z
  rw [he, he]
  exact ((hA k l).isSymmSndFDerivAt (by simp)).eq _ _

theorem matrixPartial_metric (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) (i : Fin 4) :
    matrixPartial (metricInChart g c) i z =
      (connectionMatrix g c i z)ᵀ * metricInChart g c z +
        metricInChart g c z * connectionMatrix g c i z := by
  ext j k
  symm
  change (∑ p, christoffel g c z p i j * metricInChart g c z p k) +
      (∑ p, metricInChart g c z j p * christoffel g c z p i k) =
      partialDeriv (fun w => metricInChart g c w j k) i z
  rw [← Finset.sum_add_distrib]
  convert christoffel_metric_compatibility g c z hG i j k using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p _
  rw [metricInChart_comm g c z p k]
  ring

theorem matrix_mul_differentiable (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) :
    ∀ j k, DifferentiableAt ℝ (fun w => (A w * B w) j k) z := by
  intro j k
  change DifferentiableAt ℝ (fun w => ∑ p, A w j p * B w p k) z
  exact DifferentiableAt.fun_sum (fun p _ => (hA j p).mul (hB p k))

theorem matrixPartial_metric_second (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4) :
    matrixPartial (matrixPartial (metricInChart g c) j) i z =
      (matrixPartial (connectionMatrix g c j) i z)ᵀ * metricInChart g c z +
      (connectionMatrix g c j z)ᵀ * matrixPartial (metricInChart g c) i z +
      matrixPartial (metricInChart g c) i z * connectionMatrix g c j z +
      metricInChart g c z * matrixPartial (connectionMatrix g c j) i z := by
  let G := metricInChart g c
  let A := connectionMatrix g c j
  have hG : ∀ r t, DifferentiableAt ℝ (fun w => G w r t) z :=
    fun r t => (metricInChart_contDiffAt g c z hz r t).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hA : ∀ r t, DifferentiableAt ℝ (fun w => A w r t) z :=
    fun r t => (christoffel_contDiffAt g c z hz hdet r j t).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hAt : ∀ r t, DifferentiableAt ℝ (fun w => (A w)ᵀ r t) z := fun r t => hA t r
  have hGc : ContinuousAt G z := continuousAt_pi.mpr fun r =>
    continuousAt_pi.mpr fun t => (hG r t).continuousAt
  have hdc : ContinuousAt (fun w => (G w).det) z :=
    (continuous_id.matrix_det).continuousAt.comp hGc
  have heq : matrixPartial G j =ᶠ[𝓝 z] (fun w => (A w)ᵀ * G w + G w * A w) := by
    filter_upwards [hdc.eventually_ne hdet] with w hw
    exact matrixPartial_metric g c w (isUnit_iff_ne_zero.mpr hw) j
  change matrixPartial (matrixPartial G j) i z = _
  rw [matrixPartial_congr heq i,
    matrixPartial_add _ _ z (matrix_mul_differentiable _ _ z hAt hG)
      (matrix_mul_differentiable _ _ z hG hA) i,
    matrixPartial_mul _ _ z hAt hG i, matrixPartial_mul _ _ z hG hA i,
    matrixPartial_transpose]
  change ((matrixPartial A i z)ᵀ * G z + (A z)ᵀ * matrixPartial G i z) +
      (matrixPartial G i z * A z + G z * matrixPartial A i z) = _
  dsimp only [A, G]
  abel

def coordinateCurvatureMatrix (g : SmoothMetric M) (c : M) (i j : Fin 4)
    (z : FourSpace) : Mat4 :=
  matrixPartial (connectionMatrix g c j) i z -
    matrixPartial (connectionMatrix g c i) j z +
    connectionMatrix g c i z * connectionMatrix g c j z -
    connectionMatrix g c j z * connectionMatrix g c i z

theorem coordinateCurvatureMatrix_apply (g : SmoothMetric M) (c : M)
    (i j : Fin 4) (z : FourSpace) (k l : Fin 4) :
    coordinateCurvatureMatrix g c i j z k l = curvatureComponent g c z k i j l := by
  simp only [coordinateCurvatureMatrix, matrixPartial, connectionMatrix, Matrix.sub_apply,
    Matrix.add_apply, Matrix.mul_apply, curvatureComponent, Finset.sum_sub_distrib]
  ring

theorem coordinateCurvatureMatrix_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4) :
    (coordinateCurvatureMatrix g c i j z)ᵀ * metricInChart g c z +
      metricInChart g c z * coordinateCurvatureMatrix g c i j z = 0 := by
  apply curvature_matrix_skew_of_metric_differentials
  have hh := matrixPartial_comm (metricInChart g c) z
    (metricInChart_contDiffAt g c z hz) i j
  rw [matrixPartial_metric_second g c z hz hdet i j,
    matrixPartial_metric_second g c z hz hdet j i,
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr hdet) i,
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr hdet) j] at hh
  exact hh

theorem lowered_curvature_last_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k l : Fin 4) :
    (∑ a, metricInChart g c z a k * curvatureComponent g c z a i j l) =
      -(∑ a, metricInChart g c z a l * curvatureComponent g c z a i j k) := by
  have hh := congrFun (congrFun (coordinateCurvatureMatrix_skew g c z hz hdet i j) k) l
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    coordinateCurvatureMatrix_apply, Matrix.zero_apply] at hh
  have hleft : (∑ a, curvatureComponent g c z a i j k * metricInChart g c z a l) =
      ∑ a, metricInChart g c z a l * curvatureComponent g c z a i j k := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hright : (∑ a, metricInChart g c z k a * curvatureComponent g c z a i j l) =
      ∑ a, metricInChart g c z a k * curvatureComponent g c z a i j l := by
    apply Finset.sum_congr rfl
    intro a _
    rw [metricInChart_comm g c z k a]
  rw [hleft, hright] at hh
  linarith

theorem lowered_curvature_last_skew_at_center (g : SmoothMetric M) (c : M)
    (i j k l : Fin 4) :
    (∑ a, chartMetric g c a k * curvatureComponent g c (chartAt FourSpace c c) a i j l) =
      -(∑ a, chartMetric g c a l * curvatureComponent g c (chartAt FourSpace c c) a i j k) := by
  apply lowered_curvature_last_skew
  · exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  · exact (chartMetric_posDef g c).det_pos.ne'

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoordinateChangeCalculus
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate chain rule used for changes of metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

def jacobianMatrix (F : FourSpace → FourSpace) (z : FourSpace) : Mat4 :=
  fun a i => fderiv ℝ F z (coordinateVector i) a

theorem partialDeriv_comp {F : FourSpace → FourSpace} {f : FourSpace → ℝ}
    {z : FourSpace} (hF : DifferentiableAt ℝ F z)
    (hf : DifferentiableAt ℝ f (F z)) (i : Fin 4) :
    partialDeriv (fun w => f (F w)) i z =
      ∑ a, jacobianMatrix F z a i * partialDeriv f a (F z) := by
  let L : FourSpace →L[ℝ] ℝ := fderiv ℝ f (F z)
  have hc : partialDeriv (fun w => f (F w)) i z =
      L (fderiv ℝ F z (coordinateVector i)) :=
    congrArg (fun D : FourSpace →L[ℝ] ℝ => D (coordinateVector i))
      (hf.hasFDerivAt.comp z hF.hasFDerivAt).fderiv
  have hv : fderiv ℝ F z (coordinateVector i) =
      ∑ a, jacobianMatrix F z a i • coordinateVector a :=
    (sum_coordinateVector (fun a => jacobianMatrix F z a i)).symm
  calc
    _ = L (fderiv ℝ F z (coordinateVector i)) := hc
    _ = L (∑ a, jacobianMatrix F z a i • coordinateVector a) := congrArg L hv
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, L, partialDeriv]

theorem jacobian_entry_eq_partial {F : FourSpace → FourSpace} {z : FourSpace}
    (hF : DifferentiableAt ℝ F z) (a i : Fin 4) :
    jacobianMatrix F z a i = partialDeriv (fun w => F w a) i z := by
  have h := ((EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp z
    hF.hasFDerivAt).fderiv
  change _ = fderiv ℝ ((EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ) ∘ F) z
    (coordinateVector i)
  rw [h]
  rfl

theorem jacobian_entry_contDiffAt {F : FourSpace → FourSpace} {z : FourSpace}
    (hF : ContDiffAt ℝ ∞ F z) (a i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => jacobianMatrix F w a i) z := by
  have h := (hF.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
    (contDiffAt_const (c := coordinateVector i))
  exact (EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt.comp z h

theorem matrixPartial_comp {F : FourSpace → FourSpace} {A : FourSpace → Mat4}
    {z : FourSpace} (hF : DifferentiableAt ℝ F z)
    (hA : ∀ r s, DifferentiableAt ℝ (fun w => A w r s) (F z)) (i : Fin 4) :
    matrixPartial (fun w => A (F w)) i z =
      ∑ a, jacobianMatrix F z a i • matrixPartial A a (F z) := by
  ext r s
  simpa only [matrixPartial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    partialDeriv_comp hF (hA r s) i

theorem jacobian_partials_commute {F : FourSpace → FourSpace} {z : FourSpace}
    (hF : ContDiffAt ℝ ∞ F z) (a i j : Fin 4) :
    partialDeriv (fun w => jacobianMatrix F w a j) i z =
      partialDeriv (fun w => jacobianMatrix F w a i) j z := by
  have hone : ContDiffAt ℝ 1 F z := hF.of_le (by first | simp | exact_mod_cast le_top)
  have hnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ F w :=
    (hone.eventually (by first | simp | exact_mod_cast le_top)).mono fun w hw => hw.differentiableAt (by first | simp | exact_mod_cast le_top)
  have hcongr (r s : Fin 4) :
      partialDeriv (fun w => jacobianMatrix F w a s) r z =
      partialDeriv (fun w => partialDeriv (fun v => F v a) s w) r z := by
    have he : (fun w => jacobianMatrix F w a s) =ᶠ[𝓝 z]
        (fun w => partialDeriv (fun v => F v a) s w) :=
      hnear.mono fun w hw => jacobian_entry_eq_partial hw a s
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector r)) he.fderiv_eq
  rw [hcongr, hcongr]
  have ha : ContDiffAt ℝ ∞ (fun w => F w a) z :=
    (EuclideanSpace.proj a : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt.comp z hF
  have hs := matrixPartial_comm (fun (w : FourSpace) (_ _ : Fin 4) => F w a) z
    (fun _ _ => ha) i j
  exact congrFun (congrFun hs 0) 0

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoordinateConnectionUniqueness
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate Levi-Civita coefficients are determined by torsion
freeness and metric compatibility. This is the uniqueness step used when
changing charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem christoffel_eq_of_compatible (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det)
    (C : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ p i j, C p i j = C p j i)
    (hcompat : ∀ i j k,
      (∑ p, (metricInChart g c z k p * C p i j +
        metricInChart g c z j p * C p i k)) =
        partialDeriv (fun w => metricInChart g c w j k) i z) :
    C = christoffel g c z := by
  funext p i j
  have hv : metricInChart g c z *ᵥ (fun q => C q i j) =
      metricInChart g c z *ᵥ (fun q => christoffel g c z q i j) := by
    funext k
    change (∑ q, metricInChart g c z k q * C q i j) = _
    rw [show (metricInChart g c z *ᵥ (fun q => christoffel g c z q i j)) k =
      ∑ q, metricInChart g c z k q * christoffel g c z q i j from rfl,
      lowered_christoffel g c z hG]
    have h1 := hcompat i j k
    have h2 := hcompat j i k
    have h3 := hcompat k i j
    simp only [Finset.sum_add_distrib] at h1 h2 h3
    simp_rw [hsym _ j i] at h2
    simp_rw [hsym _ k i, hsym _ k j] at h3
    linarith only [h1, h2, h3]
  have h := congrArg (fun v => (metricInChart g c z)⁻¹ *ᵥ v) hv
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG,
    Matrix.one_mulVec] at h
  exact congrFun h p

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ConnectionPullback
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compatibility under the coordinate change formula for a
connection. The matrices here are four-dimensional chart matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem matrixPartial_congruence (J A : FourSpace → Mat4) (z : FourSpace)
    (hJ : ∀ r s, DifferentiableAt ℝ (fun w => J w r s) z)
    (hA : ∀ r s, DifferentiableAt ℝ (fun w => A w r s) z) (i : Fin 4) :
    matrixPartial (fun w => (J w)ᵀ * (A w * J w)) i z =
      (matrixPartial J i z)ᵀ * A z * J z +
        (J z)ᵀ * matrixPartial A i z * J z + (J z)ᵀ * A z * matrixPartial J i z := by
  have hAJ (r s : Fin 4) :
      DifferentiableAt ℝ (fun w => (A w * J w) r s) z := by
    change DifferentiableAt ℝ (fun w => ∑ p, A w r p * J w p s) z
    exact DifferentiableAt.fun_sum (fun p _ => (hA r p).mul (hJ p s))
  rw [matrixPartial_mul (fun w => (J w)ᵀ) (fun w => A w * J w) z
      (fun r s => hJ s r) hAJ i,
    matrixPartial_transpose, matrixPartial_mul A J z hA hJ i]
  noncomm_ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoordinateSecondBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of the second Bianchi algebra to the actual smooth
Christoffel symbols, with all four curvature slots differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem matrixPartial_sub (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) (i : Fin 4) :
    matrixPartial (fun w => A w - B w) i z = matrixPartial A i z - matrixPartial B i z := by
  ext j k
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_fun_sub (hA j k) (hB j k))

theorem product_entries_differentiable (A B : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ j k, DifferentiableAt ℝ (fun w => A w j k) z)
    (hB : ∀ j k, DifferentiableAt ℝ (fun w => B w j k) z) :
    ∀ j k, DifferentiableAt ℝ (fun w => (A w * B w) j k) z := by
  intro j k
  change DifferentiableAt ℝ (fun w => ∑ p, A w j p * B w p k) z
  exact DifferentiableAt.fun_sum (fun p _ => (hA j p).mul (hB p k))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem connectionMatrix_partial_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => matrixPartial (connectionMatrix g c j) i w a b) z := by
  exact ((christoffel_contDiffAt g c z hz hdet a j b).fderiv_right
    (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply contDiffAt_const

theorem coordinateCurvatureMatrix_eq_algebra (g : SmoothMetric M) (c : M)
    (z : FourSpace) (i j : Fin 4) :
    coordinateCurvatureMatrix g c i j z = CovariantBianchi.curvature
      (fun r => connectionMatrix g c r z)
      (fun r s => matrixPartial (connectionMatrix g c s) r z) i j := rfl

theorem coordinateCurvatureMatrix_contDiffAt (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j a b : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => coordinateCurvatureMatrix g c i j w a b) z := by
  have hp (r s : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => (connectionMatrix g c r w *
        connectionMatrix g c s w) a b) z := by
    change ContDiffAt ℝ ∞ (fun w => ∑ p,
      christoffel g c w a r p * christoffel g c w p s b) z
    apply ContDiffAt.sum
    intro p _
    exact (christoffel_contDiffAt g c z hz hdet a r p).mul
      (christoffel_contDiffAt g c z hz hdet p s b)
  exact (((connectionMatrix_partial_contDiffAt g c z hz hdet i j a b).sub
    (connectionMatrix_partial_contDiffAt g c z hz hdet j i a b)).add (hp i j)).sub (hp j i)

def coordinateCovariantCurvatureDerivative (g : SmoothMetric M) (c : M)
    (z : FourSpace) (i j k : Fin 4) : Mat4 :=
  matrixPartial (coordinateCurvatureMatrix g c j k) i z +
    connectionMatrix g c i z * coordinateCurvatureMatrix g c j k z -
    coordinateCurvatureMatrix g c j k z * connectionMatrix g c i z -
    ∑ p, (connectionMatrix g c i z p j • coordinateCurvatureMatrix g c p k z +
      connectionMatrix g c i z p k • coordinateCurvatureMatrix g c j p z)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentHamiltonian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cotangent-coordinate calculation used by the geodesic measure
argument: a Hamiltonian vector field has zero coordinate divergence.
Only the four-dimensional position and momentum coordinates needed here
are introduced. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

abbrev CotangentCoordinates := FourSpace × FourSpace

def positionDirection (r : Fin 4) : CotangentCoordinates := (coordinateVector r, 0)
def momentumDirection (r : Fin 4) : CotangentCoordinates := (0, coordinateVector r)

def cotangentHamiltonianField (H : CotangentCoordinates → ℝ)
    (z : CotangentCoordinates) : CotangentCoordinates :=
  (WithLp.toLp 2 (fun r => fderiv ℝ H z (momentumDirection r)),
    WithLp.toLp 2 (fun r => -fderiv ℝ H z (positionDirection r)))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentJacobian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eight-coordinate Jacobian calculation for the cotangent flow.
The variational equation is kept explicit here; it will be supplied by
the derivative of the actual flow with respect to its initial value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def cotangentBasis : Module.Basis CotangentIndex ℝ CotangentCoordinates :=
  (PiLp.basisFun 2 ℝ (Fin 4)).prod (PiLp.basisFun 2 ℝ (Fin 4))

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricInverseCalculus
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse metric is parallel. Its coordinate derivative is derived
from the inverse identity and the proved metric compatibility equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem matrixPartial_inverseMetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    matrixPartial (fun w => (metricInChart g c w)⁻¹) i z =
      -(connectionMatrix g c i z * (metricInChart g c z)⁻¹) -
        (metricInChart g c z)⁻¹ * (connectionMatrix g c i z)ᵀ := by
  let G := metricInChart g c
  let H := fun w => (G w)⁻¹
  have hdet : (G z).det ≠ 0 := (metricInChart_posDef g c z hz).det_pos.ne'
  have hG : IsUnit (G z).det := isUnit_iff_ne_zero.mpr hdet
  have hdG (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (metricInChart_contDiffAt g c z hz r s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hdH (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_inv_contDiffAt g c z hz hdet r s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have he : (fun w => H w * G w) =ᶠ[𝓝 z] (fun _ => 1) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
      (metricInChart_posDef g c w hw).det_pos.ne')
  have hprod := matrixPartial_congr he i
  rw [matrixPartial_mul H G z hdH hdG i] at hprod
  have hc : matrixPartial (fun _ : FourSpace => (1 : Mat4)) i z = 0 := by
    ext r s
    simp [matrixPartial, partialDeriv]
  rw [hc, matrixPartial_metric g c z hG i] at hprod
  exact inverse_metric_derivative_algebra (G z) (H z) (connectionMatrix g c i z)
    (matrixPartial H i z) (Matrix.mul_nonsing_inv _ hG) (Matrix.nonsing_inv_mul _ hG) hprod

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentKineticEnergy
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual kinetic Hamiltonian of the metric in one chart, and the
unit-energy normalization of the cotangent lift of an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def kineticHamiltonian (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates) : ℝ :=
  (WithLp.ofLp z.2 ⬝ᵥ ((metricInChart g c z.1)⁻¹ *ᵥ WithLp.ofLp z.2)) / 2

theorem kineticHamiltonian_contDiffAt (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates) (hz : z.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (kineticHamiltonian g c) z := by
  have hdet := (metricInChart_posDef g c z.1 hz).det_pos.ne'
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun w : CotangentCoordinates => (metricInChart g c w.1)⁻¹ i j) z :=
    (metricInChart_inv_contDiffAt g c z.1 hz hdet i j).comp z contDiffAt_fst
  have hp (i : Fin 4) : ContDiffAt ℝ ∞
      (fun w : CotangentCoordinates => w.2 i) z := by fun_prop
  unfold kineticHamiltonian dotProduct Matrix.mulVec
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro i _
  apply (hp i).mul
  exact ContDiffAt.sum (fun j _ => (hG i j).mul (hp j))

def frameCotangentMomentum (g : SmoothMetric M) (c : M) (x : FourSpace)
    (E : Mat4) (k : Fin 4) : FourSpace :=
  WithLp.toLp 2 (metricInChart g c x *ᵥ fun i => E i k)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylDerivative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate covariant derivatives of the actual curvature tensor. The
scalar-curvature contribution is subtracted in the Ricci=3g normalization.
The definitions retain all tensor slots until after differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Coordinate components of `<R(e_a,e_b)e_c,e_d>`. -/
def curvatureCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 4 := fun a =>
  ∑ l, metricInChart g c z l (a 3) *
    curvatureComponent g c z l (a 0) (a 1) (a 2)

/-- The curvature-one algebraic tensor in arbitrary coordinates. -/
def unitCurvatureCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 4 := fun a =>
  metricInChart g c z (a 1) (a 2) * metricInChart g c z (a 0) (a 3) -
    metricInChart g c z (a 0) (a 2) * metricInChart g c z (a 1) (a 3)

/-- For Ricci=3g this is exactly the Weyl four-tensor. Defining its coordinate
field first ensures that derivatives are taken before choosing eigenframes. -/
def normalizedWeylCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 4 := curvatureCoordinates g c z - unitCurvatureCoordinates g c z

/-- The two-form contraction for a tensor with no derivative slots. -/
def blockCoordinates (T : CovariantCoordinates 4) (Q : Fin 3 → Mat4) : Mat3 :=
  curvatureBlock (fun p q => T ![p.1, p.2, q.2, q.1]) Q

/-- A fixed derivative direction in the covariant derivative of curvature. -/
def gradientBlock (T : CovariantCoordinates 5) (Q : Fin 3 → Mat4)
    (i : Fin 4) : Mat3 :=
  blockCoordinates (fun a => T (Fin.cons i a)) Q

/-- Both derivative directions in the covariant Hessian of curvature. -/
def hessianBlock (T : CovariantCoordinates 6) (Q : Fin 3 → Mat4)
    (i j : Fin 4) : Mat3 :=
  blockCoordinates (fun a => T (Fin.cons i (Fin.cons j a))) Q

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureCoordinateSmoothness
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local regularity of the actual curvature and its coordinate covariant
derivatives, on the nonsingular part of a metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem curvatureComponent_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (l i j k : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => curvatureComponent g c w l i j k) z := by
  have hc := christoffel_contDiffAt g c z hz hdet
  have hd (r s t u : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => partialDeriv (fun v => christoffel g c v r s t) u w) z :=
    ((hc r s t).fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply contDiffAt_const
  unfold curvatureComponent
  apply ((hd l j k i).sub (hd l i k j)).add
  apply ContDiffAt.sum
  intro p _
  exact ((hc l i p).mul (hc p j k)).sub ((hc l j p).mul (hc p i k))

theorem curvatureCoordinates_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => curvatureCoordinates g c w a) z := by
  unfold curvatureCoordinates
  apply ContDiffAt.sum
  intro l _
  exact (metricInChart_contDiffAt g c z hz l (a 3)).mul
    (curvatureComponent_contDiffAt g c z hz hdet l (a 0) (a 1) (a 2))

theorem unitCurvatureCoordinates_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => unitCurvatureCoordinates g c w a) z := by
  have h := metricInChart_contDiffAt g c z hz
  exact ((h (a 1) (a 2)).mul (h (a 0) (a 3))).sub
    ((h (a 0) (a 2)).mul (h (a 1) (a 3)))

theorem normalizedWeylCoordinates_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => normalizedWeylCoordinates g c w a) z :=
  (curvatureCoordinates_contDiffAt g c z hz hdet a).sub
    (unitCurvatureCoordinates_contDiffAt g c z hz a)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeightedConnectionCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature of the pulled-back connection one-form. The symmetric
second derivative of the coordinate change cancels in the alternating sum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem matrixPartial_smul (f : FourSpace → ℝ) (A : FourSpace → Mat4)
    (z : FourSpace) (hf : DifferentiableAt ℝ f z)
    (hA : ∀ r s, DifferentiableAt ℝ (fun w => A w r s) z) (i : Fin 4) :
    matrixPartial (fun w => f w • A w) i z =
      partialDeriv f i z • A z + f z • matrixPartial A i z := by
  ext r s
  simp only [matrixPartial, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    partialDeriv, fderiv_fun_mul hf (hA r s), _root_.add_apply, _root_.smul_apply]
  ring

theorem matrixPartial_sum_four (A : Fin 4 → FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ p r s, DifferentiableAt ℝ (fun w => A p w r s) z) (i : Fin 4) :
    matrixPartial (fun w => ∑ p, A p w) i z = ∑ p, matrixPartial (A p) i z := by
  ext r s
  have hd := fderiv_fun_sum (u := Finset.univ)
    (A := fun p w => A p w r s) (fun p _ => hA p r s)
  change fderiv ℝ (fun w => ∑ p, A p w r s) z (coordinateVector i) =
    ∑ p, fderiv ℝ (fun w => A p w r s) z (coordinateVector i)
  rw [hd, _root_.sum_apply]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameBundle
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual orthonormal frames with the topology inherited from tangent
vectors. Using the tangent-bundle topology is essential: chart coordinates
at varying base points do not give a global product trivialization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_frameRealization (g : SmoothMetric M) :
    Continuous (frameRealization : FrameBundle g → M × (Fin 4 → TangentBundle I4 M)) :=
  continuous_induced_dom

theorem continuous_frameBase (g : SmoothMetric M) :
    Continuous (FrameBundle.base : FrameBundle g → M) :=
  continuous_fst.comp (continuous_frameRealization g)

theorem frameRealization_injective (g : SmoothMetric M) :
    Function.Injective (frameRealization : FrameBundle g → M × (Fin 4 → TangentBundle I4 M)) := by
  rintro ⟨x, e⟩ ⟨y, f⟩ h
  have hxy : x = y := congrArg Prod.fst h
  subst y
  have hv (i : Fin 4) : e.vector i = f.vector i := by
    apply TotalSpace.mk_injective x
    exact congrArg (fun z : M × (Fin 4 → TangentBundle I4 M) => z.2 i) h
  have hm : e.matrix = f.matrix := by
    ext i j
    exact congrArg (fun v : FourSpace => v i) (hv j)
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp at hm
      subst B
      rfl

theorem isEmbedding_frameRealization (g : SmoothMetric M) :
    Topology.IsEmbedding (frameRealization : FrameBundle g →
      M × (Fin 4 → TangentBundle I4 M)) where
  eq_induced := rfl
  injective := frameRealization_injective g

theorem tangentBundle_t2Space [T2Space M] : T2Space (TangentBundle I4 M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hne
  by_cases hbase : x.proj = y.proj
  · let e := trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj
    have hx : x ∈ e.source := e.mem_source.mpr
      (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr (by
      rw [← hbase]
      exact mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x.proj)
    have hxy : e x ≠ e y := fun heq => hne (e.toOpenPartialHomeomorph.injOn hx hy heq)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hxy) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase)
      (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt

instance instT2SpaceFrameBundle [T2Space M] (g : SmoothMetric M) : T2Space (FrameBundle g) := by
  let := tangentBundle_t2Space (M := M)
  exact (isEmbedding_frameRealization g).t2Space

def frameAt (g : SmoothMetric M) (c : M) : FrameBundle g :=
  ⟨c, canonicalFrame g c⟩

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete each unit direction to its quaternionic orthonormal frame.
This relates spherical fiber averages to actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

def directionFrameMatrix (q : Directions) : Mat4 :=
  ![![q.val 0, -q.val 1, -q.val 2, -q.val 3],
    ![q.val 1, q.val 0, q.val 3, -q.val 2],
    ![q.val 2, -q.val 3, q.val 0, q.val 1],
    ![q.val 3, q.val 2, -q.val 1, q.val 0]]

theorem directionFrameMatrix_zero (q : Directions) (i : Fin 4) :
    directionFrameMatrix q i 0 = q.val i := by
  fin_cases i <;> rfl

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two fields on the actual orthonormal frame bundle that enter the
geodesic mean-square argument. They are evaluations of the metric curvature
and its covariant derivative, with no independent curvature field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

def firstDirection : Directions :=
  ⟨coordinateVector 0, by
    simp [coordinateVector]⟩

theorem firstDirection_apply (i : Fin 4) :
    firstDirection.val i = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure in the geometric application is fixed by the metric. In four
Euclidean dimensions the diameter-normalized Hausdorff measure is multiplied
by the unit-ball factor `(pi^2 / 2) / 2^4`. Positivity and finiteness are kept
separate from the elementary probability normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

/-- Canonically normalized four-dimensional Riemannian volume, constructed
from the actual length metric rather than an unspecified measure. -/
def volumeMeasure (g : SmoothMetric M) : Measure M := by
  letI : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  exact ENNReal.ofReal (Real.pi ^ 2 / 32) • Measure.hausdorffMeasure 4

def totalVolume (g : SmoothMetric M) : ℝ := (volumeMeasure g Set.univ).toReal

/-- The volume ratio with the curvature-one round four-sphere. -/
def volumeRatio (g : SmoothMetric M) : ℝ := totalVolume g / (8 * Real.pi ^ 2 / 3)

def normalizedVolume (g : SmoothMetric M) : Measure M :=
  (volumeMeasure g Set.univ)⁻¹ • volumeMeasure g

/-- Compact Riemannian volume has positive finite mass. The normalization
argument below only needs these two facts, and does not assume a volume bound. -/
structure FinitePositiveVolume (g : SmoothMetric M) : Prop where
  positive : 0 < volumeMeasure g Set.univ
  finite : volumeMeasure g Set.univ < (∞ : ℝ≥0∞)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameAverages
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spherical disintegration of the actual frame-curvature energies.

The explicit published input `BrinKarcherAveraging` is the specialization of
the Riemannian-base times Stiefel probability measure in Brin--Karcher (1984),
Section 1, p.275, to functions depending only on the first frame direction.
It is a generic integration statement and contains no curvature estimate.
The angular curvature identities used below are proved separately. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

def DirectionInvariant {g : SmoothMetric M} (F : FrameBundle g → ℝ) : Prop :=
  ∀ e f, e.base = f.base → e.frame.vector 0 = f.frame.vector 0 → F e = F f

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameCurvatureMetricSkew
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of coordinate curvature skew-adjointness through the actual
orthonormal frame. No change-of-frame assumption is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameCurvature_last_skew_of_lowered (e : OrthonormalFrame g c)
    (h : ∀ p q r b, (∑ a, chartMetric g c a b *
      curvatureComponent g c (chartAt FourSpace c c) a p q r) =
      -(∑ a, chartMetric g c a r *
      curvatureComponent g c (chartAt FourSpace c c) a p q b)) (i j k l : Fin 4) :
    frameCurvature g c e i j k l = -frameCurvature g c e i j l k :=
  tensor_last_skew_transport (chartMetric g c) e.matrix
    (curvatureComponent g c (chartAt FourSpace c c)) h i j k l

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameOrientation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orientation is a continuous choice of one of the two orientation
classes in every orthonormal frame fiber. This separates the individual
Weyl norms used by the scalar argument from the orientation-independent sum
used in radial averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def FrameOrientation.frame {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    OrthonormalFrame g c := Classical.choose (o.nonempty_fiber c)

theorem FrameOrientation.frame_positive {g : SmoothMetric M} (o : FrameOrientation g)
    (c : M) : (⟨c, o.frame c⟩ : FrameBundle g) ∈ o.positive :=
  Classical.choose_spec (o.nonempty_fiber c)

theorem FrameOrientation.positive_iff_det {g : SmoothMetric M} (o : FrameOrientation g)
    (c : M) (e : OrthonormalFrame g c) :
    (⟨c, e⟩ : FrameBundle g) ∈ o.positive ↔ 0 < (o.frame c).matrix.det * e.matrix.det :=
  o.compatible c (o.frame c) e (o.frame_positive c)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undetermined Hessian in concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Bianchi is imposed on each fixed outer derivative, using the original
quaternion action on the inner derivative and matrix slots. -/
def divergence (X : Hessian) (i : Fin 4) (r : Fin 3) : Vec :=
  ∑ s, quaternion s (WithLp.toLp 2 (fun j => X i j s r))


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Weyl gradient, with its derivative index treated as a tangent
vector. These changes of coordinate retain every component: neither the
Bianchi equation nor a differential estimate is built into the definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bianchi TraceHessian
open scoped Manifold ContDiff

noncomputable section

/-- This is the coordinate divergence of the matrix gradient. -/
def gradientDivergence (Z : Gradient) (r : Fin 3) (i : Fin 4) : ℝ :=
  ∑ s, ∑ j, quaternionMatrix s i j * Z j s r

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricContractionCalculus
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate contraction by the actual inverse metric. This is the
local identity needed to commute covariant differentiation with trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem partialDeriv_matrix_trace (A : FourSpace → Mat4) (z : FourSpace)
    (hA : ∀ r, DifferentiableAt ℝ (fun w => A w r r) z) (i : Fin 4) :
    partialDeriv (fun w => (A w).trace) i z = (matrixPartial A i z).trace := by
  have hd := fderiv_fun_sum (u := Finset.univ)
    (A := fun r w => A w r r) (fun r _ => hA r)
  change fderiv ℝ (fun w => ∑ r, A w r r) z (coordinateVector i) =
    ∑ r, fderiv ℝ (fun w => A w r r) z (coordinateVector i)
  rw [hd, _root_.sum_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem partialDeriv_metric_contraction (g : SmoothMetric M) (c : M)
    (T : FourSpace → Mat4) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hT : ∀ r s, DifferentiableAt ℝ (fun w => T w r s) z) (i : Fin 4) :
    partialDeriv (fun w => ((metricInChart g c w)⁻¹ * T w).trace) i z =
      ((metricInChart g c z)⁻¹ *
        (matrixPartial T i z - (connectionMatrix g c i z)ᵀ * T z -
          T z * connectionMatrix g c i z)).trace := by
  let H := fun w => (metricInChart g c w)⁻¹
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  have hH (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_inv_contDiffAt g c z hz hdet r s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hprod (r : Fin 4) : DifferentiableAt ℝ (fun w => (H w * T w) r r) z := by
    change DifferentiableAt ℝ (fun w => ∑ s, H w r s * T w s r) z
    exact DifferentiableAt.fun_sum (fun s _ => (hH r s).mul (hT s r))
  rw [partialDeriv_matrix_trace (fun w => H w * T w) z hprod i,
    matrixPartial_mul H T z hH hT i, matrixPartial_inverseMetric g c z hz i]
  exact metric_trace_derivative_algebra _ _ _ _

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricTensorCompatibility
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compatibility for the actual coordinate tensor derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def metricTensorCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 2 := fun a => metricInChart g c z (a 0) (a 1)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionGenerators
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rotation of the matrix indices is recovered from the actual
quaternion commutator.  Thus a four-dimensional quaternion lift also
intertwines the three-dimensional infinitesimal rotation generators. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem imaginaryLeft_commutator_0 (v : Fin 3 → ℝ) :
    quaternionMatrix 0 * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix 0 =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation 0 *ᵥ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, imaginaryCombination_apply,
    Matrix.mulVec, dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, TraceHessian.rotation, Fin.sum_univ_three,
      Fin.sum_univ_four] <;> ring

theorem imaginaryLeft_commutator_1 (v : Fin 3 → ℝ) :
    quaternionMatrix 1 * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix 1 =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation 1 *ᵥ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, imaginaryCombination_apply,
    Matrix.mulVec, dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, TraceHessian.rotation, Fin.sum_univ_three,
      Fin.sum_univ_four] <;> ring

theorem imaginaryLeft_commutator_2 (v : Fin 3 → ℝ) :
    quaternionMatrix 2 * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix 2 =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation 2 *ᵥ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, imaginaryCombination_apply,
    Matrix.mulVec, dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [quaternionMatrix, TraceHessian.rotation, Fin.sum_univ_three,
      Fin.sum_univ_four] <;> ring

/-- The speed-two generator in the matrix indices is the commutator
of the corresponding unit imaginary quaternion. -/
theorem imaginaryLeft_commutator (s : Fin 3) (v : Fin 3 → ℝ) :
    quaternionMatrix s * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix s =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation s *ᵥ v) := by
  fin_cases s
  · exact imaginaryLeft_commutator_0 v
  · exact imaginaryLeft_commutator_1 v
  · exact imaginaryLeft_commutator_2 v

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The derivative of bundle curvature is divergence free by the
differential Bianchi equation for the actual Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian

noncomputable section

/-- Differentiate the matrix coefficient in the bundle curvature action,
keeping the tensor acted on fixed in a parallel frame. -/
def bundleCurvatureDerivative (A : Mat) (i j : Fin 4) (N : Mat) : Mat :=
  (1 / 2 : ℝ) • ∑ r, quaternionMatrix r i j • ∑ s, A r s • matrixAction s N

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual scalar derivatives in the same coordinate connection and frame
flow as the Weyl tensors. The data below contain only parallel differentiation,
Hessian symmetry and the ordinary covector Ricci commutator (Petersen,
Riemannian Geometry, §3.1.1 and Proposition 2.2.8). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarCoordinates (a : M → ℝ) (c : M) (z : FourSpace) : CovariantCoordinates 0 :=
  fun _ => a ((chartAt FourSpace c).symm z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pointwise sectional curvature criterion.

Gursky--LeBrun, `On Einstein Manifolds of Positive Sectional Curvature`
(1999), Lemma 1 proof, equation (5), pp.4--5, arXiv:math/9807055.
For Einstein curvature the minimum sectional curvature is half of
`s/6 + lambda_plus + lambda_minus`. At Ric=3g, strict positivity says
the negatives of the two minimum eigenvalues have sum less than two.
The positive-semidefinite formulation below is that local specialization.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def RicciThree (g : SmoothMetric M) : Prop :=
  ∀ c : M, chartRicci g c = (3 : ℝ) • chartMetric g c

/-- Equation (5) in the proof of the published Lemma 1, with strict
sectional positivity and scalar curvature twelve. -/
def GurskyLeBrunSectionalInput (g : SmoothMetric M) : Prop :=
  RicciThree g → HasPositiveSectionalCurvature g →
    ∀ e : FrameBundle g, ∃ x y : ℝ,
      (plusWeyl g e.base e.frame + x • (1 : Mat)).PosSemidef ∧
      (minusWeyl g e.base e.frame + y • (1 : Mat)).PosSemidef ∧ x + y < 2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci normalization in an orthonormal frame is equivalent to the
actual chart Ricci normalization. This allows the raw frame calculus data
to use the already supplied Ricci contraction for its derived identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem orthogonal_basis_conjugation_injective (E : Mat4)
    (hE : IsUnit E.det) {A B : Mat4} (h : Eᵀ * A * E = Eᵀ * B * E) : A = B := by
  have hi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hE
  have hit : (Eᵀ)⁻¹ * Eᵀ = 1 := Matrix.nonsing_inv_mul _ (by simpa using hE)
  have hc (X : Mat4) : (Eᵀ)⁻¹ * (Eᵀ * X * E) * E⁻¹ = X := by
    calc
      _ = ((Eᵀ)⁻¹ * Eᵀ) * X * (E * E⁻¹) := by noncomm_ring
      _ = X := by rw [hi, hit, one_mul, mul_one]
  have he := congrArg (fun X : Mat4 => (Eᵀ)⁻¹ * X * E⁻¹) h
  simpa only [hc] using he

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem chartRicci_three_of_frame (e : OrthonormalFrame g c)
    (h : ∀ j k, (∑ i, frameCurvature g c e i j k i) = if j = k then 3 else 0) :
    chartRicci g c = (3 : ℝ) • chartMetric g c := by
  have hf : e.ricci = (3 : ℝ) • (1 : Mat4) := by
    ext j k
    rw [← frameCurvature_ricci e j k, h j k]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite,
      mul_one, mul_zero]
  apply orthogonal_basis_conjugation_injective e.matrix
    (isUnit_iff_ne_zero.mpr e.det_ne_zero)
  change e.ricci = e.matrixᵀ * ((3 : ℝ) • chartMetric g c) * e.matrix
  rw [mul_smul_comm, smul_mul_assoc, e.orthonormal]
  exact hf

theorem ricciThree_of_frame_contraction
    (h : ∀ (e : FrameBundle g) j k,
      (∑ i, frameCurvature g e.base e.frame i j k i) = if j = k then 3 else 0) :
    RicciThree g := by
  intro c
  exact chartRicci_three_of_frame (canonicalFrame g c) (h (frameAt g c))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contracting the differential Bianchi identity, with the same index
convention as the actual frame Ricci tensor. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

def curvatureDerivativeArray (T : CovariantCoordinates 5) :
    Fin 4 → Angular.CurvatureArray := fun a i j k l => T ![a, i, j, k, l]

theorem frameTensor_precompose_five (A : Mat4) (T : CovariantCoordinates 5)
    (σ : Equiv.Perm (Fin 5)) (a : Fin 5 → Fin 4) :
    frameTensor A T (a ∘ σ) = frameTensor A (fun b => T (b ∘ σ)) a := by
  let e : (Fin 5 → Fin 4) ≃ (Fin 5 → Fin 4) :=
    Equiv.arrowCongr σ.symm (Equiv.refl (Fin 4))
  unfold frameTensor
  calc
    _ = ∑ b : Fin 5 → Fin 4,
        (∏ i, A (e b i) ((a ∘ σ) i)) * T (e b) :=
      (e.sum_comp (fun b => (∏ i, A (b i) ((a ∘ σ) i)) * T b)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      change (∏ i, A (b (σ i)) (a (σ i))) * T (b ∘ σ) = _
      rw [Equiv.prod_comp σ (fun i => A (b i) (a i))]

/-- The cyclic differential identity is preserved by the actual tensor
pullback; no orthogonality or frame-flow premise is required. -/
theorem frameTensor_differentialBianchi (A : Mat4) (T : CovariantCoordinates 5)
    (h : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T)) :
    AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray (frameTensor A T)) := by
  have hc (b : Fin 5 → Fin 4) :
      T b + T (b ∘ bianchiCycle) + T (b ∘ (bianchiCycle.trans bianchiCycle)) = 0 := by
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h1 : b ∘ bianchiCycle = ![b 1, b 2, b 0, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h2 : b ∘ (bianchiCycle.trans bianchiCycle) =
        ![b 2, b 0, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h2, hb]
    exact h _ _ _ _ _
  intro a i j k l
  let v : Fin 5 → Fin 4 := ![a, i, j, k, l]
  have h1 : v ∘ bianchiCycle = ![i, j, a, k, l] := by
    funext s
    fin_cases s <;> rfl
  have h2 : v ∘ (bianchiCycle.trans bianchiCycle) = ![j, a, i, k, l] := by
    funext s
    fin_cases s <;> rfl
  have hh : frameTensor A T v + frameTensor A T (v ∘ bianchiCycle) +
      frameTensor A T (v ∘ (bianchiCycle.trans bianchiCycle)) = 0 := by
    rw [frameTensor_precompose_five A T bianchiCycle v,
      frameTensor_precompose_five A T (bianchiCycle.trans bianchiCycle) v]
    unfold frameTensor
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    linear_combination (∏ s, A (b s) (v s)) * hc b
  rw [h1, h2] at hh
  exact hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Bianchi triple becomes the positive triple after
reflecting only the derivative index. This gives the same invariant Kato
bound for the actual opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem orientationSign_sq (i : Fin 4) : orientationSign i ^ 2 = 1 := by
  unfold orientationSign
  split_ifs <;> norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternionic contraction of a closed, alternating three-tensor.
This is the finite differential-Bianchi calculation used by Weyl blocks. -/

namespace PositiveEinsteinFour.Geometry

open Matrix
open scoped BigOperators

noncomputable section

theorem quaternion_cyclic_0 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 0 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 0 := by
  simp [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 0 + hs 1 1 0 + hs 2 2 0 + hs 3 3 0
    + (2 * hc 1 2 3 - hs 1 2 3 - hs 2 1 3 - hs 3 1 2)

theorem quaternion_cyclic_1 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 1 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 1 := by
  simp [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 1 + hs 1 1 1 + hs 2 2 1 + hs 3 3 1
    - (2 * hc 0 2 3 - hs 0 2 3 - hs 2 0 3 - hs 3 0 2)

theorem quaternion_cyclic_2 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 2 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 2 := by
  simp [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 2 + hs 1 1 2 + hs 2 2 2 + hs 3 3 2
    + (2 * hc 0 1 3 - hs 0 1 3 - hs 1 0 3 - hs 3 0 1)

theorem quaternion_cyclic_3 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s 3 j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 3 := by
  simp [TraceHessian.quaternionMatrix, Fin.sum_univ_succ]
  linear_combination hs 0 0 3 + hs 1 1 3 + hs 2 2 3 + hs 3 3 3
    - (2 * hc 0 1 2 - hs 0 1 2 - hs 1 0 2 - hs 2 0 1)

theorem quaternion_cyclic_contraction (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) (i : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s i j *
        TraceHessian.quaternionMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j i := by
  fin_cases i
  · exact quaternion_cyclic_0 B hs hc
  · exact quaternion_cyclic_1 B hs hc
  · exact quaternion_cyclic_2 B hs hc
  · exact quaternion_cyclic_3 B hs hc

theorem opposite_quaternion_cyclic_0 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 0 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 0 := by
  simp [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 0 + hs 1 1 0 + hs 2 2 0 + hs 3 3 0
    - (2 * hc 1 2 3 - hs 1 2 3 - hs 2 1 3 - hs 3 1 2)

theorem opposite_quaternion_cyclic_1 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 1 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 1 := by
  simp [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 1 + hs 1 1 1 + hs 2 2 1 + hs 3 3 1
    + (2 * hc 0 2 3 - hs 0 2 3 - hs 2 0 3 - hs 3 0 2)

theorem opposite_quaternion_cyclic_2 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 2 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 2 := by
  simp [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 2 + hs 1 1 2 + hs 2 2 2 + hs 3 3 2
    - (2 * hc 0 1 3 - hs 0 1 3 - hs 1 0 3 - hs 3 0 1)

theorem opposite_quaternion_cyclic_3 (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s 3 j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j 3 := by
  simp [Angular.oppositeMatrix, oppositeQuaternion, TraceHessian.quaternionMatrix,
    Fin.sum_univ_succ]
  linear_combination hs 0 0 3 + hs 1 1 3 + hs 2 2 3 + hs 3 3 3
    + (2 * hc 0 1 2 - hs 0 1 2 - hs 1 0 2 - hs 2 0 1)

theorem opposite_quaternion_cyclic_contraction (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ a b c, B a b c + B a c b = 0)
    (hc : ∀ a b c, B a b c + B b c a + B c a b = 0) (i : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s i j *
        Angular.oppositeMatrix s a b * B j a b) =
      -2 * ∑ j : Fin 4, B j j i := by
  fin_cases i
  · exact opposite_quaternion_cyclic_0 B hs hc
  · exact opposite_quaternion_cyclic_1 B hs hc
  · exact opposite_quaternion_cyclic_2 B hs hc
  · exact opposite_quaternion_cyclic_3 B hs hc

/-- Differential Bianchi removes the Hodge-star part of the quaternionic
contraction; its remaining part is the ordinary divergence. -/
theorem curvature_quaternion_contraction (D : Fin 4 → Angular.CurvatureArray)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (D a))
    (hc : AlgebraicCurvature.DifferentialBianchi D) (i k l : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      TraceHessian.quaternionMatrix s i j *
        TraceHessian.quaternionMatrix s a b * D j a b k l) =
      -2 * ∑ j : Fin 4, D j j i k l := by
  apply quaternion_cyclic_contraction (fun j a b => D j a b k l)
  · intro a b c
    have h := hs a b c k l
    linarith only [h]
  · intro a b c
    exact hc a b c k l


theorem opposite_curvature_quaternion_contraction (D : Fin 4 → Angular.CurvatureArray)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (D a))
    (hc : AlgebraicCurvature.DifferentialBianchi D) (i k l : Fin 4) :
    (∑ s : Fin 3, ∑ j : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4,
      Angular.oppositeMatrix s i j *
        Angular.oppositeMatrix s a b * D j a b k l) =
      -2 * ∑ j : Fin 4, D j j i k l := by
  apply opposite_quaternion_cyclic_contraction (fun j a b => D j a b k l)
  · intro a b c
    have h := hs a b c k l
    linarith only [h]
  · intro a b c
    exact hc a b c k l


/-- The block divergence is the quaternionic contraction of the complete
five-tensor, with the unused two-form pair kept intact. -/
theorem gradientBlock_divergence_eq_kernel (Q : Fin 3 → Mat4)
    (T : CovariantCoordinates 5) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Q s i j * gradientBlock T Q j s r) =
      (1 / 8 : ℝ) * ∑ c, ∑ d, Q r c d *
        (∑ s, ∑ j, ∑ a, ∑ b, Q s i j * Q s a b * T ![j, a, b, d, c]) := by
  unfold gradientBlock blockCoordinates curvatureBlock
  simp only [Fintype.sum_prod_type]
  change (∑ s, ∑ j, Q s i j * ((1 / 8 : ℝ) *
    ∑ a, ∑ b, ∑ c, ∑ d, T ![j, a, b, d, c] * Q s a b * Q r c d)) = _
  simp only [Finset.mul_sum]
  rw [sum_six_last_pair]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A divergence-free curvature derivative satisfying differential Bianchi
has a divergence-free self-dual block. -/
theorem gradientBlock_divergence_zero (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hd : ∀ i k l, ∑ j, T ![j, j, i, k, l] = 0)
    (r : Fin 3) (i : Fin 4) :
    gradientDivergence (fun j => gradientBlock T TraceHessian.quaternionMatrix j) r i = 0 := by
  change (∑ s, ∑ j, TraceHessian.quaternionMatrix s i j *
    gradientBlock T TraceHessian.quaternionMatrix j s r) = 0
  rw [gradientBlock_divergence_eq_kernel]
  have he (c d : Fin 4) :
      (∑ s, ∑ j, ∑ a, ∑ b,
        TraceHessian.quaternionMatrix s i j * TraceHessian.quaternionMatrix s a b *
          T ![j, a, b, d, c]) = 0 := by
    have h := curvature_quaternion_contraction (curvatureDerivativeArray T) hs hc i d c
    change (∑ s, ∑ j, ∑ a, ∑ b,
      TraceHessian.quaternionMatrix s i j * TraceHessian.quaternionMatrix s a b *
        T ![j, a, b, d, c]) = -2 * ∑ j, T ![j, j, i, d, c] at h
    rw [h, hd i d c, mul_zero]
  simp only [he, mul_zero, Finset.sum_const_zero]

/-- The contracted Ricci identity supplies the remaining divergence
condition; all the block-Bianchi algebra is then automatic. -/
theorem gradientBlock_divergence_of_ricci_parallel (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hl : ∀ a, AlgebraicCurvature.LastSkew (curvatureDerivativeArray T a))
    (hp : ∀ a, AlgebraicCurvature.PairSymmetric (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hr : ∀ a j k, ∑ i, T ![a, i, j, k, i] = 0)
    (r : Fin 3) (i : Fin 4) :
    gradientDivergence (fun j => gradientBlock T TraceHessian.quaternionMatrix j) r i = 0 := by
  apply gradientBlock_divergence_zero T hs hc
  intro i k l
  exact AlgebraicCurvature.divergence_zero_of_ricci_parallel
    (curvatureDerivativeArray T) hp hl hc hr i k l


/-- The opposite quaternion block satisfies its own Bianchi contraction. -/
theorem opposite_gradientBlock_divergence_zero (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hd : ∀ i k l, ∑ j, T ![j, j, i, k, l] = 0)
    (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j *
      gradientBlock T Angular.oppositeMatrix j s r) = 0 := by
  rw [gradientBlock_divergence_eq_kernel]
  have he (c d : Fin 4) :
      (∑ s, ∑ j, ∑ a, ∑ b,
        Angular.oppositeMatrix s i j * Angular.oppositeMatrix s a b *
          T ![j, a, b, d, c]) = 0 := by
    have h := opposite_curvature_quaternion_contraction
      (curvatureDerivativeArray T) hs hc i d c
    change (∑ s, ∑ j, ∑ a, ∑ b,
      Angular.oppositeMatrix s i j * Angular.oppositeMatrix s a b *
        T ![j, a, b, d, c]) = -2 * ∑ j, T ![j, j, i, d, c] at h
    rw [h, hd i d c, mul_zero]
  simp only [he, mul_zero, Finset.sum_const_zero]

theorem opposite_gradientBlock_divergence_of_ricci_parallel (T : CovariantCoordinates 5)
    (hs : ∀ a, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T a))
    (hl : ∀ a, AlgebraicCurvature.LastSkew (curvatureDerivativeArray T a))
    (hp : ∀ a, AlgebraicCurvature.PairSymmetric (curvatureDerivativeArray T a))
    (hc : AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray T))
    (hr : ∀ a j k, ∑ i, T ![a, i, j, k, i] = 0)
    (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j *
      gradientBlock T Angular.oppositeMatrix j s r) = 0 := by
  apply opposite_gradientBlock_divergence_zero T hs hc
  intro i k l
  exact AlgebraicCurvature.divergence_zero_of_ricci_parallel
    (curvatureDerivativeArray T) hp hl hc hr i k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reflection of one axis in the actual orthonormal frame. It exchanges
the two Weyl blocks, with one sign for each covariant derivative slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Matrix Bundle
open scoped BigOperators Manifold ContDiff

noncomputable section

def frameReflectionMatrix : Mat4 := Matrix.diagonal orientationSign

theorem frameReflectionMatrix_transpose : frameReflectionMatrixᵀ = frameReflectionMatrix := by
  simp [frameReflectionMatrix]

theorem frameReflectionMatrix_sq : frameReflectionMatrix * frameReflectionMatrix = 1 := by
  rw [frameReflectionMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact (pow_two (orientationSign i)).symm.trans (orientationSign_sq i)
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def OrthonormalFrame.reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) : OrthonormalFrame g c where
  matrix := e.matrix * frameReflectionMatrix
  orthonormal := by
    calc
      (e.matrix * frameReflectionMatrix)ᵀ * chartMetric g c *
          (e.matrix * frameReflectionMatrix) =
        frameReflectionMatrixᵀ * (e.matrixᵀ * chartMetric g c * e.matrix) *
          frameReflectionMatrix := by rw [Matrix.transpose_mul]; noncomm_ring
      _ = 1 := by rw [e.orthonormal, mul_one, frameReflectionMatrix_transpose,
        frameReflectionMatrix_sq]

theorem OrthonormalFrame.reflect_matrix {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (a i : Fin 4) :
    e.reflect.matrix a i = orientationSign i * e.matrix a i := by
  simp only [OrthonormalFrame.reflect, frameReflectionMatrix, Matrix.mul_diagonal]
  ring

theorem OrthonormalFrame.reflect_vector {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i : Fin 4) :
    e.reflect.vector i = orientationSign i • e.vector i := by
  ext a
  exact e.reflect_matrix a i

theorem OrthonormalFrame.reflect_reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) : e.reflect.reflect = e := by
  have hm : e.reflect.reflect.matrix = e.matrix := by
    change e.matrix * frameReflectionMatrix * frameReflectionMatrix = e.matrix
    rw [mul_assoc, frameReflectionMatrix_sq, mul_one]
  generalize hf : e.reflect.reflect = f at hm ⊢
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp at hm
      subst B
      rfl

def frameReflection {g : SmoothMetric M} (e : FrameBundle g) : FrameBundle g :=
  ⟨e.base, e.frame.reflect⟩

theorem frameCurvature_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e.reflect i j k l =
      orientationSign i * orientationSign j * orientationSign k * orientationSign l *
        frameCurvature g c e i j k l := by
  simp only [frameCurvature, OrthonormalFrame.reflect_matrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem curvatureBlock_reflect (R : (Fin 4 × Fin 4) → (Fin 4 × Fin 4) → ℝ) :
    curvatureBlock (fun p q => orientationSign p.1 * orientationSign p.2 *
      orientationSign q.2 * orientationSign q.1 * R p q) TraceHessian.quaternionMatrix =
      curvatureBlock R oppositeQuaternion := by
  ext s t
  change (1 / 8 : ℝ) * (∑ p, ∑ q, (orientationSign p.1 * orientationSign p.2 *
      orientationSign q.2 * orientationSign q.1 * R p q) *
      TraceHessian.quaternionMatrix s p.1 p.2 * TraceHessian.quaternionMatrix t q.1 q.2) =
    (1 / 8 : ℝ) * (∑ p, ∑ q, R p q *
      oppositeQuaternion s p.1 p.2 * oppositeQuaternion t q.1 q.2)
  apply congrArg (fun z : ℝ => (1 / 8 : ℝ) * z)
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  change _ = R p q *
    (orientationSign p.1 * orientationSign p.2 * TraceHessian.quaternionMatrix s p.1 p.2) *
    (orientationSign q.1 * orientationSign q.2 * TraceHessian.quaternionMatrix t q.1 q.2)
  ring

theorem curvaturePairing_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) :
    curvaturePairing g c e.reflect = fun p q => orientationSign p.1 * orientationSign p.2 *
      orientationSign q.2 * orientationSign q.1 * curvaturePairing g c e p q := by
  funext p q
  exact frameCurvature_reflect g c e p.1 p.2 q.2 q.1

theorem plusWeyl_reflect (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) :
    plusWeyl g c e.reflect = minusWeyl g c e := by
  unfold plusWeyl
  rw [curvaturePairing_reflect, curvatureBlock_reflect]
  rfl

theorem frameTensor_reflect {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)
    {n : ℕ} (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor e.reflect.matrix T a =
      (∏ i, orientationSign (a i)) * frameTensor e.matrix T a := by
  simp only [frameTensor, OrthonormalFrame.reflect_matrix, Finset.prod_mul_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem gradientBlock_frame_reflect {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (T : CovariantCoordinates 5) (i : Fin 4) :
    gradientBlock (frameTensor e.reflect.matrix T) quaternionMatrix i =
      orientationSign i • gradientBlock (frameTensor e.matrix T) oppositeQuaternion i := by
  ext s t
  simp only [gradientBlock, blockCoordinates, curvatureBlock, frameTensor_reflect,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero,
    mul_one]
  change _ = orientationSign i * ((1 / 8 : ℝ) * (_ *
    (orientationSign p.1 * orientationSign p.2 * TraceHessian.quaternionMatrix s p.1 p.2) *
    (orientationSign q.1 * orientationSign q.2 * TraceHessian.quaternionMatrix t q.1 q.2)))
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lowering the actual curvature derivative and transporting the second
Bianchi identity to the coordinate/frame tensor used by the Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem loweredCurvatureMatrix_apply (g : SmoothMetric M) (c : M)
    (z : FourSpace) (j k l m : Fin 4) :
    (metricInChart g c z * coordinateCurvatureMatrix g c j k z) m l =
      curvatureCoordinates g c z ![j, k, l, m] := by
  simp only [Matrix.mul_apply, coordinateCurvatureMatrix_apply]
  change (∑ a, metricInChart g c z m a * curvatureComponent g c z a j k l) =
    ∑ a, metricInChart g c z a m * curvatureComponent g c z a j k l
  apply Finset.sum_congr rfl
  intro a _
  rw [metricInChart_comm g c z m a]

theorem lowered_derivative_matrix (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    matrixPartial (fun w => metricInChart g c w * coordinateCurvatureMatrix g c j k w) i z -
      (connectionMatrix g c i z)ᵀ *
        (metricInChart g c z * coordinateCurvatureMatrix g c j k z) -
      (metricInChart g c z * coordinateCurvatureMatrix g c j k z) * connectionMatrix g c i z -
      (∑ p, (connectionMatrix g c i z p j •
          (metricInChart g c z * coordinateCurvatureMatrix g c p k z) +
        connectionMatrix g c i z p k •
          (metricInChart g c z * coordinateCurvatureMatrix g c j p z))) =
      metricInChart g c z * coordinateCovariantCurvatureDerivative g c z i j k := by
  have hG (a b : Fin 4) : DifferentiableAt ℝ (fun w => metricInChart g c w a b) z :=
    (metricInChart_contDiffAt g c z hz a b).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hR (a b : Fin 4) :
      DifferentiableAt ℝ (fun w => coordinateCurvatureMatrix g c j k w a b) z :=
    (coordinateCurvatureMatrix_contDiffAt g c z hz hdet j k a b).differentiableAt (by first | simp | exact_mod_cast le_top)
  rw [matrixPartial_mul _ _ z hG hR i,
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr hdet)]
  have hsum : metricInChart g c z *
      (∑ p, (connectionMatrix g c i z p j • coordinateCurvatureMatrix g c p k z +
        connectionMatrix g c i z p k • coordinateCurvatureMatrix g c j p z)) =
      ∑ p, (connectionMatrix g c i z p j •
          (metricInChart g c z * coordinateCurvatureMatrix g c p k z) +
        connectionMatrix g c i z p k •
          (metricInChart g c z * coordinateCurvatureMatrix g c j p z)) := by
    simp only [Finset.mul_sum, mul_add, mul_smul_comm]
  unfold coordinateCovariantCurvatureDerivative
  rw [mul_sub, hsum]
  noncomm_ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite curvature reconstruction for the orthonormal-frame tensor, using
metric skew-adjointness of the curvature operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_algebraic_firstSkew (e : OrthonormalFrame g c) :
    AlgebraicCurvature.FirstSkew (frameCurvature g c e) := by
  intro i j k l
  exact frameCurvature_first_skew e j i k l

theorem frame_algebraic_firstBianchi (e : OrthonormalFrame g c) :
    AlgebraicCurvature.FirstBianchi (frameCurvature g c e) :=
  frameCurvature_first_bianchi e

theorem frame_algebraic_pairSymmetric (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) :
    AlgebraicCurvature.PairSymmetric (frameCurvature g c e) :=
  AlgebraicCurvature.pairSymmetric_of_bianchi (frame_algebraic_firstSkew e) hl
    (frame_algebraic_firstBianchi e)

theorem frame_algebraic_ricciThree (e : OrthonormalFrame g c) (hRic : RicciThree g)
    (j k : Fin 4) :
    AlgebraicCurvature.ricci (frameCurvature g c e) j k = if j = k then 3 else 0 := by
  unfold AlgebraicCurvature.ricci
  rw [frameCurvature_ricci]
  have h := congrArg (fun A : Mat4 => A j k) (e.ricci_eq_three_one (hRic c))
  simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite,
    mul_one, mul_zero] using h

theorem frame_einstein_decomposition_of_lastSkew (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) (hRic : RicciThree g) :
    frameCurvature g c e = Angular.einsteinCurvatureTensor
      (plusWeyl g c e) (minusWeyl g c e) :=
  AlgebraicCurvature.einstein_decomposition_of_bianchi (frameCurvature g c e)
    (frame_algebraic_firstSkew e) hl (frame_algebraic_firstBianchi e)
    (frame_algebraic_ricciThree e hRic)

theorem frame_weyl_symmetric_of_lastSkew (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) :
    TraceHessian.symmetric (plusWeyl g c e) ∧
      TraceHessian.symmetric (minusWeyl g c e) := by
  have hp := frame_algebraic_pairSymmetric e hl
  exact ⟨AlgebraicCurvature.curvatureBlock_sub_one_symmetric _
    (frame_algebraic_firstSkew e) hl hp _,
    AlgebraicCurvature.curvatureBlock_sub_one_symmetric _
    (frame_algebraic_firstSkew e) hl hp _⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual smooth metric supplies the algebraic curvature identities.
No curvature decomposition or sectional criterion is a premise here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameCurvature_last_skew (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l = -frameCurvature g c e i j l k :=
  frameCurvature_last_skew_of_lowered e
    (fun p q r b => lowered_curvature_last_skew_at_center g c p q b r) i j k l

theorem frame_algebraic_lastSkew (e : OrthonormalFrame g c) :
    AlgebraicCurvature.LastSkew (frameCurvature g c e) :=
  fun i j k l => frameCurvature_last_skew e i j l k

theorem actual_einstein_decomposition (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameCurvature g c e = Angular.einsteinCurvatureTensor
      (plusWeyl g c e) (minusWeyl g c e) :=
  frame_einstein_decomposition_of_lastSkew e (frame_algebraic_lastSkew e) hRic

theorem actual_weyl_symmetric (e : OrthonormalFrame g c) :
    TraceHessian.symmetric (plusWeyl g c e) ∧
      TraceHessian.symmetric (minusWeyl g c e) :=
  frame_weyl_symmetric_of_lastSkew e (frame_algebraic_lastSkew e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Tracing the actual curvature derivative commutes with covariant
 differentiation.  The connection terms in the contracted input/output
 slots cancel; no Einstein equation is differentiated here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem curvature_trace_connection (C : Mat4)
    (R D : Fin 4 → Fin 4 → Mat4) (j k : Fin 4) :
    (∑ r, (D r j + C * R r j - R r j * C -
      ∑ p, (C p r • R p j + C p j • R r p)) r k) =
      (∑ r, D r j r k) -
      ((∑ p, C p j * ∑ r, R r p r k) +
        ∑ p, C p k * ∑ r, R r j r p) := by
  have hc : (∑ r, ∑ p, C r p * R r j p k) =
      ∑ r, ∑ p, C p r * R p j r k := Finset.sum_comm
  have hj : (∑ r, ∑ p, C p j * R r p r k) =
      ∑ p, C p j * ∑ r, R r p r k := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hk : (∑ r, ∑ p, R r j r p * C p k) =
      ∑ p, C p k * ∑ r, R r j r p := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hc, hj, hk]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The Ricci field in one fixed chart, retaining both covariant slots. -/
def ricciTensorCoordinates (g : SmoothMetric M) (c : M) (z : FourSpace) :
    CovariantCoordinates 2 := fun a => ricciInChart g c z (a 0) (a 1)

theorem ricciInChart_eq_curvatureMatrix_trace (g : SmoothMetric M) (c : M)
    (z : FourSpace) (j k : Fin 4) :
    ricciInChart g c z j k = ∑ r, coordinateCurvatureMatrix g c r j z r k := by
  simp only [coordinateCurvatureMatrix_apply, ricciInChart]

theorem partialDeriv_ricciInChart (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    partialDeriv (fun w => ricciInChart g c w j k) i z =
      ∑ r, matrixPartial (coordinateCurvatureMatrix g c r j) i z r k := by
  have he : (fun w => ricciInChart g c w j k) =
      fun w => ∑ r, coordinateCurvatureMatrix g c r j w r k := by
    funext w
    exact ricciInChart_eq_curvatureMatrix_trace g c w j k
  rw [he]
  unfold partialDeriv
  have hd := fderiv_fun_sum (u := Finset.univ)
    (A := fun r w => coordinateCurvatureMatrix g c r j w r k)
    (fun r _ => (coordinateCurvatureMatrix_contDiffAt g c z hz hdet r j r k).differentiableAt
      (by first | simp | exact_mod_cast le_top))
  rw [hd, _root_.sum_apply]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed reflection is continuous in the actual tangent-bundle
topology, and hence defines a measurable involution of the frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_tangent_fiber_smul (a : ℝ) :
    Continuous (fun v : TangentBundle I4 M =>
      (⟨v.proj, a • v.2⟩ : TangentBundle I4 M)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  rw [FiberBundle.continuousAt_totalSpace FourSpace]
  refine ⟨(FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt, ?_⟩
  let e := trivializationAt FourSpace (TangentSpace I4 : M → Type _) v.proj
  have hv : v ∈ e.source := e.mem_source.mpr
    (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) v.proj)
  have hc : ContinuousAt (fun w : TangentBundle I4 M => (e w).2) v :=
    continuous_snd.continuousAt.comp (e.toOpenPartialHomeomorph.continuousAt hv)
  apply ((continuousAt_const (y := a)).smul hc).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hv] with w hw
  have hb : w.proj ∈ e.baseSet := e.mem_source.mp hw
  change (e (⟨w.proj, a • w.2⟩ : TangentBundle I4 M)).2 = a • (e w).2
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ w.proj hb]
  change e.continuousLinearEquivAt ℝ w.proj hb (a • w.2) =
    a • (e (⟨w.proj, w.2⟩ : TangentBundle I4 M)).2
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ w.proj hb]
  exact map_smul _ _ _

theorem continuous_frameReflection (g : SmoothMetric M) :
    Continuous (frameReflection : FrameBundle g → FrameBundle g) := by
  apply continuous_induced_rng.mpr
  have hv (i : Fin 4) : Continuous (fun e : FrameBundle g =>
      (⟨e.base, orientationSign i • e.frame.vector i⟩ : TangentBundle I4 M)) :=
    (continuous_tangent_fiber_smul (orientationSign i)).comp
      ((continuous_apply i).comp (continuous_snd.comp (continuous_frameRealization g)))
  convert! (continuous_frameBase g).prodMk (continuous_pi hv) using 1
  all_goals try with_reducible_and_instances rfl
  funext e
  change (e.base, fun i => (⟨e.base, e.frame.reflect.vector i⟩ : TangentBundle I4 M)) =
    (e.base, fun i => (⟨e.base, orientationSign i • e.frame.vector i⟩ : TangentBundle I4 M))
  apply Prod.ext
  · rfl
  · funext i
    exact congrArg (fun v => (⟨e.base, v⟩ : TangentBundle I4 M)) (e.frame.reflect_vector i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant sectional-curvature tensor is parallel for the actual
metric connection. Thus subtracting it preserves differential Bianchi. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem partial_product {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem partial_difference {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w - h w) i z = partialDeriv f i z - partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_sub hf hh, _root_.sub_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite frame transport for the differentiated Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem frameTensor_cons {n : ℕ} (E : Mat4) (T : CovariantCoordinates (n + 1))
    (a : Fin 4) (v : Fin n → Fin 4) :
    frameTensor E T (Fin.cons a v) =
      ∑ b, E b a * frameTensor E (fun w => T (Fin.cons b w)) v := by
  let f : (Fin (n + 1) → Fin 4) → ℝ :=
    fun w => (∏ i, E (w i) ((Fin.cons a v : Fin (n + 1) → Fin 4) i)) * T w
  change (∑ w, f w) = _
  rw [sum_tensor_cons f]
  dsimp only [f]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    frameTensor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem frameTensor_zero (E : Mat4) (T : CovariantCoordinates 0)
    (a : Fin 0 → Fin 4) : frameTensor E T a = T a := by
  unfold frameTensor
  rw [Fintype.sum_subsingleton _ a]
  simp

theorem frameTensor_three (E : Mat4) (T : CovariantCoordinates 3)
    (i j k : Fin 4) :
    frameTensor E T ![i, j, k] =
      ∑ a, ∑ b, ∑ c, E a i * E b j * E c k * T ![a, b, c] := by
  change frameTensor E T (Fin.cons i (Fin.cons j (Fin.cons k ![]))) = _
  simp only [frameTensor_cons, frameTensor_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  change E a i * (E b j * (E c k * T ![a, b, c])) = _
  ring

theorem frameTensor_four (E : Mat4) (T : CovariantCoordinates 4)
    (i j k l : Fin 4) :
    frameTensor E T ![i, j, k, l] =
      ∑ a, ∑ b, ∑ c, ∑ d, E a i * E b j * E c k * E d l * T ![a, b, c, d] := by
  change frameTensor E T (Fin.cons i (Fin.cons j (Fin.cons k (Fin.cons l ![])))) = _
  simp only [frameTensor_cons, frameTensor_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  change E a i * (E b j * (E c k * (E d l * T ![a, b, c, d]))) = _
  ring

theorem frameTensor_trace_gram (E : Mat4) (T : CovariantCoordinates 4)
    (j k : Fin 4) :
    (∑ i, frameTensor E T ![i, j, k, i]) =
      ∑ b, ∑ c, E b j * E c k *
        (∑ a, ∑ d, (E * Eᵀ) a d * T ![a, b, c, d]) := by
  simp only [frameTensor_four]
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i,
        E a i * E b j * E c k * E d i * T ![a, b, c, d] := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
        E b j * E c k * ((E * Eᵀ) a d * T ![a, b, c, d]) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ b, ∑ c, ∑ a, ∑ d,
        E b j * E c k * ((E * Eᵀ) a d * T ![a, b, c, d]) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem OrthonormalFrame.matrix_mul_transpose (e : OrthonormalFrame g c) :
    e.matrix * e.matrixᵀ = (chartMetric g c)⁻¹ := by
  have hi : e.matrix * (e.matrixᵀ * chartMetric g c) = 1 :=
    mul_eq_one_comm.mp e.orthonormal
  have hG : IsUnit (chartMetric g c).det :=
    isUnit_iff_ne_zero.mpr (chartMetric_posDef g c).det_pos.ne'
  calc
    _ = e.matrix * e.matrixᵀ * (chartMetric g c * (chartMetric g c)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hG, mul_one]
    _ = (e.matrix * (e.matrixᵀ * chartMetric g c)) * (chartMetric g c)⁻¹ := by
      noncomm_ring
    _ = _ := by rw [hi, one_mul]

/-- Contracting in an orthonormal frame equals contraction by the inverse
chart metric before framing the uncontracted indices. -/
theorem frameTensor_trace_inverse (e : OrthonormalFrame g c)
    (T : CovariantCoordinates 4) (j k : Fin 4) :
    (∑ i, frameTensor e.matrix T ![i, j, k, i]) =
      ∑ b, ∑ d, e.matrix b j * e.matrix d k *
        (∑ a, ∑ f, (chartMetric g c)⁻¹ a f * T ![a, b, d, f]) := by
  rw [frameTensor_trace_gram, e.matrix_mul_transpose]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation preserves the algebraic slot symmetries.
The statements here apply to the actual coordinate curvature and its
actual orthonormal-frame pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameTensor_permute {n : ℕ} (E : Mat4) (T : CovariantCoordinates n)
    (σ : Equiv.Perm (Fin n)) (a : Fin n → Fin 4) :
    frameTensor E T (a ∘ σ) = frameTensor E (fun b => T (b ∘ σ)) a := by
  let f : (Fin n → Fin 4) → ℝ :=
    fun b => (∏ i, E (b i) (a (σ i))) * T b
  change (∑ b, f b) = _
  rw [sum_tensor_permute f σ]
  change (∑ b, (∏ i, E (b (σ i)) (a (σ i))) * T (b ∘ σ)) = _
  apply Finset.sum_congr rfl
  intro b _
  rw [Equiv.prod_comp σ (fun i => E (b i) (a i))]

theorem frameTensor_neg {n : ℕ} (E : Mat4) (T : CovariantCoordinates n)
    (a : Fin n → Fin 4) : frameTensor E (-T) a = -frameTensor E T a := by
  simp only [frameTensor, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite covector-slot action used by the actual tensor commutator.
The anti-representation sign comes from acting on covariant slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

/-- Apply a matrix in one covariant slot. -/
def covariantSlotAction {n : ℕ} (s : Fin n) (A : Mat4)
    (T : CovariantCoordinates n) : CovariantCoordinates n := fun a =>
  ∑ b, A b (a s) * T (Function.update a s b)

/-- The induced action on all covariant slots. -/
def tensorSlotAction {n : ℕ} (A : Mat4) (T : CovariantCoordinates n) :
    CovariantCoordinates n := fun a => ∑ s, covariantSlotAction s A T a

theorem covariantSlotAction_add_matrix {n : ℕ} (s : Fin n) (A B : Mat4)
    (T : CovariantCoordinates n) :
    covariantSlotAction s (A + B) T =
      covariantSlotAction s A T + covariantSlotAction s B T := by
  funext a
  simp only [covariantSlotAction, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib, Pi.add_apply]

theorem covariantSlotAction_sub_matrix {n : ℕ} (s : Fin n) (A B : Mat4)
    (T : CovariantCoordinates n) :
    covariantSlotAction s (A - B) T =
      covariantSlotAction s A T - covariantSlotAction s B T := by
  funext a
  simp only [covariantSlotAction, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib, Pi.sub_apply]

theorem covariantSlotAction_sub_tensor {n : ℕ} (s : Fin n) (A : Mat4)
    (S T : CovariantCoordinates n) :
    covariantSlotAction s A (S - T) =
      covariantSlotAction s A S - covariantSlotAction s A T := by
  funext a
  simp only [covariantSlotAction, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem covariantSlotAction_same {n : ℕ} (s : Fin n) (A B : Mat4)
    (T : CovariantCoordinates n) :
    covariantSlotAction s A (covariantSlotAction s B T) =
      covariantSlotAction s (B * A) T := by
  funext a
  simp only [covariantSlotAction, Function.update_self, Function.update_idem,
    Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem covariantSlotAction_distinct {n : ℕ} (s t : Fin n) (hst : s ≠ t)
    (A B : Mat4) (T : CovariantCoordinates n) :
    covariantSlotAction s A (covariantSlotAction t B T) =
      covariantSlotAction t B (covariantSlotAction s A T) := by
  funext a
  simp only [covariantSlotAction, Function.update_of_ne hst,
    Function.update_of_ne hst.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  rw [Function.update_comm hst]
  ring

theorem covariantSlotAction_commutator {n : ℕ} (s t : Fin n)
    (A B : Mat4) (T : CovariantCoordinates n) :
    covariantSlotAction s A (covariantSlotAction t B T) -
      covariantSlotAction t B (covariantSlotAction s A T) =
        if s = t then covariantSlotAction s (B * A - A * B) T else 0 := by
  by_cases hst : s = t
  · subst t
    rw [ite_eq_left rfl, covariantSlotAction_same, covariantSlotAction_same,
      covariantSlotAction_sub_matrix]
  · rw [ite_eq_right hst, covariantSlotAction_distinct s t hst, sub_self]

theorem tensorSlotAction_add_matrix {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction (A + B) T = tensorSlotAction A T + tensorSlotAction B T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_add_matrix, Pi.add_apply,
    Finset.sum_add_distrib]

theorem tensorSlotAction_sub_matrix {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction (A - B) T = tensorSlotAction A T - tensorSlotAction B T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_sub_matrix, Pi.sub_apply,
    Finset.sum_sub_distrib]

theorem tensorSlotAction_sub_tensor {n : ℕ} (A : Mat4)
    (S T : CovariantCoordinates n) :
    tensorSlotAction A (S - T) = tensorSlotAction A S - tensorSlotAction A T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction_sub_tensor, Pi.sub_apply,
    Finset.sum_sub_distrib]

theorem tensorSlotAction_compose {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    tensorSlotAction A (tensorSlotAction B T) a =
      ∑ s, ∑ t, covariantSlotAction s A (covariantSlotAction t B T) a := by
  unfold tensorSlotAction
  apply Finset.sum_congr rfl
  intro s _
  simp only [covariantSlotAction, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Covariant tensors form the anti-representation of the matrix slot
operation; the opposite sign is the covector curvature sign. -/
theorem tensorSlotAction_commutator {n : ℕ} (A B : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction A (tensorSlotAction B T) -
      tensorSlotAction B (tensorSlotAction A T) =
        tensorSlotAction (B * A - A * B) T := by
  funext a
  rw [Pi.sub_apply, tensorSlotAction_compose, tensorSlotAction_compose]
  rw [Finset.sum_comm (f := fun s t => covariantSlotAction s B (covariantSlotAction t A T) a)]
  rw [← Finset.sum_sub_distrib]
  change (∑ s, ((∑ t, covariantSlotAction s A (covariantSlotAction t B T) a) -
    (∑ t, covariantSlotAction t B (covariantSlotAction s A T) a))) = _
  simp only [← Finset.sum_sub_distrib]
  have he (s t : Fin n) :
      covariantSlotAction s A (covariantSlotAction t B T) a -
        covariantSlotAction t B (covariantSlotAction s A T) a =
      if s = t then covariantSlotAction s (B * A - A * B) T a else 0 := by
    have h := congrFun (covariantSlotAction_commutator s t A B T) a
    simpa only [Pi.sub_apply, Pi.zero_apply, ite_apply] using h
  simp only [he]
  simp [tensorSlotAction]

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def curvatureArray (T : CovariantCoordinates 4) : Angular.CurvatureArray :=
  fun i j k l => T ![i, j, k, l]

theorem firstSkew_permute (T : CovariantCoordinates 4)
    (h : AlgebraicCurvature.FirstSkew (curvatureArray T)) (a : Fin 4 → Fin 4) :
    T (a ∘ Equiv.swap 0 1) = -T a := by
  have h1 : a ∘ Equiv.swap 0 1 = ![a 1, a 0, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  have h0 : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h0]
  exact h _ _ _ _

theorem lastSkew_permute (T : CovariantCoordinates 4)
    (h : AlgebraicCurvature.LastSkew (curvatureArray T)) (a : Fin 4 → Fin 4) :
    T (a ∘ Equiv.swap 2 3) = -T a := by
  have h1 : a ∘ Equiv.swap 2 3 = ![a 0, a 1, a 3, a 2] := by
    funext i
    fin_cases i <;> rfl
  have h0 : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h0]
  exact h _ _ _ _

theorem pairSymmetric_permute (T : CovariantCoordinates 4)
    (h : AlgebraicCurvature.PairSymmetric (curvatureArray T)) (a : Fin 4 → Fin 4) :
    T (a ∘ pairSwap) = T a := by
  have h1 : a ∘ pairSwap = ![a 2, a 3, a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  have h0 : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [h1, h0]
  exact h _ _ _ _

theorem coordinate_curvature_firstSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) : AlgebraicCurvature.FirstSkew
      (curvatureArray (curvatureCoordinates g c z)) := by
  intro i j k l
  change (∑ r, metricInChart g c z r l * curvatureComponent g c z r j i k) =
    -(∑ r, metricInChart g c z r l * curvatureComponent g c z r i j k)
  simp_rw [curvatureComponent_first_skew g c z _ j i k]
  simp only [mul_neg, Finset.sum_neg_distrib]

theorem coordinate_curvature_lastSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) : AlgebraicCurvature.LastSkew
      (curvatureArray (curvatureCoordinates g c z)) := by
  intro i j k l
  exact lowered_curvature_last_skew g c z hz hdet i j k l

theorem coordinate_curvature_firstBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) : AlgebraicCurvature.FirstBianchi
      (curvatureArray (curvatureCoordinates g c z)) := by
  intro i j k l
  change (∑ r, metricInChart g c z r l * curvatureComponent g c z r i j k) +
    (∑ r, metricInChart g c z r l * curvatureComponent g c z r j k i) +
    (∑ r, metricInChart g c z r l * curvatureComponent g c z r k i j) = 0
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r _
  linear_combination metricInChart g c z r l * curvatureComponent_first_bianchi g c z r i j k

theorem coordinate_curvature_pairSymmetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) : AlgebraicCurvature.PairSymmetric
      (curvatureArray (curvatureCoordinates g c z)) :=
  AlgebraicCurvature.pairSymmetric_of_bianchi
    (coordinate_curvature_firstSkew g c z)
    (coordinate_curvature_lastSkew g c z hz hdet)
    (coordinate_curvature_firstBianchi g c z)

theorem frameTensor_firstSkew (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.FirstSkew (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hp (b : Fin 5 → Fin 4) : T (b ∘ Equiv.swap 1 2) = -T b := by
    have h1 : b ∘ Equiv.swap 1 2 = ![b 0, b 2, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact h _ _ _ _ _
  intro i j k l
  have hv : ![d, i, j, k, l] ∘ Equiv.swap 1 2 = ![d, j, i, k, l] := by
    funext a
    fin_cases a <;> rfl
  change frameTensor E T ![d, j, i, k, l] = -frameTensor E T ![d, i, j, k, l]
  rw [← hv, frameTensor_permute]
  have he : (fun b => T (b ∘ Equiv.swap 1 2)) = -T := funext hp
  rw [he, frameTensor_neg]

theorem frameTensor_lastSkew (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.LastSkew (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.LastSkew
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hp (b : Fin 5 → Fin 4) : T (b ∘ Equiv.swap 3 4) = -T b := by
    have h1 : b ∘ Equiv.swap 3 4 = ![b 0, b 1, b 2, b 4, b 3] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact h _ _ _ _ _
  intro i j k l
  have hv : ![d, i, j, k, l] ∘ Equiv.swap 3 4 = ![d, i, j, l, k] := by
    funext a
    fin_cases a <;> rfl
  change frameTensor E T ![d, i, j, l, k] = -frameTensor E T ![d, i, j, k, l]
  rw [← hv, frameTensor_permute]
  have he : (fun b => T (b ∘ Equiv.swap 3 4)) = -T := funext hp
  rw [he, frameTensor_neg]

theorem frameTensor_pairSymmetric (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.PairSymmetric (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.PairSymmetric
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hp (b : Fin 5 → Fin 4) : T (b ∘ derivativePairSwap) = T b := by
    have h1 : b ∘ derivativePairSwap = ![b 0, b 3, b 4, b 1, b 2] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact h _ _ _ _ _
  intro i j k l
  have hv : ![d, i, j, k, l] ∘ derivativePairSwap = ![d, k, l, i, j] := by
    funext a
    fin_cases a <;> rfl
  change frameTensor E T ![d, k, l, i, j] = frameTensor E T ![d, i, j, k, l]
  rw [← hv, frameTensor_permute]
  have he : (fun b => T (b ∘ derivativePairSwap)) = T := funext hp
  rw [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual commutation of the coordinate Levi-Civita derivative on the
covariant tensors used for the Weyl Hessian and its first derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def tensorPartial {n : ℕ} (T : FourSpace → CovariantCoordinates n)
    (i : Fin 4) (z : FourSpace) : CovariantCoordinates n :=
  fun a => partialDeriv (fun w => T w a) i z

def tensorCovariantDirection {n : ℕ} (G : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (i : Fin 4) (z : FourSpace) :
    CovariantCoordinates n := tensorPartial T i z - tensorSlotAction (G i z) (T z)

theorem tensor_partial_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (z : FourSpace)
    (hF : ∀ a, DifferentiableAt ℝ (F a) z) (i : Fin 4) :
    partialDeriv (fun w => ∑ a, F a w) i z = ∑ a, partialDeriv (F a) i z := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun a _ => hF a), _root_.sum_apply]

theorem tensor_partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem tensorPartial_sub {n : ℕ} (S T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hS : ∀ a, DifferentiableAt ℝ (fun w => S w a) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) (i : Fin 4) :
    tensorPartial (fun w => S w - T w) i z = tensorPartial S i z - tensorPartial T i z := by
  funext a
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_fun_sub (hS a) (hT a))

theorem tensorPartial_slotAction {n : ℕ} (A : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hA : ∀ b c, DifferentiableAt ℝ (fun w => A w b c) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) (i : Fin 4) :
    tensorPartial (fun w => tensorSlotAction (A w) (T w)) i z =
      tensorSlotAction (matrixPartial A i z) (T z) +
        tensorSlotAction (A z) (tensorPartial T i z) := by
  funext a
  have hd (s : Fin n) : DifferentiableAt ℝ
      (fun w => ∑ b, A w b (a s) * T w (Function.update a s b)) z :=
    DifferentiableAt.fun_sum (u := Finset.univ)
      (fun b _ => (hA b (a s)).mul (hT (Function.update a s b)))
  have hi (s : Fin n) :
      partialDeriv (fun w => ∑ b, A w b (a s) * T w (Function.update a s b)) i z =
        ∑ b, partialDeriv (fun w => A w b (a s) * T w (Function.update a s b)) i z :=
    tensor_partial_sum _ z (fun b => (hA b (a s)).mul (hT (Function.update a s b))) i
  have hp (s : Fin n) (b : Fin 4) :
      partialDeriv (fun w => A w b (a s) * T w (Function.update a s b)) i z =
        partialDeriv (fun w => A w b (a s)) i z * T z (Function.update a s b) +
          A z b (a s) * partialDeriv (fun w => T w (Function.update a s b)) i z :=
    tensor_partial_mul (hA b (a s)) (hT (Function.update a s b)) i
  change partialDeriv (fun w => ∑ s, ∑ b, A w b (a s) *
    T w (Function.update a s b)) i z = _
  rw [tensor_partial_sum _ z hd i]
  simp only [hi, hp, Finset.sum_add_distrib,
    tensorSlotAction, covariantSlotAction, matrixPartial, tensorPartial, Pi.add_apply]

theorem tensorPartial_comm {n : ℕ} (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z)
    (i j : Fin 4) :
    tensorPartial (tensorPartial T j) i z = tensorPartial (tensorPartial T i) j z := by
  funext a
  have hd := ((hT a).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he (r s : Fin 4) :
      partialDeriv (fun w => partialDeriv (fun y => T y a) s w) r z =
        fderiv ℝ (fderiv ℝ (fun y => T y a)) z (coordinateVector r) (coordinateVector s) := by
    unfold partialDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change partialDeriv (fun w => partialDeriv (fun y => T y a) j w) i z =
    partialDeriv (fun w => partialDeriv (fun y => T y a) i w) j z
  rw [he, he]
  exact ((hT a).isSymmSndFDerivAt (by simp)).eq _ _

theorem slotAction_contDiffAt {n : ℕ} (A : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hA : ∀ b c, ContDiffAt ℝ ∞ (fun w => A w b c) z)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (a : Fin n → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => tensorSlotAction (A w) (T w) a) z := by
  apply ContDiffAt.sum
  intro s _
  apply ContDiffAt.sum
  intro b _
  exact (hA b _).mul (hT _)

theorem tensorCovariantDirection_commutator {n : ℕ}
    (G : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hG : ∀ i b c, ContDiffAt ℝ ∞ (fun w => G i w b c) z)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (i j : Fin 4) :
    tensorCovariantDirection G (tensorCovariantDirection G T j) i z -
      tensorCovariantDirection G (tensorCovariantDirection G T i) j z =
        -tensorSlotAction
          (matrixPartial (G j) i z - matrixPartial (G i) j z +
            (G i z * G j z - G j z * G i z)) (T z) := by
  have hp (r : Fin 4) (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => tensorPartial T r w a) z :=
    (((hT a).fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply contDiffAt_const).differentiableAt
      (by first | simp | exact_mod_cast le_top)
  have hs (r : Fin 4) (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => tensorSlotAction (G r w) (T w) a) z :=
    (slotAction_contDiffAt (G r) T z (hG r) hT a).differentiableAt (by first | simp | exact_mod_cast le_top)
  unfold tensorCovariantDirection
  rw [tensorPartial_sub _ _ z (hp j) (hs j),
    tensorPartial_sub _ _ z (hp i) (hs i),
    tensorPartial_slotAction (G j) T z (fun b c => (hG j b c).differentiableAt (by simp))
      (fun a => (hT a).differentiableAt (by simp)),
    tensorPartial_slotAction (G i) T z (fun b c => (hG i b c).differentiableAt (by simp))
      (fun a => (hT a).differentiableAt (by simp)),
    tensorSlotAction_sub_tensor, tensorSlotAction_sub_tensor,
    tensorPartial_comm T z hT i j,
    tensorSlotAction_add_matrix, tensorSlotAction_sub_matrix,
    tensorSlotAction_sub_matrix]
  have hc := tensorSlotAction_commutator (G i z) (G j z) (T z)
  rw [tensorSlotAction_sub_matrix] at hc
  have hh := congrArg (fun X : CovariantCoordinates n =>
    X - tensorSlotAction (matrixPartial (G j) i z) (T z) +
      tensorSlotAction (matrixPartial (G i) j z) (T z)) hc
  abel_nf at hh ⊢
  exact hh

theorem tensorCovariantDirection_cons {n : ℕ}
    (G : Fin 4 → FourSpace → Mat4) (S : FourSpace → CovariantCoordinates (n + 1))
    (z : FourSpace) (i j : Fin 4) (a : Fin n → Fin 4) :
    tensorCovariantDirection G S i z (Fin.cons j a) =
      tensorCovariantDirection G (fun w b => S w (Fin.cons j b)) i z a -
        ∑ b, G i z b j * S z (Fin.cons b a) := by
  simp only [tensorCovariantDirection, tensorPartial, tensorSlotAction,
    covariantSlotAction, Pi.sub_apply, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation and framing preserve the algebraic first
Bianchi identity as well as the pair and alternating symmetries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameTensor_firstBianchi (E : Mat4) (T : CovariantCoordinates 5)
    (h : ∀ d, AlgebraicCurvature.FirstBianchi (curvatureDerivativeArray T d))
    (d : Fin 4) : AlgebraicCurvature.FirstBianchi
      (curvatureDerivativeArray (frameTensor E T) d) := by
  have hc (b : Fin 5 → Fin 4) : T b + T (b ∘ frameCurvatureCycle) +
      T (b ∘ (frameCurvatureCycle.trans frameCurvatureCycle)) = 0 := by
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h1 : b ∘ frameCurvatureCycle = ![b 0, b 2, b 3, b 1, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h2 : b ∘ (frameCurvatureCycle.trans frameCurvatureCycle) =
        ![b 0, b 3, b 1, b 2, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h2, hb]
    exact h _ _ _ _ _
  intro i j k l
  let v : Fin 5 → Fin 4 := ![d, i, j, k, l]
  have h1 : v ∘ frameCurvatureCycle = ![d, j, k, i, l] := by
    funext a
    fin_cases a <;> rfl
  have h2 : v ∘ (frameCurvatureCycle.trans frameCurvatureCycle) = ![d, k, i, j, l] := by
    funext a
    fin_cases a <;> rfl
  have hh : frameTensor E T v + frameTensor E T (v ∘ frameCurvatureCycle) +
      frameTensor E T (v ∘ (frameCurvatureCycle.trans frameCurvatureCycle)) = 0 := by
    rw [frameTensor_permute E T frameCurvatureCycle,
      frameTensor_permute E T (frameCurvatureCycle.trans frameCurvatureCycle)]
    unfold frameTensor
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    linear_combination (∏ s, E (b s) (v s)) * hc b
  rw [h1, h2] at hh
  exact hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic curvature symmetries persist through a second covariant
derivative; all derivative slots remain separate from curvature slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def curvatureHessianArray (T : CovariantCoordinates 6) (d e : Fin 4) :
    Angular.CurvatureArray := fun i j k l => T ![d, e, i, j, k, l]

theorem frameHessian_firstSkew (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d e, AlgebraicCurvature.FirstSkew (curvatureHessianArray T d e))
    (d e : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureHessianArray (frameTensor E T) d e) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![e, j, i, k, l]) =
    -frameTensor E T (Fin.cons d ![e, i, j, k, l])
  rw [frameTensor_cons E T d ![e, j, i, k, l],
    frameTensor_cons E T d ![e, i, j, k, l]]
  have hp (p : Fin 4) :
      frameTensor E (fun w => T (Fin.cons p w)) ![e, j, i, k, l] =
        -frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, k, l] :=
    frameTensor_firstSkew E (fun w => T (Fin.cons p w)) (h p) e i j k l
  simp only [hp, mul_neg, Finset.sum_neg_distrib]

theorem frameHessian_lastSkew (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d e, AlgebraicCurvature.LastSkew (curvatureHessianArray T d e))
    (d e : Fin 4) : AlgebraicCurvature.LastSkew
      (curvatureHessianArray (frameTensor E T) d e) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![e, i, j, l, k]) =
    -frameTensor E T (Fin.cons d ![e, i, j, k, l])
  rw [frameTensor_cons E T d ![e, i, j, l, k],
    frameTensor_cons E T d ![e, i, j, k, l]]
  have hp (p : Fin 4) :
      frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, l, k] =
        -frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, k, l] :=
    frameTensor_lastSkew E (fun w => T (Fin.cons p w)) (h p) e i j k l
  simp only [hp, mul_neg, Finset.sum_neg_distrib]

theorem frameHessian_pairSymmetric (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d e, AlgebraicCurvature.PairSymmetric (curvatureHessianArray T d e))
    (d e : Fin 4) : AlgebraicCurvature.PairSymmetric
      (curvatureHessianArray (frameTensor E T) d e) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![e, k, l, i, j]) =
    frameTensor E T (Fin.cons d ![e, i, j, k, l])
  rw [frameTensor_cons E T d ![e, k, l, i, j],
    frameTensor_cons E T d ![e, i, j, k, l]]
  have hp (p : Fin 4) :
      frameTensor E (fun w => T (Fin.cons p w)) ![e, k, l, i, j] =
        frameTensor E (fun w => T (Fin.cons p w)) ![e, i, j, k, l] :=
    frameTensor_pairSymmetric E (fun w => T (Fin.cons p w)) (h p) e i j k l
  simp only [hp]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite frame covariance for the curvature action on covariant tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem frameTensor_add {n : ℕ} (E : Mat4) (S T : CovariantCoordinates n)
    (a : Fin n → Fin 4) :
    frameTensor E (S + T) a = frameTensor E S a + frameTensor E T a := by
  simp only [frameTensor, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem frameTensor_const_mul {n : ℕ} (E : Mat4) (r : ℝ)
    (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor E (fun b => r * T b) a = r * frameTensor E T a := by
  simp only [frameTensor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem frameTensor_sum {n : ℕ} {ι : Type*} [Fintype ι] (E : Mat4)
    (F : ι → CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor E (fun b => ∑ k, F k b) a = ∑ k, frameTensor E (F k) a := by
  simp only [frameTensor, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem tensorSlotAction_const_mul {n : ℕ} (A : Mat4) (r : ℝ)
    (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    tensorSlotAction A (fun b => r * T b) a = r * tensorSlotAction A T a := by
  simp only [tensorSlotAction, covariantSlotAction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorSlotAction_sum {n : ℕ} {ι : Type*} [Fintype ι] (A : Mat4)
    (F : ι → CovariantCoordinates n) (a : Fin n → Fin 4) :
    tensorSlotAction A (fun b => ∑ k, F k b) a = ∑ k, tensorSlotAction A (F k) a := by
  simp only [tensorSlotAction, covariantSlotAction, Finset.mul_sum]
  calc
    _ = ∑ s, ∑ k, ∑ b, A b (a s) * F k (Function.update a s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem tensorSlotAction_cons {n : ℕ} (A : Mat4)
    (T : CovariantCoordinates (n + 1)) (i : Fin 4) (a : Fin n → Fin 4) :
    tensorSlotAction A T (Fin.cons i a) =
      (∑ b, A b i * T (Fin.cons b a)) +
        tensorSlotAction A (fun w => T (Fin.cons i w)) a := by
  simp only [tensorSlotAction, covariantSlotAction, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]

theorem intertwining_pairing (E A B : Mat4) (h : A * E = E * B)
    (f : Fin 4 → ℝ) (i : Fin 4) :
    (∑ b, E b i * ∑ c, A c b * f c) =
      ∑ b, B b i * ∑ c, E c b * f c := by
  calc
    _ = ∑ c, (A * E) c i * f c := by
      simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ c, (E * B) c i * f c := by rw [h]
    _ = _ := by
      simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring

/-- An intertwining frame acts simultaneously on every covariant slot.
The proof uses one fresh slot at a time, so no large coordinate sum is expanded. -/
theorem frameTensor_slotAction_intertwine (E A B : Mat4) (h : A * E = E * B)
    {n : ℕ} (T : CovariantCoordinates n) :
    frameTensor E (tensorSlotAction A T) = tensorSlotAction B (frameTensor E T) := by
  induction n with
  | zero =>
    funext a
    simp [tensorSlotAction, frameTensor]
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) : CovariantCoordinates n := fun w => T (Fin.cons b w)
    have hT (b : Fin 4) :
        (fun w => tensorSlotAction A T (Fin.cons b w)) =
          (fun w => ∑ c, A c b * F c w) + tensorSlotAction A (F b) := by
      funext w
      exact tensorSlotAction_cons A T b w
    have hL (b : Fin 4) :
        frameTensor E (fun w => tensorSlotAction A T (Fin.cons b w)) v =
          (∑ c, A c b * frameTensor E (F c) v) +
            tensorSlotAction B (frameTensor E (F b)) v := by
      rw [hT, frameTensor_add, frameTensor_sum]
      simp only [frameTensor_const_mul]
      rw [ih (F b)]
    have hR :
        tensorSlotAction B (fun w => frameTensor E T (Fin.cons i w)) v =
          ∑ b, E b i * tensorSlotAction B (frameTensor E (F b)) v := by
      have hf : (fun w => frameTensor E T (Fin.cons i w)) =
          fun w => ∑ b, E b i * frameTensor E (F b) w := by
        funext w
        exact frameTensor_cons E T i w
      rw [hf, tensorSlotAction_sum]
      simp only [tensorSlotAction_const_mul]
    rw [frameTensor_cons, tensorSlotAction_cons]
    simp only [hL, mul_add, Finset.sum_add_distrib]
    rw [hR]
    congr 1
    simp only [frameTensor_cons]
    exact intertwining_pairing E A B h (fun c => frameTensor E (F c) v) i

theorem frameTensor_slotAction {n : ℕ} (E A : Mat4) (hE : IsUnit E.det)
    (T : CovariantCoordinates n) :
    frameTensor E (tensorSlotAction A T) =
      tensorSlotAction (E⁻¹ * A * E) (frameTensor E T) := by
  apply frameTensor_slotAction_intertwine
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv E hE, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the actual covariant slot action with two-form matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

/-- The bilinear two-form contraction defining each Weyl block entry. -/
def twoFormPairing (T : CovariantCoordinates 4) (P Q : Mat4) : ℝ :=
  (1 / 8 : ℝ) * ∑ a, ∑ b, ∑ c, ∑ d, T ![a, b, d, c] * P a b * Q c d

theorem twoFormPairing_add_tensor (S T : CovariantCoordinates 4) (P Q : Mat4) :
    twoFormPairing (S + T) P Q = twoFormPairing S P Q + twoFormPairing T P Q := by
  simp only [twoFormPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem twoFormPairing_add_left (T : CovariantCoordinates 4) (P R Q : Mat4) :
    twoFormPairing T (P + R) Q = twoFormPairing T P Q + twoFormPairing T R Q := by
  simp only [twoFormPairing, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem twoFormPairing_add_right (T : CovariantCoordinates 4) (P Q R : Mat4) :
    twoFormPairing T P (Q + R) = twoFormPairing T P Q + twoFormPairing T P R := by
  simp only [twoFormPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem updateFour_0 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 0 x = ![x, b, d, c] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot0 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 0 A T) P Q =
      twoFormPairing T (A * P) Q := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_0,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap0]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

theorem updateFour_1 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 1 x = ![a, x, d, c] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot1 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 1 A T) P Q =
      twoFormPairing T (P * Aᵀ) Q := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_1,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap1]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

theorem updateFour_2 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 2 x = ![a, b, x, c] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot2 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 2 A T) P Q =
      twoFormPairing T P (Q * Aᵀ) := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_2,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap3]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

theorem updateFour_3 (a b c d x : Fin 4) :
    Function.update ![a, b, d, c] 3 x = ![a, b, d, x] := by
  funext i
  fin_cases i <;> simp

theorem twoFormPairing_slot3 (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (covariantSlotAction 3 A T) P Q =
      twoFormPairing T P (A * Q) := by
  unfold twoFormPairing
  congr 1
  simp only [covariantSlotAction, updateFour_3,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFive_swap2]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

/-- Contracting all four covariant slots acts on each two-form factor. -/
theorem twoFormPairing_slotAction (A : Mat4) (T : CovariantCoordinates 4)
    (P Q : Mat4) :
    twoFormPairing (tensorSlotAction A T) P Q =
      twoFormPairing T (A * P + P * Aᵀ) Q +
        twoFormPairing T P (Q * Aᵀ + A * Q) := by
  have hT : tensorSlotAction A T = covariantSlotAction 0 A T +
      covariantSlotAction 1 A T + covariantSlotAction 2 A T + covariantSlotAction 3 A T := by
    funext a
    simp only [tensorSlotAction, Fin.sum_univ_four, Pi.add_apply]
  rw [hT]
  simp only [twoFormPairing_add_tensor, twoFormPairing_slot0,
    twoFormPairing_slot1, twoFormPairing_slot2, twoFormPairing_slot3,
    twoFormPairing_add_left, twoFormPairing_add_right]
  ring

theorem twoFormPairing_skew_slotAction (A : Mat4) (hA : Aᵀ = -A)
    (T : CovariantCoordinates 4) (P Q : Mat4) :
    twoFormPairing (tensorSlotAction A T) P Q =
      twoFormPairing T (A * P - P * A) Q +
        twoFormPairing T P (A * Q - Q * A) := by
  rw [twoFormPairing_slotAction, hA, Matrix.mul_neg, Matrix.mul_neg]
  have he : -(Q * A) + A * Q = A * Q - Q * A := by
    abel
  rw [he]
  rfl


theorem twoFormPairing_smul_left (T : CovariantCoordinates 4) (P Q : Mat4) (r : ℝ) :
    twoFormPairing T (r • P) Q = r * twoFormPairing T P Q := by
  simp only [twoFormPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoFormPairing_smul_right (T : CovariantCoordinates 4) (P Q : Mat4) (r : ℝ) :
    twoFormPairing T P (r • Q) = r * twoFormPairing T P Q := by
  simp only [twoFormPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoFormPairing_zero_left (T : CovariantCoordinates 4) (Q : Mat4) :
    twoFormPairing T 0 Q = 0 := by simp [twoFormPairing]

theorem twoFormPairing_zero_right (T : CovariantCoordinates 4) (P : Mat4) :
    twoFormPairing T P 0 = 0 := by simp [twoFormPairing]

theorem blockCoordinates_pairing (T : CovariantCoordinates 4) (Q : Fin 3 → Mat4)
    (a b : Fin 3) : blockCoordinates T Q a b = twoFormPairing T (Q a) (Q b) := by
  simp only [blockCoordinates, curvatureBlock, twoFormPairing, Fintype.sum_prod_type]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Einstein curvature Hessian has zero Ricci contraction.
The first Ricci contraction vanishes on an open chart before differentiating. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Put the two contracted curvature slots into the row/column positions. -/
def fiveTensorMatrix (T : FourSpace → CovariantCoordinates 5)
    (a j k : Fin 4) (z : FourSpace) : Mat4 :=
  fun p q => T z ![a, q, j, k, p]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternion basis converts the actual four covector actions into
the matrix commutator used by the Weyl block equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem quaternion_generator_commutator (s r : Fin 3) :
    quaternionMatrix s * quaternionMatrix r - quaternionMatrix r * quaternionMatrix s =
      ∑ k, rotation s k r • quaternionMatrix k := by
  have h := QuaternionFrame.imaginaryLeft_commutator s (Pi.single r (1 : ℝ))
  simpa [QuaternionFrame.imaginaryCombination, Matrix.mulVec, dotProduct, Pi.single_apply] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature endomorphism acts on the quaternionic Weyl block.
This is a finite contraction of the full tensor, before any diagonalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem twoFormPairing_smul_tensor (T : CovariantCoordinates 4)
    (P Q : Mat4) (r : ℝ) :
    twoFormPairing (r • T) P Q = r * twoFormPairing T P Q := by
  simp only [twoFormPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

/-- The fixed two-form contraction is linear in the four-tensor. -/
def blockCoordinatesLinear (Q : Fin 3 → Mat4) : CovariantCoordinates 4 →ₗ[ℝ] Mat3 where
  toFun T := blockCoordinates T Q
  map_add' S T := by
    ext a b
    simpa only [blockCoordinates_pairing, Matrix.add_apply] using
      twoFormPairing_add_tensor S T (Q a) (Q b)
  map_smul' r T := by
    ext a b
    simpa only [blockCoordinates_pairing, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply] using
      twoFormPairing_smul_tensor T (Q a) (Q b) r

/-- Slots are arranged as the endomorphism `R(e_i,e_j)` on vectors. -/
def curvatureEndomorphism (R : Angular.CurvatureArray) (i j : Fin 4) : Mat4 :=
  fun a b => R i j b a

theorem curvatureEndomorphism_blockTensor (A : Mat3) (Q : Fin 3 → Mat4)
    (i j : Fin 4) :
    curvatureEndomorphism (Angular.blockTensor A Q) i j =
      (1 / 2 : ℝ) • ∑ r, ∑ s, (A r s * Q r i j) • Q s := by
  ext a b
  simp only [curvatureEndomorphism, Angular.blockTensor, Angular.twoFormProduct,
    Pi.smul_apply, Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem tensorSlotAction_smul_matrix {n : ℕ} (r : ℝ) (A : Mat4)
    (T : CovariantCoordinates n) :
    tensorSlotAction (r • A) T = r • tensorSlotAction A T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorSlotAction_sum_matrix {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Mat4) (T : CovariantCoordinates n) :
    tensorSlotAction (∑ r, A r) T = ∑ r, tensorSlotAction (A r) T := by
  funext a
  simp only [tensorSlotAction, covariantSlotAction, Finset.sum_apply, Matrix.sum_apply,
    Finset.sum_mul]
  calc
    _ = ∑ s, ∑ r, ∑ b, A r b (a s) * T (Function.update a s b) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic first Bianchi survives a second covariant derivative.
Only an identity on the open chart is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameHessian_firstBianchi (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d a, AlgebraicCurvature.FirstBianchi (curvatureHessianArray T d a))
    (d a : Fin 4) : AlgebraicCurvature.FirstBianchi
      (curvatureHessianArray (frameTensor E T) d a) := by
  intro i j k l
  change frameTensor E T (Fin.cons d ![a, i, j, k, l]) +
    frameTensor E T (Fin.cons d ![a, j, k, i, l]) +
    frameTensor E T (Fin.cons d ![a, k, i, j, l]) = 0
  rw [frameTensor_cons E T d ![a, i, j, k, l],
    frameTensor_cons E T d ![a, j, k, i, l], frameTensor_cons E T d ![a, k, i, j, l],
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  have hb := frameTensor_firstBianchi E (fun w => T (Fin.cons b w)) (h b) a i j k l
  simp only [curvatureDerivativeArray] at hb
  linear_combination E b d * hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Ricci commutator is transported in its two derivative slots and
all covariant tensor slots by the same actual frame matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem frameTensor_sub {n : ℕ} (E : Mat4) (S T : CovariantCoordinates n)
    (a : Fin n → Fin 4) :
    frameTensor E (S - T) a = frameTensor E S a - frameTensor E T a := by
  simp only [frameTensor, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem frameTensor_two_prefix {n : ℕ} (E : Mat4)
    (X : CovariantCoordinates (n + 1 + 1)) (i j : Fin 4) (a : Fin n → Fin 4) :
    frameTensor E X (Fin.cons i (Fin.cons j a)) =
      ∑ p, ∑ q, (E p i * E q j) *
        frameTensor E (fun b => X (Fin.cons p (Fin.cons q b))) a := by
  rw [frameTensor_cons]
  simp only [frameTensor_cons, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Pull back the two tangent arguments of the curvature endomorphism. -/
def pulledCurvatureEndomorphism (E : Mat4) (C : Fin 4 → Fin 4 → Mat4)
    (i j : Fin 4) : Mat4 :=
  ∑ p, ∑ q, (E p i * E q j) • C p q

/-- This is purely finite tensor algebra; the actual coordinate curvature
commutator supplies `hX` in the geometric specialization. -/
theorem framed_tensor_commutator {n : ℕ} (E : Mat4) (hE : IsUnit E.det)
    (C : Fin 4 → Fin 4 → Mat4) (T : CovariantCoordinates n)
    (X : CovariantCoordinates (n + 1 + 1))
    (hX : ∀ p q a, X (Fin.cons p (Fin.cons q a)) -
      X (Fin.cons q (Fin.cons p a)) = -tensorSlotAction (C p q) T a)
    (i j : Fin 4) (a : Fin n → Fin 4) :
    frameTensor E X (Fin.cons i (Fin.cons j a)) -
      frameTensor E X (Fin.cons j (Fin.cons i a)) =
        -tensorSlotAction
          (E⁻¹ * pulledCurvatureEndomorphism E C i j * E) (frameTensor E T) a := by
  have hswap :
      (∑ p, ∑ q, (E p j * E q i) *
        frameTensor E (fun b => X (Fin.cons p (Fin.cons q b))) a) =
      ∑ p, ∑ q, (E p i * E q j) *
        frameTensor E (fun b => X (Fin.cons q (Fin.cons p b))) a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hd (p q : Fin 4) :
      (fun b => X (Fin.cons p (Fin.cons q b))) -
        (fun b => X (Fin.cons q (Fin.cons p b))) = -tensorSlotAction (C p q) T := by
    funext b
    exact hX p q b
  have hsum : tensorSlotAction (pulledCurvatureEndomorphism E C i j) T =
      fun b => ∑ p, ∑ q, (E p i * E q j) * tensorSlotAction (C p q) T b := by
    simp only [pulledCurvatureEndomorphism, tensorSlotAction_sum_matrix,
      tensorSlotAction_smul_matrix]
    rfl
  calc
    _ = ∑ p, ∑ q, (E p i * E q j) *
        frameTensor E ((fun b => X (Fin.cons p (Fin.cons q b))) -
          (fun b => X (Fin.cons q (Fin.cons p b)))) a := by
      rw [frameTensor_two_prefix, frameTensor_two_prefix, hswap]
      simp only [frameTensor_sub, mul_sub, Finset.sum_sub_distrib]
    _ = -(∑ p, ∑ q, (E p i * E q j) *
        frameTensor E (tensorSlotAction (C p q) T) a) := by
      simp only [hd, frameTensor_neg, mul_neg, Finset.sum_neg_distrib]
    _ = -frameTensor E (tensorSlotAction (pulledCurvatureEndomorphism E C i j) T) a := by
      rw [hsum, frameTensor_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact (frameTensor_const_mul E (E p i * E q j) (tensorSlotAction (C p q) T) a).symm
    _ = _ := by rw [frameTensor_slotAction E _ hE]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-four curvature commutator on the positive Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem metric_pairing_apply (E G : Mat4) (i j : Fin 4) :
    (Eᵀ * G * E) i j = ∑ p, ∑ q, E p i * G p q * E q j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem unit_product_first (E G : Mat4) (i j k l : Fin 4) :
    (∑ p, ∑ q, ∑ r, ∑ s,
      E p i * E q j * E r k * E s l * (G q r * G p s)) =
      (Eᵀ * G * E) i l * (Eᵀ * G * E) j k := by
  simp only [metric_pairing_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFour_BCAD]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem unit_product_second (E G : Mat4) (i j k l : Fin 4) :
    (∑ p, ∑ q, ∑ r, ∑ s,
      E p i * E q j * E r k * E s l * (G p r * G q s)) =
      (Eᵀ * G * E) i k * (Eᵀ * G * E) j l := by
  simp only [metric_pairing_apply, Finset.sum_mul, Finset.mul_sum]
  rw [sumFour_BDAC]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameTensor_unitCurvature (e : OrthonormalFrame g c) :
    frameTensor e.matrix
      (unitCurvatureCoordinates g c (chartAt FourSpace c c)) = unitFrameTensor := by
  funext a
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ s, e.matrix p (a 0) * e.matrix q (a 1) *
      e.matrix r (a 2) * e.matrix s (a 3) *
      (chartMetric g c q r * chartMetric g c p s -
        chartMetric g c p r * chartMetric g c q s)) = _
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [unit_product_first, unit_product_second, e.orthonormal]
  simp only [unitFrameTensor, Matrix.one_apply]
  dsimp
  congr 1
  exact mul_comm _ _

theorem frameTensor_curvatureCoordinates (e : OrthonormalFrame g c)
    (i j k l : Fin 4) :
    frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)) ![i,j,k,l] =
      frameCurvature g c e i j k l := by
  rw [frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ b, e.matrix p i * e.matrix q j * e.matrix r k *
    e.matrix b l * (∑ a, chartMetric g c a b *
      curvatureComponent g c (chartAt FourSpace c c) a p q r)) = _
  simp only [Finset.mul_sum]
  rw [sumFive_moveLast]
  unfold frameCurvature
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ b, ∑ p, ∑ q, ∑ r,
        e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l *
          (chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r) := by
      rw [sumFour_moveLast]
    _ = _ := by
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ring

theorem unitFrameTensor_pairing (P Q : Mat4)
    (hQ : Qᵀ = -Q) : twoFormPairing unitFrameTensor P Q =
      (1 / 4 : ℝ) * ∑ a, ∑ b, P a b * Q a b := by
  have hq (a b : Fin 4) : Q b a = -Q a b := congrArg (fun A : Mat4 => A a b) hQ
  change (1 / 8 : ℝ) * (∑ a, ∑ b, ∑ c, ∑ d,
    ((if b = d then (1 : ℝ) else 0) * (if a = c then 1 else 0) -
      (if a = d then 1 else 0) * (if b = c then 1 else 0)) * P a b * Q c d) = _
  simp only [sub_mul, mul_ite, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, ite_self, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const_zero]
  have hcross : (∑ a, ∑ b, P a b * Q b a) = -(∑ a, ∑ b, P a b * Q a b) := by
    calc
      _ = ∑ a, ∑ b, -(P a b * Q a b) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hq a b]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  rw [hcross]
  ring

theorem OrthonormalFrame.inverse_eq_transpose_metric (e : OrthonormalFrame g c) :
    e.matrix⁻¹ = e.matrixᵀ * chartMetric g c := by
  have h := congrArg (fun A : Mat4 => A * e.matrix⁻¹) e.orthonormal
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr e.det_ne_zero),
    mul_one, one_mul] at h
  exact h.symm

/-- The matrix in the framed covector action is exactly the metric's
curvature endomorphism evaluated on that orthonormal frame. -/
theorem frame_curvatureEndomorphism (e : OrthonormalFrame g c) (i j : Fin 4) :
    e.matrix⁻¹ * pulledCurvatureEndomorphism e.matrix
      (fun p q => coordinateCurvatureMatrix g c p q (chartAt FourSpace c c)) i j * e.matrix =
        curvatureEndomorphism (frameCurvature g c e) i j := by
  rw [e.inverse_eq_transpose_metric]
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pulledCurvatureEndomorphism,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    coordinateCurvatureMatrix_apply, curvatureEndomorphism, frameCurvature]
  rw [sumFive_moveFirst, sumFour_pairSwap]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  have hs (v w : Fin 4) : chartMetric g c w v = chartMetric g c v w := by
    exact g.symm _ _ _
  rw [hs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual cyclic second Bianchi identity preserves
its derivative and curvature slots, before passage to an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameHessian_differentialBianchi (E : Mat4) (T : CovariantCoordinates 6)
    (h : ∀ d, AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (fun b => T (Fin.cons d b)))) (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (fun b => frameTensor E T (Fin.cons d b))) := by
  intro a i j k l
  change frameTensor E T (Fin.cons d ![a, i, j, k, l]) +
    frameTensor E T (Fin.cons d ![i, j, a, k, l]) +
    frameTensor E T (Fin.cons d ![j, a, i, k, l]) = 0
  rw [frameTensor_cons E T d ![a, i, j, k, l],
    frameTensor_cons E T d ![i, j, a, k, l], frameTensor_cons E T d ![j, a, i, k, l],
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  have hb := frameTensor_differentialBianchi E (fun w => T (Fin.cons b w))
    (h b) a i j k l
  simp only [curvatureDerivativeArray] at hb
  linear_combination E b d * hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation of a finite covariant tensor pullback. Rank induction
keeps the product rule and connection cancellation small at ranks four
through seven used by the actual Weyl fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

/-- First variation in the frame matrix, adding one covariant slot at a time. -/
def frameVariation : {n : ℕ} → Mat4 → Mat4 → CovariantCoordinates n →
    CovariantCoordinates n
  | 0, _, _, _ => 0
  | _n + 1, E, P, T => fun a =>
      (∑ b, P b (a 0) * frameTensor E (fun v => T (Fin.cons b v)) (fun k => a k.succ)) +
      ∑ b, E b (a 0) * frameVariation E P (fun v => T (Fin.cons b v)) (fun k => a k.succ)

theorem frameVariation_cons {n : ℕ} (E P : Mat4)
    (T : CovariantCoordinates (n + 1)) (i : Fin 4) (a : Fin n → Fin 4) :
    frameVariation E P T (Fin.cons i a) =
      (∑ b, P b i * frameTensor E (fun v => T (Fin.cons b v)) a) +
      ∑ b, E b i * frameVariation E P (fun v => T (Fin.cons b v)) a := rfl

theorem connection_pairing (E P U C : Mat4) (h : E * C = P + U * E)
    (f : Fin 4 → ℝ) (i : Fin 4) :
    (∑ b, P b i * f b) + (∑ b, E b i * ∑ c, U c b * f c) =
      ∑ b, C b i * ∑ c, E c b * f c := by
  have hp : (∑ b, E b i * ∑ c, U c b * f c) =
      ∑ c, (U * E) c i * f c := by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  have hc : (∑ b, C b i * ∑ c, E c b * f c) =
      ∑ c, (E * C) c i * f c := by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  rw [hp, hc, h]
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The derivative of the frame precisely cancels the difference between
the source and target connection coefficients. -/
theorem frameVariation_connection {n : ℕ} (E P U C : Mat4)
    (h : E * C = P + U * E) (T : CovariantCoordinates n) :
    frameVariation E P T + frameTensor E (tensorSlotAction U T) =
      tensorSlotAction C (frameTensor E T) := by
  induction n with
  | zero =>
    funext a
    simp [frameVariation, tensorSlotAction, frameTensor]
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) : CovariantCoordinates n := fun w => T (Fin.cons b w)
    have hU (b : Fin 4) :
        frameTensor E (fun w => tensorSlotAction U T (Fin.cons b w)) v =
          (∑ c, U c b * frameTensor E (F c) v) +
            frameTensor E (tensorSlotAction U (F b)) v := by
      have he : (fun w => tensorSlotAction U T (Fin.cons b w)) =
          (fun w => ∑ c, U c b * F c w) + tensorSlotAction U (F b) := by
        funext w
        exact tensorSlotAction_cons U T b w
      rw [he, frameTensor_add, frameTensor_sum]
      simp only [frameTensor_const_mul]
    have hC : tensorSlotAction C (fun w => frameTensor E T (Fin.cons i w)) v =
        ∑ b, E b i * tensorSlotAction C (frameTensor E (F b)) v := by
      have he : (fun w => frameTensor E T (Fin.cons i w)) =
          fun w => ∑ b, E b i * frameTensor E (F b) w := by
        funext w
        exact frameTensor_cons E T i w
      rw [he, tensorSlotAction_sum]
      simp only [tensorSlotAction_const_mul]
    have hV (b : Fin 4) : frameVariation E P (F b) v +
        frameTensor E (tensorSlotAction U (F b)) v =
          tensorSlotAction C (frameTensor E (F b)) v := congrFun (ih (F b)) v
    change frameVariation E P T (Fin.cons i v) +
      frameTensor E (tensorSlotAction U T) (Fin.cons i v) = _
    rw [frameVariation_cons, frameTensor_cons, tensorSlotAction_cons]
    simp only [hU, mul_add, Finset.sum_add_distrib]
    rw [hC]
    have hsum := connection_pairing E P U C h (fun b => frameTensor E (F b) v) i
    have hrem : (∑ b, E b i * frameVariation E P (F b) v) +
        (∑ b, E b i * frameTensor E (tensorSlotAction U (F b)) v) =
          ∑ b, E b i * tensorSlotAction C (frameTensor E (F b)) v := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← mul_add, hV b]
    simp only [frameTensor_cons]
    linarith only [hsum, hrem]

theorem frameTensor_differentiableAt {n : ℕ} (E : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hE : ∀ i j, DifferentiableAt ℝ (fun w => E w i j) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (a : Fin n → Fin 4) :
    DifferentiableAt ℝ (fun w => frameTensor (E w) (T w) a) z := by
  unfold frameTensor
  apply DifferentiableAt.fun_sum
  intro b _
  exact (HasFDerivAt.finsetProd (fun k _ => (hE (b k) (a k)).hasFDerivAt)).differentiableAt.mul
    (hT b)

theorem pullback_partial_sum {ι : Type*} [Fintype ι]
    (F : ι → FourSpace → ℝ) (z : FourSpace)
    (hF : ∀ a, DifferentiableAt ℝ (F a) z) (i : Fin 4) :
    partialDeriv (fun w => ∑ a, F a w) i z = ∑ a, partialDeriv (F a) i z := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun a _ => hF a), _root_.sum_apply]

theorem pullback_partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem tensorPartial_frameTensor {n : ℕ} (E : FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hE : ∀ i j, DifferentiableAt ℝ (fun w => E w i j) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) (i : Fin 4) :
    tensorPartial (fun w => frameTensor (E w) (T w)) i z =
      frameVariation (E z) (matrixPartial E i z) (T z) +
        frameTensor (E z) (tensorPartial T i z) := by
  induction n with
  | zero =>
    funext a
    simp [tensorPartial, frameTensor, frameVariation]
  | succ n ih =>
    funext a
    obtain ⟨j, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) (w : FourSpace) : CovariantCoordinates n := fun a => T w (Fin.cons b a)
    have hF (b : Fin 4) (a : Fin n → Fin 4) :
        DifferentiableAt ℝ (fun w => F b w a) z := hT _
    have hprod (b : Fin 4) : DifferentiableAt ℝ
        (fun w => E w b j * frameTensor (E w) (F b w) v) z :=
      (hE b j).mul (frameTensor_differentiableAt E (F b) z hE (hF b) v)
    have hd (b : Fin 4) :
        partialDeriv (fun w => E w b j * frameTensor (E w) (F b w) v) i z =
          matrixPartial E i z b j * frameTensor (E z) (F b z) v +
            E z b j * (frameVariation (E z) (matrixPartial E i z) (F b z) v +
              frameTensor (E z) (tensorPartial (F b) i z) v) := by
      rw [pullback_partial_mul (hE b j)
        (frameTensor_differentiableAt E (F b) z hE (hF b) v)]
      have hv := congrFun (ih (F b) (hF b)) v
      change partialDeriv (fun w => E w b j) i z * _ + E z b j * _ = _
      rw [show partialDeriv (fun w => frameTensor (E w) (F b w) v) i z = _ from hv]
      rfl
    change partialDeriv (fun w => frameTensor (E w) (T w) (Fin.cons j v)) i z = _
    simp only [frameTensor_cons]
    rw [pullback_partial_sum _ z hprod i]
    simp only [hd, frameVariation_cons, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      frameTensor_cons, tensorPartial, F]
    simp only [add_assoc]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-five commutator includes the curvature action on the
leading covector slot of the Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem gradientBlock_negative_slotAction (B : Mat4) (T : CovariantCoordinates 5)
    (Q : Fin 3 → Mat4) (j : Fin 4) :
    gradientBlock (-tensorSlotAction B T) Q j =
      blockCoordinates (-tensorSlotAction B (fun a => T (Fin.cons j a))) Q -
        ∑ r, B r j • gradientBlock T Q r := by
  have hT : (fun a => (-tensorSlotAction B T) (Fin.cons j a)) =
      -tensorSlotAction B (fun a => T (Fin.cons j a)) -
        ∑ r, B r j • (fun a => T (Fin.cons r a)) := by
    funext a
    simp only [Pi.neg_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [tensorSlotAction_cons]
    ring
  have hh := congrArg (blockCoordinatesLinear Q) hT
  rw [map_sub, map_sum] at hh
  simp only [map_smul] at hh
  exact hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-frame changes and their exact Frobenius invariants. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- Coordinates of the second frame in the first. -/
def OrthonormalFrame.changeMatrix (e f : OrthonormalFrame g c) : Mat4 :=
  e.matrix⁻¹ * f.matrix

theorem OrthonormalFrame.mul_changeMatrix (e f : OrthonormalFrame g c) :
    e.matrix * e.changeMatrix f = f.matrix := by
  rw [OrthonormalFrame.changeMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr e.det_ne_zero), Matrix.one_mul]

theorem OrthonormalFrame.changeMatrix_orthogonal (e f : OrthonormalFrame g c) :
    (e.changeMatrix f)ᵀ * e.changeMatrix f = 1 := by
  calc
    _ = (e.changeMatrix f)ᵀ * (e.matrixᵀ * chartMetric g c * e.matrix) *
        e.changeMatrix f := by rw [e.orthonormal, Matrix.mul_one]
    _ = (e.matrix * e.changeMatrix f)ᵀ * chartMetric g c *
        (e.matrix * e.changeMatrix f) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [e.mul_changeMatrix f]; exact f.orthonormal

theorem OrthonormalFrame.changeMatrix_first (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) (i : Fin 4) :
    e.changeMatrix f i 0 = if i = 0 then 1 else 0 := by
  have hcol (j : Fin 4) : f.matrix j 0 = e.matrix j 0 := by
    exact (congrArg (fun v : FourSpace => v j) hfirst).symm
  have h := congrArg (fun A : Mat4 => A i 0)
    (Matrix.nonsing_inv_mul e.matrix (isUnit_iff_ne_zero.mpr e.det_ne_zero))
  simpa only [OrthonormalFrame.changeMatrix, Matrix.mul_apply, hcol,
    Matrix.one_apply] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiate the proved Weyl Hessian commutator along parallel frames.
Only the ordinary derivative identities already present in the flow data are used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance parallelInnerNormedRing : NormedRing Mat := Matrix.frobeniusNormedRing
local instance parallelInnerNormedSpace : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

local instance parallelInnerNormedAlgebra_r73e4b7_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def matrixActionLinear (s : Fin 3) : Mat →ₗ[ℝ] Mat where
  toFun A := matrixAction s A
  map_add' A B := by
    ext a b
    simp only [matrixAction, Matrix.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  map_smul' r A := by
    ext a b
    simp only [matrixAction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring

def matrixActionCLM (s : Fin 3) : Mat →L[ℝ] Mat :=
  (matrixActionLinear s).toContinuousLinearMap

def matrixEntryLinear (a b : Fin 3) : Mat →ₗ[ℝ] ℝ where
  toFun A := A a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixEntryCLM (a b : Fin 3) : Mat →L[ℝ] ℝ :=
  (matrixEntryLinear a b).toContinuousLinearMap

theorem hasDerivAt_matrixAction {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) (s : Fin 3) :
    HasDerivAt (fun r => matrixAction s (T r)) (matrixAction s Z) t := by
  exact (matrixActionCLM s).hasFDerivAt.comp_hasDerivAt t hT

theorem parallel_hasDerivAt_entry {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) (a b : Fin 3) :
    HasDerivAt (fun r => T r a b) (Z a b) t := by
  exact (matrixEntryCLM a b).hasFDerivAt.comp_hasDerivAt t hT

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rotation of the actual first curvature derivative, including its
covector direction, before either Weyl block is contracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

/-- Successive pullbacks act by the product of their frame matrices. -/
theorem frameTensor_mul {n : ℕ} (E P : Mat4) (T : CovariantCoordinates n) :
    frameTensor (E * P) T = frameTensor P (frameTensor E T) := by
  induction n with
  | zero =>
    funext a
    rw [frameTensor_zero, frameTensor_zero, frameTensor_zero]
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) : CovariantCoordinates n := fun w => T (Fin.cons b w)
    have hs (d : Fin 4) :
        (fun w => frameTensor E T (Fin.cons d w)) =
          fun w => ∑ b, E b d * frameTensor E (F b) w := by
      funext w
      exact frameTensor_cons E T d w
    rw [frameTensor_cons, frameTensor_cons]
    simp only [hs, frameTensor_sum, frameTensor_const_mul]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (F b)]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Euclidean tensor pairing is unchanged by an orthogonal frame change. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem orthogonal_covector_pairing (P : Mat4) (hP : P * Pᵀ = 1)
    (x y : Fin 4 → ℝ) :
    (∑ i, (∑ a, P a i * x a) * (∑ b, P b i * y b)) = ∑ a, x a * y a := by
  have hg (a b : Fin 4) : (∑ i, P a i * P b i) = if a = b then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun A : Mat4 => A a b) hP
  calc
    _ = ∑ a, ∑ b, (∑ i, P a i * P b i) * (x b * y a) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [hg, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]

theorem frameTensor_pairing_orthogonal {n : ℕ} (P : Mat4) (hP : P * Pᵀ = 1)
    (T U : CovariantCoordinates n) :
    frameTensorPairing (frameTensor P T) (frameTensor P U) = frameTensorPairing T U := by
  induction n with
  | zero =>
    simp only [frameTensorPairing, frameTensor_zero]
  | succ n ih =>
    unfold frameTensorPairing
    rw [sum_tensor_indices_cons, sum_tensor_indices_cons]
    simp only [frameTensor_cons]
    calc
      _ = ∑ a : Fin n → Fin 4, ∑ i,
          (∑ b, P b i * frameTensor P (fun w => T (Fin.cons b w)) a) *
            (∑ b, P b i * frameTensor P (fun w => U (Fin.cons b w)) a) :=
        Finset.sum_comm
      _ = ∑ a : Fin n → Fin 4, ∑ b,
          frameTensor P (fun w => T (Fin.cons b w)) a *
            frameTensor P (fun w => U (Fin.cons b w)) a := by
        apply Finset.sum_congr rfl
        intro a _
        exact orthogonal_covector_pairing P hP _ _
      _ = ∑ b, ∑ a : Fin n → Fin 4,
          frameTensor P (fun w => T (Fin.cons b w)) a *
            frameTensor P (fun w => U (Fin.cons b w)) a := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        exact ih (fun w => T (Fin.cons b w)) (fun w => U (Fin.cons b w))

theorem frameTensor_norm_orthogonal {n : ℕ} (P : Mat4) (hP : P * Pᵀ = 1)
    (T : CovariantCoordinates n) :
    frameTensorSquareNorm (frameTensor P T) = frameTensorSquareNorm T :=
  frameTensor_pairing_orthogonal P hP T T

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameTensor_norm_same_base {n : ℕ} (e f : OrthonormalFrame g c)
    (T : CovariantCoordinates n) :
    frameTensorSquareNorm (frameTensor e.matrix T) =
      frameTensorSquareNorm (frameTensor f.matrix T) := by
  have hf : f.matrix = e.matrix * e.changeMatrix f := (e.mul_changeMatrix f).symm
  rw [hf, frameTensor_mul, frameTensor_norm_orthogonal _
    (mul_eq_one_comm.mp (e.changeMatrix_orthogonal f))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-dimensional two-form fiber and its actual Hodge involution.
The coordinate order is 01, 02, 03, 12, 13, 23. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormMatrix (a : TwoFormFour) : Mat4 :=
  !![0, a 0, a 1, a 2;
    -a 0, 0, a 3, a 4;
    -a 1, -a 3, 0, a 5;
    -a 2, -a 4, -a 5, 0]

theorem twoFormMatrix_skew (a : TwoFormFour) : (twoFormMatrix a)ᵀ = -twoFormMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix]

theorem twoFormMatrix_injective : Function.Injective twoFormMatrix := by
  intro a b hab
  ext i
  fin_cases i
  · exact congrFun (congrFun hab 0) 1
  · exact congrFun (congrFun hab 0) 2
  · exact congrFun (congrFun hab 0) 3
  · exact congrFun (congrFun hab 1) 2
  · exact congrFun (congrFun hab 1) 3
  · exact congrFun (congrFun hab 2) 3

end
end PositiveEinsteinFour.Geometry
end


section

/-! The individual Weyl norms descend to each oriented frame component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem frameTensor_one {n : ℕ} (T : CovariantCoordinates n) :
    frameTensor (1 : Mat4) T = T := by
  induction n with
  | zero =>
    funext a
    exact frameTensor_zero _ T a
  | succ n ih =>
    funext a
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    rw [frameTensor_cons]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, if_true]
    exact congrFun (ih (fun w => T (Fin.cons i w))) v

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- Two frames in the same oriented component have an orientation-preserving
orthogonal change matrix. -/
theorem OrthonormalFrame.changeMatrix_det_one (e f : OrthonormalFrame g c)
    (hor : 0 < e.matrix.det * f.matrix.det) : (e.changeMatrix f).det = 1 := by
  have hd := congrArg Matrix.det (e.mul_changeMatrix f)
  rw [Matrix.det_mul] at hd
  have hp : 0 < (e.matrix.det) ^ 2 * (e.changeMatrix f).det := by
    calc
      _ = e.matrix.det * f.matrix.det := by rw [← hd]; ring
      _ > 0 := hor
  have hpos : 0 < (e.changeMatrix f).det := by
    rcases mul_pos_iff.mp hp with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (sq_nonneg e.matrix.det)) h.1)
  have ho := congrArg Matrix.det (e.changeMatrix_orthogonal f)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at ho
  nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lowering the actual chart curvature transformation and pulling back
all four covariant slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def loweredMatrixTensor (G : Mat4) (R : Fin 4 → Fin 4 → Mat4) :
    CovariantCoordinates 4 := fun a => (G * R (a 0) (a 1)) (a 3) (a 2)

theorem lowered_matrix_transition (G H J : Mat4)
    (R S : Fin 4 → Fin 4 → Mat4) (hJ : IsUnit J.det)
    (hG : G = Jᵀ * H * J)
    (hR : ∀ i j, R i j = J⁻¹ * (∑ a, ∑ b, (J a i * J b j) • S a b) * J)
    (i j : Fin 4) :
    G * R i j = ∑ a, ∑ b, (J a i * J b j) • (Jᵀ * (H * S a b) * J) := by
  calc
    _ = Jᵀ * H * (J * J⁻¹) * (∑ a, ∑ b, (J a i * J b j) • S a b) * J := by
      rw [hG, hR]
      simp only [Matrix.mul_assoc]
    _ = Jᵀ * H * (∑ a, ∑ b, (J a i * J b j) • S a b) * J := by
      rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]

theorem loweredMatrixTensor_transition (G H J : Mat4)
    (R S : Fin 4 → Fin 4 → Mat4) (hJ : IsUnit J.det)
    (hG : G = Jᵀ * H * J)
    (hR : ∀ i j, R i j = J⁻¹ * (∑ a, ∑ b, (J a i * J b j) • S a b) * J) :
    loweredMatrixTensor G R = frameTensor J (loweredMatrixTensor H S) := by
  funext v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, frameTensor_four]
  change (G * R (v 0) (v 1)) (v 3) (v 2) = _
  rw [lowered_matrix_transition G H J R S hJ hG hR]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    loweredMatrixTensor]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  dsimp
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem loweredMatrixTensor_curvature (g : SmoothMetric M) (c : M) (z : FourSpace) :
    loweredMatrixTensor (metricInChart g c z)
      (fun i j => coordinateCurvatureMatrix g c i j z) = curvatureCoordinates g c z := by
  funext a
  simp only [loweredMatrixTensor, Matrix.mul_apply, coordinateCurvatureMatrix_apply,
    curvatureCoordinates]
  apply Finset.sum_congr rfl
  intro b _
  rw [show metricInChart g c z (a 3) b = metricInChart g c z b (a 3) from g.symm _ _ _]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Christoffel transformation transports the covariant derivative
of every finite covariant tensor.  This is used only at ranks four to seven. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem tensorPartial_comp {n : ℕ} (F : FourSpace → FourSpace)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hF : DifferentiableAt ℝ F z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (F z)) (i : Fin 4) :
    tensorPartial (fun w => T (F w)) i z =
      ∑ r, jacobianMatrix F z r i • tensorPartial T r (F z) := by
  funext a
  simpa only [tensorPartial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    partialDeriv_comp hF (hT a) i

theorem frameTensor_weighted_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (E : Mat4) (c : ι → ℝ) (T : ι → CovariantCoordinates n)
    (a : Fin n → Fin 4) :
    frameTensor E (∑ r, c r • T r) a = ∑ r, c r * frameTensor E (T r) a := by
  have he : (∑ r, c r • T r) = (fun b => ∑ r, c r * T r b) := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, frameTensor_sum]
  simp only [frameTensor_const_mul]

/-- Connection cancellation in one direction, before adding the derivative
slot to the tensor pullback. -/
theorem covariantDirection_pullback {n : ℕ}
    (F : FourSpace → FourSpace) (E : FourSpace → Mat4)
    (C D : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hF : DifferentiableAt ℝ F z)
    (hE : ∀ a b, DifferentiableAt ℝ (fun w => E w a b) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (F z))
    (hJ : E z = jacobianMatrix F z) (i : Fin 4)
    (hC : E z * C i z = matrixPartial E i z +
      (∑ r, E z r i • D r (F z)) * E z) :
    tensorCovariantDirection C (fun w => frameTensor (E w) (T (F w))) i z =
      frameTensor (E z) (∑ r, E z r i • tensorCovariantDirection D T r (F z)) := by
  have hcomp (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => T (F w) a) z := (hT a).comp z hF
  have hder := tensorPartial_frameTensor E (fun w => T (F w)) z hE hcomp i
  have hchain := tensorPartial_comp F T z hF hT i
  rw [← hJ] at hchain
  have hvar := frameVariation_connection (E z) (matrixPartial E i z)
    (∑ r, E z r i • D r (F z)) (C i z) hC (T (F z))
  have hslot : tensorSlotAction (∑ r, E z r i • D r (F z)) (T (F z)) =
      ∑ r, E z r i • tensorSlotAction (D r (F z)) (T (F z)) := by
    simp only [tensorSlotAction_sum_matrix, tensorSlotAction_smul_matrix]
  funext a
  have hv := congrFun hvar a
  change tensorPartial (fun w => frameTensor (E w) (T (F w))) i z a -
    tensorSlotAction (C i z) (frameTensor (E z) (T (F z))) a = _
  rw [hder, hchain]
  rw [hslot] at hv
  simp only [Pi.add_apply] at hv ⊢
  rw [frameTensor_weighted_sum] at hv
  rw [frameTensor_weighted_sum, frameTensor_weighted_sum]
  simp only [tensorCovariantDirection, frameTensor_sub, mul_sub, Finset.sum_sub_distrib]
  linarith only [hv]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem chart_overlap_eventually (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source := by
  have h₁ : ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).open_target.mem_nhds hz
  have h₂ : ∀ᶠ w in 𝓝 z,
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source :=
    ((chartAt FourSpace c).continuousAt_symm hz).eventually
      ((chartAt FourSpace d).open_source.mem_nhds hx)
  exact h₁.and h₂

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_inverse_moving_vector_smooth (c : M) (v : FourSpace → FourSpace)
    (hv : ContDiffOn ℝ ∞ v (chartAt FourSpace c).target) :
    ContMDiffOn I4 I4.tangent ∞
      (fun z => (⟨(chartAt FourSpace c).symm z,
        mfderiv I4 I4 (chartAt FourSpace c).symm z (v z)⟩ : TangentBundle I4 M))
      (chartAt FourSpace c).target := by
  have hphi : ContMDiffOn I4 I4 ∞ (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have ht := hphi.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt FourSpace c).open_target.uniqueMDiffOn
  have hv' : ContMDiffOn I4 I4.tangent ∞
      (fun z => (⟨z, v z⟩ : TangentBundle I4 FourSpace))
      (chartAt FourSpace c).target :=
    contMDiffOn_vectorSpace_iff_contDiffOn.mpr hv
  have hcomp := ht.comp hv' (fun z hz => hz)
  apply hcomp.congr
  intro z hz
  exact congrArg (fun L : TangentSpace I4 z →L[ℝ]
      TangentSpace I4 ((chartAt FourSpace c).symm z) =>
        (⟨(chartAt FourSpace c).symm z, L (v z)⟩ : TangentBundle I4 M))
    (mfderivWithin_of_isOpen (chartAt FourSpace c).open_target hz).symm

omit [IsManifold I4 ∞ M] in
theorem chartInverseMatrix_apply (c : M) (z : FourSpace) (u : CoordinateColumn) :
    WithLp.toLp 2 (chartInverseMatrix c z *ᵥ u) =
      mfderiv I4 I4 (chartAt FourSpace c).symm z (WithLp.toLp 2 u) := by
  let L : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  change WithLp.toLp 2 (chartInverseMatrix c z *ᵥ u) = L (WithLp.toLp 2 u)
  change WithLp.toLp 2 (fun i => ∑ j, L (coordinateVector j) i * u j) = _
  rw [← sum_coordinateVector u, map_sum]
  ext i
  simp only [map_smul, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frame_eq_of_matrix_eq_p0 {g : SmoothMetric M} {x : M}
    (e f : OrthonormalFrame g x)
    (h : e.matrix = f.matrix) : e = f := by
  cases e
  cases f
  cases h
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual changes of orthonormal frame on the six two-form coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix

noncomputable section

def twoFormExtract (A : Mat4) : TwoFormFour :=
  WithLp.toLp 2 ![A 0 1, A 0 2, A 0 3, A 1 2, A 1 3, A 2 3]

theorem twoFormExtract_matrix (a : TwoFormFour) : twoFormExtract (twoFormMatrix a) = a := by
  ext i
  fin_cases i <;> rfl

theorem twoFormMatrix_extract (A : Mat4) (hA : Aᵀ = -A) :
    twoFormMatrix (twoFormExtract A) = A := by
  have hs (i j : Fin 4) : A j i = -A i j := congrFun (congrFun hA i) j
  have hd (i : Fin 4) : A i i = 0 := by linarith [hs i i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix, twoFormExtract]
  all_goals first | exact (hd _).symm | exact (hs _ _).symm

def twoFormFrameAction (P : Mat4) (a : TwoFormFour) : TwoFormFour :=
  twoFormExtract (Pᵀ * twoFormMatrix a * P)

theorem twoFormMatrix_frameAction (P : Mat4) (a : TwoFormFour) :
    twoFormMatrix (twoFormFrameAction P a) = Pᵀ * twoFormMatrix a * P := by
  apply twoFormMatrix_extract
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, twoFormMatrix_skew,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem twoFormMatrix_add (a b : TwoFormFour) :
    twoFormMatrix (a + b) = twoFormMatrix a + twoFormMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix, add_comm]

theorem twoFormMatrix_smul (r : ℝ) (a : TwoFormFour) :
    twoFormMatrix (r • a) = r • twoFormMatrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix]

def twoFormFrameActionLinear (P : Mat4) : TwoFormFour →ₗ[ℝ] TwoFormFour where
  toFun := twoFormFrameAction P
  map_add' a b := by
    apply twoFormMatrix_injective
    simp only [twoFormMatrix_frameAction, twoFormMatrix_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r a := by
    apply twoFormMatrix_injective
    simp only [twoFormMatrix_frameAction, twoFormMatrix_smul, mul_smul_comm, smul_mul_assoc,
      RingHom.id_apply]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameOrientationContinuity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous frame curves stay in the same orientation component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- Orientation membership is constant along a continuous real frame curve. -/
theorem FrameOrientation.mem_iff_of_continuous_curve (o : FrameOrientation g)
    (γ : ℝ → FrameBundle g) (hγ : Continuous γ) (s t : ℝ) :
    γ s ∈ o.positive ↔ γ t ∈ o.positive := by
  have hc : IsClopen (γ ⁻¹' o.positive) := o.clopen.preimage hγ
  constructor
  · intro hs
    have he : γ ⁻¹' o.positive = univ := hc.eq_univ ⟨s, hs⟩
    change t ∈ γ ⁻¹' o.positive
    rw [he]
    exact mem_univ t
  · intro ht
    have he : γ ⁻¹' o.positive = univ := hc.eq_univ ⟨t, ht⟩
    change s ∈ γ ⁻¹' o.positive
    rw [he]
    exact mem_univ s

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricDistance
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tangent norm and path distance of a smooth metric. These
basic definitions are independent of the classification and scaling steps. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def metricTangentNorm (g : SmoothMetric M) (x : M) (v : TangentSpace I4 x) : ℝ :=
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ‖v‖

def metricTangentENorm (g : SmoothMetric M) (x : M) (v : TangentSpace I4 x) : ℝ≥0∞ :=
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ‖v‖ₑ

theorem metricTangentNorm_eq_sqrt (g : SmoothMetric M) (x : M)
    (v : TangentSpace I4 x) : metricTangentNorm g x v = Real.sqrt (g.inner x v v) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact norm_eq_sqrt_real_inner v

theorem metricTangentENorm_eq_ofReal (g : SmoothMetric M) (x : M)
    (v : TangentSpace I4 x) :
    metricTangentENorm g x v = ENNReal.ofReal (metricTangentNorm g x v) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact (ofReal_norm v).symm

def metricEDistance (g : SmoothMetric M) (x y : M) : ℝ≥0∞ :=
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I4 x y

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ModelIdentification
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derdzinski, Compositio Math. 49 (1983), Remark 7,
p.429 (citing Hitchin), identifies compact connected oriented Einstein
four-manifolds of positive scalar curvature with one vanishing Weyl block.
Positive sectional curvature supplies the required scalar sign. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ConnectedSpace M]

/-- The compact positive-curvature specialization of the published
half-conformally-flat identification. -/
def DerdzinskiHitchinInput (g : SmoothMetric M) (o : FrameOrientation g) : Prop :=
  T2Space M → SecondCountableTopology M → CompactSpace M → ConnectedSpace M →
    IsEinstein g → HasPositiveSectionalCurvature g →
    ((∀ c, plusWeyl g c (o.frame c) = 0) ∨
      (∀ c, minusWeyl g c (o.frame c) = 0)) →
    ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo g a roundDistance ∨
        ScaledIsometricTo g a fubiniStudyDistance)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The six two-form coefficients carry the actual tensor norm, with the
usual factor of two for repeated alternating pairs. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormTensor (a : TwoFormFour) : CovariantCoordinates 2 :=
  fun i => twoFormMatrix a (i 0) (i 1)

theorem twoFormTensor_frameAction (P : Mat4) (a : TwoFormFour) :
    twoFormTensor (twoFormFrameAction P a) = frameTensor P (twoFormTensor a) := by
  funext i
  have hi : i = ![i 0, i 1] := by ext j; fin_cases j <;> rfl
  rw [hi]
  change twoFormMatrix (twoFormFrameAction P a) (i 0) (i 1) =
    frameTensor P (twoFormTensor a) (Fin.cons (i 0) (Fin.cons (i 1) ![]))
  rw [twoFormMatrix_frameAction]
  simp only [frameTensor_cons, frameTensor_zero, twoFormTensor, Fin.cons_zero,
    Fin.cons_one, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem twoFormTensor_norm (a : TwoFormFour) :
    frameTensorSquareNorm (twoFormTensor a) = 2 * ‖a‖ ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp_rw [sum_tensor_indices_cons]
  simp [twoFormTensor, twoFormMatrix, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_succ, Real.norm_eq_abs]
  ring

theorem twoFormFrameAction_norm (P : Mat4) (hP : Pᵀ * P = 1) (a : TwoFormFour) :
    ‖twoFormFrameAction P a‖ = ‖a‖ := by
  have h := frameTensor_norm_orthogonal P (mul_eq_one_comm.mp hP) (twoFormTensor a)
  rw [← twoFormTensor_frameAction, twoFormTensor_norm, twoFormTensor_norm] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [h])

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating a tensor along a coordinate curve and a parallel frame.
The premises are the ordinary velocity and Levi-Civita parallel ODE, rather
than a specialized derivative identity for curvature or scalar fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem hasDerivAt_frameTensor {n : ℕ} (E : ℝ → Mat4)
    (T : ℝ → CovariantCoordinates n) (P : Mat4) (D : CovariantCoordinates n)
    (t : ℝ) (hE : ∀ i j, HasDerivAt (fun s => E s i j) (P i j) t)
    (hT : ∀ a, HasDerivAt (fun s => T s a) (D a) t) (a : Fin n → Fin 4) :
    HasDerivAt (fun s => frameTensor (E s) (T s) a)
      (frameVariation (E t) P (T t) a + frameTensor (E t) D a) t := by
  induction n with
  | zero =>
    simpa only [frameVariation, Pi.zero_apply, frameTensor_zero, zero_add] using hT a
  | succ n ih =>
    obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
    let F (b : Fin 4) (s : ℝ) : CovariantCoordinates n := fun w => T s (Fin.cons b w)
    let D' (b : Fin 4) : CovariantCoordinates n := fun w => D (Fin.cons b w)
    have hd (b : Fin 4) := ih (F b) (D' b) (fun w => hT (Fin.cons b w)) v
    have hp (b : Fin 4) := (hE b i).mul (hd b)
    have hs := HasDerivAt.fun_sum (fun b (_ : b ∈ Finset.univ) => hp b)
    refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · beta_reduce
      exact frameTensor_cons (E s) (T s) i v
    · simp only [frameVariation_cons, frameTensor_cons, mul_add,
        Finset.sum_add_distrib, D', F]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual continuous right action of orthogonal matrices on frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

instance instMeasurableSpaceOrthogonalFour : MeasurableSpace OrthogonalFour := borel OrthogonalFour
instance instBorelSpaceOrthogonalFour : BorelSpace OrthogonalFour := ⟨rfl⟩
instance instSecondCountableTopologyOrthogonalFour : SecondCountableTopology OrthogonalFour := by
  let : SecondCountableTopology Mat4 :=
    inferInstanceAs (SecondCountableTopology (Fin 4 → Fin 4 → ℝ))
  exact (show Topology.IsEmbedding (Subtype.val : OrthogonalFour → Mat4) from
    Topology.IsEmbedding.subtypeVal).secondCountableTopology

end
end PositiveEinsteinFour.Geometry
end


section

/-! All four actual Weyl fields used in the parallel-frame Green calculus
are continuous on the intrinsic orthonormal-frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem continuous_blockCoordinates {X : Type*} [TopologicalSpace X]
    (T : X → CovariantCoordinates 4) (hT : Continuous T) (Q : Fin 3 → Mat4) :
    Continuous (fun x => blockCoordinates (T x) Q) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun x => (1 / 8 : ℝ) * ∑ p : Fin 4 × Fin 4,
    ∑ q : Fin 4 × Fin 4, T x ![p.1, p.2, q.2, q.1] * Q i p.1 p.2 * Q j q.1 q.2)
  apply continuous_const.mul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro q _
  exact (((continuous_apply _).comp hT).mul continuous_const).mul continuous_const

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete oriented orthogonal action on the unit directions, and a
continuous oriented orthogonal completion of every direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped BigOperators

noncomputable section

instance instSecondCountableTopologySubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour : SecondCountableTopology OrientedOrthogonalFour := by
  let : SecondCountableTopology Mat4 :=
    inferInstanceAs (SecondCountableTopology (Fin 4 → Fin 4 → ℝ))
  exact (show Topology.IsEmbedding (Subtype.val : OrientedOrthogonalFour → Mat4) from
    Topology.IsEmbedding.subtypeVal).secondCountableTopology

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed linear coordinates determined by the Gram frame at one
point, and the sharp bounds on the coordinate differentials. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem fourMatrix_bijective (A : Mat4) (hA : IsUnit A) :
    Function.Bijective (Matrix.toEuclideanLin A) := by
  constructor
  · intro x y h
    apply WithLp.ofLp_injective
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hA)
    exact congrArg WithLp.ofLp h
  · intro y
    obtain ⟨x, hx⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hA) (WithLp.ofLp y)
    refine ⟨WithLp.toLp 2 x, ?_⟩
    apply WithLp.ofLp_injective
    exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reflection transforms an actual parallel-frame curve into a parallel
curve with the corresponding reversal of its time parameter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem reflection_parallel_rhs (E : Mat4) (C : Fin 4 → Mat4)
    (k i j : Fin 4) :
    (-((∑ r, (orientationSign k * E r k) • C r) *
        (E * frameReflectionMatrix)) i j) =
      orientationSign j * ((-((∑ r, E r k • C r) * E) i j) * orientationSign k) := by
  have hE : E * frameReflectionMatrix =
      fun l m => E l m * orientationSign m := by
    ext l m
    simp only [frameReflectionMatrix, Matrix.mul_diagonal]
  have hc (l : Fin 4) :
      (∑ r, orientationSign k * E r k * C r i l) =
        orientationSign k * (∑ r, E r k * C r i l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  change -(∑ l, (∑ r, (orientationSign k * E r k) * C r i l) *
      (E * frameReflectionMatrix) l j) =
    orientationSign j * ((-(∑ l, (∑ r, E r k * C r i l) * E l j)) *
      orientationSign k)
  rw [hE]
  simp_rw [hc]
  calc
    -(∑ l, (orientationSign k * ∑ r, E r k * C r i l) *
        (E l j * orientationSign j)) =
      -(∑ l, (orientationSign j * orientationSign k) *
        ((∑ r, E r k * C r i l) * E l j)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ = _ := by rw [← Finset.mul_sum]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual frame Laplacian descends to a smooth scalar on the base.
This supplies smooth test functions for the distributional Poisson equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

theorem frameTensor_two (E : Mat4) (T : CovariantCoordinates 2) (i j : Fin 4) :
    frameTensor E T ![i, j] = ∑ a, ∑ b, E a i * E b j * T ![a, b] := by
  change frameTensor E T (Fin.cons i (Fin.cons j ![])) = _
  simp only [frameTensor_cons, frameTensor_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change E a i * (E b j * T ![a, b]) = _
  ring

theorem frameTensor_trace_two (E : Mat4) (T : CovariantCoordinates 2) :
    (∑ i, frameTensor E T ![i, i]) =
      ∑ a, ∑ b, (E * Eᵀ) a b * T ![a, b] := by
  simp_rw [frameTensor_two]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cotangent lift of the actual horizontal frame equation satisfies
Hamilton's equations for the metric kinetic energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem inverse_metric_force (H C : Mat4) (hH : H.IsSymm)
    (p : Fin 4 → ℝ) :
    -(p ⬝ᵥ ((-(C * H) - H * Cᵀ) *ᵥ p) / 2) =
      p ⬝ᵥ (C *ᵥ (H *ᵥ p)) := by
  have ht : H * Cᵀ = (C * H)ᵀ := by
    rw [Matrix.transpose_mul, hH]
  rw [ht, Matrix.sub_mulVec, Matrix.neg_mulVec,
    dotProduct_sub, dotProduct_neg, Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec]
  ring

theorem parallel_momentum_algebra (G C E : Mat4) :
    (Cᵀ * G + G * C) * E + G * (-(C * E)) = Cᵀ * G * E := by
  noncomm_ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual covariant coordinate tensors of the smooth two-form sections.
The chart expression is recovered from any local orthonormal frame by its
metric coframe; no regularity of the chosen global reference frame is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def twoFormTensorLinear : TwoFormFour →ₗ[ℝ] CovariantCoordinates 2 where
  toFun := twoFormTensor
  map_add' a b := by
    funext i
    exact congrArg (fun A : Mat4 => A (i 0) (i 1)) (twoFormMatrix_add a b)
  map_smul' r a := by
    funext i
    exact congrArg (fun A : Mat4 => A (i 0) (i 1)) (twoFormMatrix_smul r a)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature term in the coordinate Jacobi equation, expressed in
an actual orthonormal frame, has normal matrix `1 + frameCurvatureField`. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def jacobiCurvatureCombination (C : Fin 4 → Fin 4 → Mat4)
    (v w : JacobiCoordinateVector) : Mat4 := ∑ i, ∑ j, (v i * w j) • C i j

def curvatureFirstLinear (C : Fin 4 → Fin 4 → Mat4)
    (w : JacobiCoordinateVector) : JacobiCoordinateVector →ₗ[ℝ] Mat4 where
  toFun v := jacobiCurvatureCombination C v w
  map_add' v u := by
    simp only [jacobiCurvatureCombination, Pi.add_apply, add_mul, add_smul,
      Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [jacobiCurvatureCombination, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.smul_sum, smul_smul, mul_assoc]

theorem jacobi_mulVec_sum (E : Mat4) (v : JacobiCoordinateVector) :
    E *ᵥ v = ∑ i, v i • (fun a => E a i) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature action on the six two-form coordinates. The
minus sign matches the convention R(i,j,k,l) = <R(i,j)k,l>. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoTensorMatrixLinear : CovariantCoordinates 2 →ₗ[ℝ] Mat4 where
  toFun T := fun i j => T ![i,j]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def twoFormExtractLinear : Mat4 →ₗ[ℝ] TwoFormFour where
  toFun := twoFormExtract
  map_add' A B := by ext i; fin_cases i <;> rfl
  map_smul' r A := by ext i; fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse parallel-frame coordinates of a variation and its covariant
derivative. The component equations follow by differentiating the inverse matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def inverseFrameComponents (E : ℝ → Mat4) (Y : ℝ → JacobiCoordinateVector)
    (s : ℝ) : JacobiCoordinateVector := (E s)⁻¹ *ᵥ Y s

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature matrix in any fixed chart. This transports the
actual curvature tensor; it does not require a diagonal or moving chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem framed_pairMatrix (E : Mat4) (D : Fin 4 → Fin 4 → Mat4)
    (i j a b : Fin 4) :
    frameTensor E (fun v => D (v 0) (v 1) (v 3) (v 2)) ![i,j,b,a] =
      ∑ p, ∑ q, (E p i * E q j) * (Eᵀ * D p q * E) a b := by
  rw [frameTensor_four]
  change (∑ p, ∑ q, ∑ r, ∑ s, E p i * E q j * E r b * E s a * D p q s r) = _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual six-dimensional Weitzenböck potential and its first two
matrix traces. These are local algebraic identities, not an index formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormCurvatureMatrix (R : CovariantCoordinates 4) : TwoFormMatrix := fun i j =>
  -R ![(AlgebraicCurvature.pair i).1, (AlgebraicCurvature.pair i).2,
    (AlgebraicCurvature.pair j).1, (AlgebraicCurvature.pair j).2]

def twoFormPotentialMatrix (R : CovariantCoordinates 4) : TwoFormMatrix :=
  (6 : ℝ) • 1 - (2 : ℝ) • twoFormCurvatureMatrix R

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruction of actual smooth two-form fields from compatible
alternating coordinate tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem twoTensorMatrix_frame (E : Mat4) (T : CovariantCoordinates 2) :
    twoTensorMatrixLinear (frameTensor E T) = Eᵀ * twoTensorMatrixLinear T * E := by
  ext i j
  change frameTensor E T ![i,j] = _
  rw [frameTensor_two]
  change (∑ a, ∑ b, E a i * E b j * T ![a,b]) =
    ∑ b, (∑ a, E a i * T ![a,b]) * E b j
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoTensorMatrix_skew (T : CovariantCoordinates 2)
    (hT : ∀ i j, T ![j,i] = -T ![i,j]) :
    (twoTensorMatrixLinear T)ᵀ = -twoTensorMatrixLinear T := by
  ext i j
  exact hT i j

theorem twoTensor_frame_skew (E : Mat4) (T : CovariantCoordinates 2)
    (hT : ∀ i j, T ![j,i] = -T ![i,j]) :
    ∀ i j, frameTensor E T ![j,i] = -frameTensor E T ![i,j] := by
  have hm : (twoTensorMatrixLinear (frameTensor E T))ᵀ =
      -twoTensorMatrixLinear (frameTensor E T) := by
    rw [twoTensorMatrix_frame]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, twoTensorMatrix_skew T hT,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  intro i j
  exact congrArg (fun A : Mat4 => A i j) hm

theorem twoFormTensor_extract (T : CovariantCoordinates 2)
    (hT : ∀ i j, T ![j,i] = -T ![i,j]) :
    twoFormTensor (twoFormExtract (twoTensorMatrixLinear T)) = T := by
  funext v
  change twoFormMatrix (twoFormExtract (twoTensorMatrixLinear T)) (v 0) (v 1) = T v
  rw [twoFormMatrix_extract _ (twoTensorMatrix_skew T hT)]
  have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  exact congrArg T hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite determinant conversion from radial/normal Jacobi components
to the metric volume density of a coordinate differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def jacobiBlockMatrix (a : ℝ) (J : Matrix (Fin 3) (Fin 3) ℝ) : Mat4 :=
  Fin.cons (Fin.cons a (fun _ => 0)) (fun i => Fin.cons 0 (J i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior derivative from smooth one-forms to two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

theorem twoCovariantAlternation_frame (E : Mat4) (T : CovariantCoordinates 2) :
    frameTensor E (twoCovariantAlternation T) = twoCovariantAlternation (frameTensor E T) := by
  funext a
  exact (frameTensor_sub E T (fun b => T (b ∘ Equiv.swap 0 1)) a).trans
    (congrArg (frameTensor E T a - ·) (frameTensor_permute E T (Equiv.swap 0 1) a).symm)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The ordinary continuous H¹-to-L⁴ embedding for the actual compact
four-manifold, assembled from compact chart cutoffs. No sharp constant is
asserted here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instFactLeENNRealOfNat_solutions_6 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


