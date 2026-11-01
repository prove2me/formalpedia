-- Prove2me | Definitions.Def_OAIQ091C042
-- name    : OAIQ091C042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:21:31.165511+00:00
-- url     : https://prove2.me/theorems/81581fb7-dd39-4779-8387-bba43819a65e
-- title:
--   Definitions bundle OAIQ091C042 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 208 declarations of OpenAI's Lean: 51 definitions, 1 instance and 156 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.TwoFormEigenIndex`, `OAI.PositiveEinsteinFour.Geometry.TwoFormSpectralSpace`, `OAI.PositiveEinsteinFour.Geometry.TwoFormSpectralValue`, `OAI.PositiveEinsteinFour.Geometry.heatNormalHodgeImage`, `OAI.PositiveEinsteinFour.Geometry.instMeasureSpaceFourSpace_1`, `OAI.PositiveEinsteinFour.Geometry.jetL4Linear`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselJetL4`, `OAI.PositiveEinsteinFour.Geometry.scalarChartReconstruction`, `OAI.PositiveEinsteinFour.Geometry.scalarChartReconstructionLinear`, `OAI.PositiveEinsteinFour.Geometry.scalarChartReconstructionLp`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormCutoffJet`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormCutoffJetCLM`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormGramL2`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormGramL2Linear`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormGreenDual`, `OAI.PositiveEinsteinFour.Geometry.twoFormChartControl`, `OAI.PositiveEinsteinFour.Geometry.twoFormChartReverseControl`, `OAI.PositiveEinsteinFour.Geometry.twoFormCutoffEuclideanH1`, `OAI.PositiveEinsteinFour.Geometry.twoFormCutoffJet`, `OAI.PositiveEinsteinFour.Geometry.twoFormCutoffSupportedH1`, `OAI.PositiveEinsteinFour.Geometry.twoFormCutoffValueL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormEigenbasis`, `OAI.PositiveEinsteinFour.Geometry.twoFormEigenvector`, `OAI.PositiveEinsteinFour.Geometry.twoFormFluxCorrection`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramConnectionL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramCorrectionVectorL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramCovariantL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramCutoffJet`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramDerivativeCorrection`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramGradientL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramNablaL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramPartialL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramPartialVectorL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramTest`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramValueL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGramVectorL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormGreenDual`, `OAI.PositiveEinsteinFour.Geometry.twoFormHodgeDomain`, `OAI.PositiveEinsteinFour.Geometry.twoFormHodgeDomainEquiv`, `OAI.PositiveEinsteinFour.Geometry.twoFormHodgeForm` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory06.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C027`, `OAIQ091C028`, `OAIQ091C059`, `OAIQ091C061`, `OAIQ091C062`, `OAIQ091C063`, `OAIQ091C065` and `OAIQ091C068`; the statement `OAI_PositiveEinsteinFour_Geometry_actual_jacobi_average_lower_refined`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C023

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

theorem smoothTwoFormToL2_dense : DenseRange (smoothTwoFormToL2 (o := o)) :=
  UniformSpace.Completion.denseRange_coe

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite curvature contraction in the two-form Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormMatrix_pairing (a b : TwoFormFour) :
    (∑ i, ∑ j, twoFormMatrix a i j * twoFormMatrix b i j) = 2 * inner ℝ a b := by
  have h := twoFormTensor_pairing a b
  rw [frameTensorPairing, twoFormCurvature_sum_two_indices] at h
  exact h

theorem twoFormCurvature_quadratic (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l]) (a : TwoFormFour) :
    (∑ i, ∑ j, ∑ k, ∑ l, R ![i,j,k,l] * twoFormMatrix a i j * twoFormMatrix a k l) =
      -4 * inner ℝ (twoFormCurvatureAction R a) a := by
  have h := twoFormTensor_pairing (twoFormCurvatureAction R a) a
  rw [twoFormTensor_curvature R hR] at h
  have he : frameTensorPairing ((-1 / 2 : ℝ) • twoTensorContraction R (twoFormTensor a))
      (twoFormTensor a) = (-1 / 2 : ℝ) *
        frameTensorPairing R (twoTensorProduct (twoFormTensor a) (twoFormTensor a)) := by
    rw [← twoTensorContraction_pairing]
    simp only [frameTensorPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he] at h
  have hp : frameTensorPairing R (twoTensorProduct (twoFormTensor a) (twoFormTensor a)) =
      ∑ i, ∑ j, ∑ k, ∑ l, R ![i,j,k,l] * twoFormMatrix a i j * twoFormMatrix a k l := by
    rw [frameTensorPairing, twoFormCurvature_sum_four_indices]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    change R _ * (twoFormMatrix a _ _ * twoFormMatrix a _ _) = _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hp] at h
  linarith only [h]

theorem twoFormCurvature_cross_contraction (R : Angular.CurvatureArray)
    (hf : AlgebraicCurvature.FirstSkew R) (hl : AlgebraicCurvature.LastSkew R)
    (hp : AlgebraicCurvature.PairSymmetric R) (hb : AlgebraicCurvature.FirstBianchi R)
    (a : TwoFormFour) :
    (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * twoFormMatrix a j l * twoFormMatrix a i k) =
      -2 * inner ℝ (twoFormCurvatureAction (fun v => R (v 0) (v 1) (v 2) (v 3)) a) a := by
  let U := ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * twoFormMatrix a j l * twoFormMatrix a i k
  have hs (i j : Fin 4) : twoFormMatrix a j i = -twoFormMatrix a i j :=
    congrArg (fun A : Mat4 => A i j) (twoFormMatrix_skew a)
  have hB (i j k l : Fin 4) : R i k j l = R i j k l + R j k i l := by
    have h := hb i j k l
    rw [hf i k j l] at h
    linarith only [h]
  have hU : (∑ i, ∑ j, ∑ k, ∑ l, R j k i l * twoFormMatrix a j l * twoFormMatrix a i k) = U := by
    rw [sum_four_swap_middle_last]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hp i j l k, hl i j k l, hs j l]
    ring
  have hV : (∑ i, ∑ j, ∑ k, ∑ l, R i k j l * twoFormMatrix a j l * twoFormMatrix a i k) = 2 * U := by
    have hx (i j k l : Fin 4) :
        R i k j l * twoFormMatrix a j l * twoFormMatrix a i k =
          R i j k l * twoFormMatrix a j l * twoFormMatrix a i k +
          R j k i l * twoFormMatrix a j l * twoFormMatrix a i k := by
      rw [hB i j k l]
      ring
    simp only [hx, Finset.sum_add_distrib]
    rw [hU]
    dsimp [U]
    ring
  have hquad := twoFormCurvature_quadratic (fun v => R (v 0) (v 1) (v 2) (v 3)) hf a
  change (∑ i, ∑ j, ∑ k, ∑ l,
    R i j k l * twoFormMatrix a i j * twoFormMatrix a k l) = _ at hquad
  have hV' : (∑ i, ∑ j, ∑ k, ∑ l, R i k j l * twoFormMatrix a j l * twoFormMatrix a i k) =
      ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * twoFormMatrix a i j * twoFormMatrix a k l := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  rw [hV'] at hV
  change U = _
  linarith only [hquad, hV]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The completion in the actual two-form H1 norm and its bounded map to
L2. Injectivity of the map is not assumed; it requires the weak derivative
closure argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormH1ToL2_smooth (u : SmoothH1TwoForm o) :
    twoFormH1ToL2 (smoothTwoFormToH1 u) = smoothTwoFormToL2 (smoothH1ToL2 u) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

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

theorem twoFormChartTest_support [T2Space M] (c : M)
    (F : FourSpace → CovariantCoordinates 2)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    (hFa : ∀ z i j, F z ![j,i] = -F z ![i,j])
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K) :
    tsupport (twoFormChartTest o c F hF hFa hK hKt hFs).val ⊆ (chartAt FourSpace c).symm '' K := by
  apply closure_minimal
  · intro x hx
    by_contra hn
    exact hx (twoFormChartTest_zero_off c F hF hFa hK hKt hFs x hn)
  · exact (hK.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hKt)).isClosed

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature term in the two-form commutator, with the actual Einstein
Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormCurvature_slot_sum (R : Angular.CurvatureArray)
    (hf : AlgebraicCurvature.FirstSkew R) (hl : AlgebraicCurvature.LastSkew R)
    (hp : AlgebraicCurvature.PairSymmetric R) (hb : AlgebraicCurvature.FirstBianchi R)
    (hr : ∀ i j, AlgebraicCurvature.ricci R i j = if i = j then 3 else 0)
    (a : TwoFormFour) :
    (∑ i, ∑ j, ∑ k, twoFormMatrix a i k *
      tensorSlotAction (curvatureEndomorphism R i j) (twoFormTensor a) ![j,k]) =
      6 * inner ℝ a a -
        2 * inner ℝ (twoFormCurvatureAction (fun v => R (v 0) (v 1) (v 2) (v 3)) a) a := by
  have hri (i p : Fin 4) : (∑ j, R i j j p) = if p = i then 3 else 0 := by
    calc
      _ = ∑ j, R j p i j := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hp i j j p).symm
      _ = _ := hr p i
  have hinner (i k : Fin 4) :
      (∑ j, ∑ p, R i j j p * twoFormMatrix a p k) = 3 * twoFormMatrix a i k := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hri]
    simp
  have hfirst : (∑ i, ∑ j, ∑ k, twoFormMatrix a i k *
      (∑ p, R i j j p * twoFormMatrix a p k)) = 6 * inner ℝ a a := by
    calc
      _ = ∑ i, ∑ k, twoFormMatrix a i k * (3 * twoFormMatrix a i k) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hinner]
      _ = 3 * (∑ i, ∑ k, twoFormMatrix a i k * twoFormMatrix a i k) := by
        simp only [Finset.mul_sum]
        repeat' (apply Finset.sum_congr rfl; intro _ _)
        ring
      _ = _ := by rw [twoFormMatrix_pairing]; ring
  have hsecond : (∑ i, ∑ j, ∑ k, twoFormMatrix a i k *
      (∑ p, R i j k p * twoFormMatrix a j p)) =
        -2 * inner ℝ (twoFormCurvatureAction (fun v => R (v 0) (v 1) (v 2) (v 3)) a) a := by
    rw [← twoFormCurvature_cross_contraction R hf hl hp hb a]
    simp only [Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  simp only [tensorSlotAction_two, curvatureEndomorphism, twoFormTensor,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_add, Finset.sum_add_distrib]
  rw [hfirst, hsecond]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormMetricCurvature_slot_sum (hRic : RicciThree g)
    (u : M → TwoFormFour) (e : FrameBundle g) :
    (∑ i, ∑ j, ∑ k, twoFormFramedValue o u e ![i,k] *
      tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
        (twoFormFramedValue o u e) ![j,k]) =
      6 * inner ℝ (twoFormFrameValue o u e) (twoFormFrameValue o u e) -
        2 * inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
          (twoFormFrameValue o u e)) (twoFormFrameValue o u e) := by
  have hR : twoFormMetricCurvatureTensor g e =
      fun v => frameCurvature g e.base e.frame (v 0) (v 1) (v 2) (v 3) := by
    funext v
    have hv : ![v 0, v 1, v 2, v 3] = v := by
      ext i
      fin_cases i <;> rfl
    rw [← hv]
    exact frameTensor_curvatureCoordinates e.frame _ _ _ _
  rw [twoFormFramedValue_eq, hR]
  exact twoFormCurvature_slot_sum _ (frame_algebraic_firstSkew e.frame)
    (frame_algebraic_lastSkew e.frame)
    (frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame))
    (frame_algebraic_firstBianchi e.frame) (frame_algebraic_ricciThree e.frame hRic) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Realization of compactly supported local orthonormal-frame tests as
actual smooth global two-forms, including their covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Function
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormGramTest [T2Space M] (o : FrameOrientation g) (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) : smoothTwoForms o :=
  twoFormChartTest o c (twoFormGramTestTensor g c S a)
    (twoFormGramTestTensor_smooth g c S a ha) (twoFormGramTestTensor_skew g c S a)
    hK hKt ((twoFormGramTestTensor_support g c S a).trans has)

theorem twoFormGramTest_value [T2Space M] (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormChartValue o (twoFormGramTest o c S a ha hK hKt has) c S hS z = a z := by
  apply twoFormTensor_injective
  rw [twoFormChartValue_tensor o _ c S hS z hz]
  change frameTensor (chartGramMatrix g c S z)
    (twoFormCoordinates o (twoFormChartTest o c _ _ _ hK hKt _) c z) = _
  rw [twoFormChartTest_coordinates c _ _ _ hK hKt _ z hz]
  unfold twoFormGramTestTensor
  rw [← frameTensor_mul, chartGramMatrix_normalizes g c S hS ⟨z, hz⟩, frameTensor_one]

theorem twoFormGramTest_nabla [T2Space M] (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    twoFormLocalNabla (g := g) c S
      (twoFormChartValue o (twoFormGramTest o c S a ha hK hKt has) c S hS) i z =
      twoFormLocalNabla (g := g) c S a i z := by
  apply twoFormLocalNabla_congr
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact twoFormGramTest_value c S hS a ha hK hKt has w hw

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic first-derivative pairing in a chart. Its principal
coefficient is the actual inverse metric on each of the six components. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormDerivativeRows_pairing (A B : Fin 4 → TwoFormFour) :
    frameTensorPairing (twoFormDerivativeRows A) (twoFormDerivativeRows B) =
      2 * ∑ i, inner ℝ (A i) (B i) := by
  unfold frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [twoFormDerivativeRows_cons]
  change (∑ i, frameTensorPairing (twoFormTensor (A i)) (twoFormTensor (B i))) = _
  simp_rw [twoFormTensor_pairing]
  exact (Finset.mul_sum _ _ _).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.covariantPairing_chart {u v : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (hv : TwoFormSmooth o v)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive)
    (z : FourSpace) (hz : z ∈ U) :
    twoFormCovariantPairing o u v ((chartAt FourSpace c).symm z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        inner ℝ (twoFormLocalNabla (g := g) c S (twoFormChartValue o u c S hS) i z)
          (twoFormLocalNabla (g := g) c S (twoFormChartValue o v c S hS) j z) := by
  have he := twoFormCovariantPairing_eq_frame o u v
    (chartGramSection g c S hS ⟨z, hUt hz⟩)
  change twoFormCovariantPairing o u v ((chartAt FourSpace c).symm z) = _ at he
  rw [he, hu.gramCovariantDerivative c S hS U hU hUt hp z hz,
    hv.gramCovariantDerivative c S hS U hU hUt hp z hz, twoFormDerivativeRows_pairing]
  have hc := twoFormLocalNablaRows_pairing (g := g) c S hS
    (twoFormChartValue o u c S hS) (twoFormChartValue o v c S hS) z (hUt hz)
  linarith only [hc]

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

/-! Frame-bundle integral realizations of the intrinsic two-form pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

theorem smoothTwoFormCurvatureInner_eq_frame (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormCurvature u) v = ∫ e,
      inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
        (twoFormFrameValue o u.val e)) (twoFormFrameValue o v.val e)
          ∂canonicalFrameMeasure g o := by
  rw [smoothTwoFormL2Inner_eq_frame]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [← twoFormCurvatureField_frame]
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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.twoFormBound_compactFrame
theorem smoothTwoFormCovariantEnergy_L2_bound (hRic : RicciThree g)
    (u : SmoothL2TwoForm o) (v : smoothTwoForms o) :
    |smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v| ≤
      ‖u‖ * ‖smoothTwoFormTensorTraceL2 v‖ := by
  have hg := smoothTwoForm_rough_green hRic (u : smoothTwoForms o) v
  have ht := smoothTwoFormTensorValueTrace_inner (u : smoothTwoForms o) v
  rw [← ht] at hg
  have hi := abs_real_inner_le_norm (smoothTwoFormTensorValueL2 (u : smoothTwoForms o))
    (smoothTwoFormTensorTraceL2 v)
  have hn := mul_le_mul_of_nonneg_right (smoothTwoFormTensorValueL2_norm_le u)
    (norm_nonneg (smoothTwoFormTensorTraceL2 v))
  rw [hg, abs_mul]
  norm_num
  nlinarith only [hi, hn]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed-direction integration by parts for the actual two-form jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle
theorem smoothTwoForm_mixed_green (hRic : RicciThree g) (u v : smoothTwoForms o)
    (i j : Fin 4) (a b : Fin 2 → Fin 4) :
    (∫ e, twoFormFramedCovariantDerivative o u.val e (Fin.cons i a) *
      twoFormFramedCovariantDerivative o v.val e (Fin.cons j b) ∂canonicalFrameMeasure g o) =
      -(∫ e, twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons j b))
        ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedValue o u.val e a,
    (continuous_apply a).comp u.property.continuous_framedValue⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o u.val e (Fin.cons i a),
    (continuous_apply _).comp u.property.continuous_framedCovariantDerivative⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o v.val e (Fin.cons j b),
    (continuous_apply _).comp v.property.continuous_framedCovariantDerivative⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons j b)),
    (continuous_apply _).comp v.property.continuous_framedSecondDerivative⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.framedValue_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) a
  · intro t e
    exact v.property.framedCovariant_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) (Fin.cons j b)

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

theorem tensorTransportWeight_nonneg (n : ℕ) (P : Mat4) :
    0 ≤ tensorTransportWeight n P :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCoordinates_abs_le (u : M → TwoFormFour) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 2 → Fin 4) :
    |twoFormCoordinates o u c z a| ≤
      2 * tensorTransportWeight 2 (twoFormChartTransport g c z) *
        ‖u ((chartAt FourSpace c).symm z)‖ := by
  rw [twoFormCoordinates_from_chart o u c 1 (by simp) z hz]
  have hn : ‖twoFormChartValue o u c 1 (by simp) z‖ =
      ‖u ((chartAt FourSpace c).symm z)‖ := by
    simp only [twoFormChartValue, dite_eq_left hz]
    exact twoFormFrameValue_norm o u _
  have hbound (b : Fin 2 → Fin 4) :
      |twoFormTensor (twoFormChartValue o u c 1 (by simp) z) b| ≤
        2 * ‖u ((chartAt FourSpace c).symm z)‖ := by
    have hb := tensor_component_sq_le
      (twoFormTensor (twoFormChartValue o u c 1 (by simp) z)) b
    rw [twoFormTensor_norm, hn] at hb
    nlinarith [abs_nonneg (twoFormTensor (twoFormChartValue o u c 1 (by simp) z) b),
      norm_nonneg (u ((chartAt FourSpace c).symm z))]
  have h := frameTensor_abs_le_weight (twoFormChartTransport g c z) _
    (2 * ‖u ((chartAt FourSpace c).symm z)‖) (by positivity) hbound a
  exact h.trans_eq (by ring)

theorem TwoFormSmooth.covariantCoordinates_abs_le {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 3 → Fin 4) :
    |twoFormCovariantCoordinates o u c z a| ≤
      2 * tensorTransportWeight 3 (twoFormChartTransport g c z) *
        Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z)) := by
  let e := chartGramSection g c 1 (by simp) ⟨z, hz⟩
  have he : e.base = (chartAt FourSpace c).symm z := rfl
  have hnorm : frameTensorSquareNorm (twoFormFramedCovariantDerivative o u e) =
      2 * twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z) := by
    have h := twoFormCovariantPairing_eq_frame o u u e
    change twoFormCovariantPairing o u u e.base =
      (1 / 2 : ℝ) * frameTensorSquareNorm (twoFormFramedCovariantDerivative o u e) at h
    rw [he] at h
    linarith
  have hback : twoFormCovariantCoordinates o u c z =
      frameTensor (twoFormChartTransport g c z) (twoFormFramedCovariantDerivative o u e) := by
    rw [hu.gramCovariantCoordinates c z hz, ← frameTensor_mul]
    have h := chartGramMatrix_normalizes g c 1 (by simp) ⟨z, hz⟩
    change (chartGramMatrix g c 1 z)ᵀ * metricInChart g c z *
      chartGramMatrix g c 1 z = 1 at h
    change twoFormChartTransport g c z * chartGramMatrix g c 1 z = 1 at h
    rw [mul_eq_one_comm.mp h, frameTensor_one]
  have hbound (b : Fin 3 → Fin 4) : |twoFormFramedCovariantDerivative o u e b| ≤
      2 * Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z)) := by
    have hb := tensor_component_sq_le (twoFormFramedCovariantDerivative o u e) b
    rw [hnorm] at hb
    have hs := Real.sq_sqrt
      (twoFormCovariantPairing_self_nonneg o u ((chartAt FourSpace c).symm z))
    nlinarith [abs_nonneg (twoFormFramedCovariantDerivative o u e b), Real.sqrt_nonneg
      (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))]
  rw [hback]
  have h := frameTensor_abs_le_weight (twoFormChartTransport g c z) _
    (2 * Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z)))
    (by positivity) hbound a
  exact h.trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed integration by parts turns the first-order cross terms into
the actual curvature action on two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_1
theorem smoothTwoForm_cross_curvature (hRic : RicciThree g) (u v : smoothTwoForms o) :
    (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
        twoFormFramedCovariantDerivative o v.val e ![j,j,k] ∂canonicalFrameMeasure g o) -
    (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
        twoFormFramedCovariantDerivative o v.val e ![j,i,k] ∂canonicalFrameMeasure g o) =
    ∑ i, ∑ j, ∑ k, ∫ e, twoFormFramedValue o u.val e ![i,k] *
      tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
        (twoFormFramedValue o v.val e) ![j,k] ∂canonicalFrameMeasure g o := by
  let μ := canonicalFrameMeasure g o
  let A := fun i j k => ∫ e, twoFormFramedValue o u.val e ![i,k] *
    twoFormFramedSecondDerivative o v.val e ![i,j,j,k] ∂μ
  let B := fun i j k => ∫ e, twoFormFramedValue o u.val e ![i,k] *
    twoFormFramedSecondDerivative o v.val e ![j,i,j,k] ∂μ
  let C := fun i j k => ∫ e, twoFormFramedValue o u.val e ![i,k] *
    tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
      (twoFormFramedValue o v.val e) ![j,k] ∂μ
  have hint (a : Fin 2 → Fin 4) (b : Fin 4 → Fin 4) :
      Integrable (fun e => twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o v.val e b) μ :=
    (((continuous_apply a).comp u.property.continuous_framedValue).mul
      ((continuous_apply b).comp v.property.continuous_framedSecondDerivative)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hAB (i j k : Fin 4) : A i j k - B i j k = -C i j k := by
    change (∫ e, _ ∂μ) - (∫ e, _ ∂μ) = -(∫ e, _ ∂μ)
    rw [← integral_sub (hint ![i,k] ![i,j,j,k]) (hint ![i,k] ![j,i,j,k]), ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with e
    have hc := v.property.framed_commutator e i j ![j,k]
    change twoFormFramedSecondDerivative o v.val e ![i,j,j,k] -
      twoFormFramedSecondDerivative o v.val e ![j,i,j,k] = _ at hc
    rw [← mul_sub, hc, mul_neg]
  have hfirst : (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
      twoFormFramedCovariantDerivative o v.val e ![j,j,k] ∂μ) =
        -(∑ i, ∑ j, ∑ k, A i j k) := by
    have h (i j k : Fin 4) : (∫ e,
        twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
        twoFormFramedCovariantDerivative o v.val e ![j,j,k] ∂μ) = -A i j k :=
      smoothTwoForm_mixed_green hRic u v i j ![i,k] ![j,k]
    simp only [h, Finset.sum_neg_distrib]
  have hsecond : (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
      twoFormFramedCovariantDerivative o v.val e ![j,i,k] ∂μ) =
        -(∑ i, ∑ j, ∑ k, B i j k) := by
    rw [Finset.sum_comm]
    have h (i j k : Fin 4) : (∫ e,
        twoFormFramedCovariantDerivative o u.val e ![j,i,k] *
        twoFormFramedCovariantDerivative o v.val e ![i,j,k] ∂μ) = -B i j k :=
      smoothTwoForm_mixed_green hRic u v j i ![i,k] ![j,k]
    simp only [h, Finset.sum_neg_distrib]
  change _ - _ = ∑ i, ∑ j, ∑ k, C i j k
  rw [hfirst, hsecond]
  have hs : (∑ i, ∑ j, ∑ k, A i j k) - (∑ i, ∑ j, ∑ k, B i j k) =
      -(∑ i, ∑ j, ∑ k, C i j k) := by
    simp only [← Finset.sum_sub_distrib]
    simp_rw [hAB, Finset.sum_neg_distrib]
  linarith only [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The H1 pairing against a smooth two-form extends to the actual L2
completion by the rough Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormGreenLinear_bound (hRic : RicciThree g)
    (v : SmoothL2TwoForm o) (u : SmoothL2TwoForm o) :
    ‖smoothTwoFormGreenLinear v u‖ ≤
      (‖v‖ + ‖smoothTwoFormTensorTraceL2 v‖) * ‖u‖ := by
  have hL2 : |smoothTwoFormL2Inner (u : smoothTwoForms o) v| ≤
      ‖u‖ * ‖v‖ :=
    abs_real_inner_le_norm u v
  have hE := smoothTwoFormCovariantEnergy_L2_bound hRic u v
  change |smoothTwoFormL2Inner (u : smoothTwoForms o) v +
    smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v| ≤ _
  calc
    _ ≤ |smoothTwoFormL2Inner (u : smoothTwoForms o) v| +
      |smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v| := abs_add_le _ _
    _ ≤ ‖u‖ * ‖v‖ +
      ‖u‖ * ‖smoothTwoFormTensorTraceL2 v‖ := add_le_add hL2 hE
    _ = _ := by ring

def smoothTwoFormGreenDual (hRic : RicciThree g) (v : SmoothL2TwoForm o) :
    SmoothL2TwoForm o →L[ℝ] ℝ :=
  (smoothTwoFormGreenLinear v).mkContinuous
    (‖v‖ + ‖smoothTwoFormTensorTraceL2 v‖)
    (smoothTwoFormGreenLinear_bound hRic v)

def twoFormGreenDual (hRic : RicciThree g) (v : SmoothL2TwoForm o) :
    TwoFormL2 o →L[ℝ] ℝ :=
  (smoothTwoFormGreenDual hRic v).fromCompletion

theorem twoFormGreenDual_smooth (hRic : RicciThree g) (v : SmoothL2TwoForm o)
    (u : SmoothL2TwoForm o) :
    twoFormGreenDual hRic v (smoothTwoFormToL2 u) =
      smoothTwoFormL2Inner (u : smoothTwoForms o) v +
        smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem twoFormH1_inner_smooth (hRic : RicciThree g) (u : TwoFormH1 o)
    (v : SmoothH1TwoForm o) :
    inner ℝ u (smoothTwoFormToH1 v) =
      twoFormGreenDual hRic (smoothH1ToL2 v) (twoFormH1ToL2 u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (continuous_id.inner continuous_const)
      ((twoFormGreenDual hRic (smoothH1ToL2 v)).continuous.comp
        twoFormH1ToL2.continuous)) ?_
  intro w
  change inner ℝ (smoothTwoFormToH1 w) (smoothTwoFormToH1 v) =
    twoFormGreenDual hRic (smoothH1ToL2 v) (twoFormH1ToL2 (smoothTwoFormToH1 w))
  rw [twoFormH1ToL2_smooth, twoFormGreenDual_smooth]
  exact UniformSpace.Completion.inner_coe w v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact chart control of ordinary derivatives by the actual two-form
H1 energy. The connection coefficients are bounded only on the chosen
compact chart set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartControl (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  2 * tensorTransportWeight 2 (twoFormChartTransport g c z) +
  2 * tensorTransportWeight 3 (twoFormChartTransport g c z) +
  2 * twoFormChartConnectionWeight g c z * tensorTransportWeight 2 (twoFormChartTransport g c z)

theorem twoFormChartControl_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (twoFormChartControl g c) (chartAt FourSpace c).target := by
  have hc : ContinuousOn (twoFormChartConnectionWeight g c) (chartAt FourSpace c).target := by
    apply continuousOn_finsetSum
    intro i _
    apply (tensorSlotWeight_continuous 2).comp_continuousOn
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k z hz
    exact (christoffel_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
      j i k).continuousAt.continuousWithinAt
  have h₂ := (tensorTransportWeight_continuous 2).comp_continuousOn
    (twoFormChartTransport_continuousOn g c)
  have h₃ := (tensorTransportWeight_continuous 3).comp_continuousOn
    (twoFormChartTransport_continuousOn g c)
  exact ((continuousOn_const.mul h₂).add (continuousOn_const.mul h₃)).add
    ((continuousOn_const.mul hc).mul h₂)

theorem TwoFormSmooth.coordinate_partial_control {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) (a : Fin 2 → Fin 4) :
    |partialDeriv (fun w => twoFormCoordinates o u c w a) i z| ≤
      twoFormChartControl g c z * (‖u ((chartAt FourSpace c).symm z)‖ +
        Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))) := by
  let V := ‖u ((chartAt FourSpace c).symm z)‖
  let E := Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))
  let A := 2 * tensorTransportWeight 3 (twoFormChartTransport g c z)
  let B := 2 * twoFormChartConnectionWeight g c z *
    tensorTransportWeight 2 (twoFormChartTransport g c z)
  have hV : 0 ≤ V := norm_nonneg _
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hA : 0 ≤ A := mul_nonneg (by norm_num) (tensorTransportWeight_nonneg _ _)
  have hB : 0 ≤ B := by
    dsimp [B, twoFormChartConnectionWeight]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ => tensorSlotWeight_nonneg _ _)))
      (tensorTransportWeight_nonneg _ _)
  have hs := tensorSlotAction_abs_le_weight (connectionMatrix g c i z)
    (twoFormCoordinates o u c z)
    (2 * tensorTransportWeight 2 (twoFormChartTransport g c z) * V)
    (mul_nonneg (mul_nonneg (by norm_num) (tensorTransportWeight_nonneg _ _)) hV)
    (twoFormCoordinates_abs_le u c z hz) a
  have hi : tensorSlotWeight 2 (connectionMatrix g c i z) ≤
      twoFormChartConnectionWeight g c z :=
    Finset.single_le_sum (fun j _ => tensorSlotWeight_nonneg 2 (connectionMatrix g c j z))
      (Finset.mem_univ i)
  have hs' : |tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a| ≤ B * V :=
    hs.trans ((mul_le_mul_of_nonneg_right hi
      (mul_nonneg (mul_nonneg (by norm_num) (tensorTransportWeight_nonneg _ _)) hV)).trans_eq
        (by dsimp [B]; ring))
  have heq : partialDeriv (fun w => twoFormCoordinates o u c w a) i z =
      twoFormCovariantCoordinates o u c z (Fin.cons i a) +
        tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a := by
    unfold twoFormCovariantCoordinates
    rw [covariantDerivative_direction]
    change _ = (partialDeriv (fun w => twoFormCoordinates o u c w a) i z -
      tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a) + _
    ring
  rw [heq]
  calc
    _ ≤ |twoFormCovariantCoordinates o u c z (Fin.cons i a)| +
      |tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a| := abs_add_le _ _
    _ ≤ A * E + B * V := add_le_add (hu.covariantCoordinates_abs_le c z hz _) hs'
    _ ≤ A * (V + E) + B * (V + E) := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hV) hA)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE) hB)
    _ ≤ twoFormChartControl g c z * (V + E) := by
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (add_nonneg hV hE)
      change A + B ≤ _ + A + B
      linarith [mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (tensorTransportWeight_nonneg 2 (twoFormChartTransport g c z))]

theorem twoFormChart_compact_control (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : M → TwoFormFour), TwoFormSmooth o u →
      ∀ z ∈ K, (∀ a, |twoFormCoordinates o u c z a| ≤ C * ‖u ((chartAt FourSpace c).symm z)‖) ∧
        ∀ i a, |partialDeriv (fun w => twoFormCoordinates o u c w a) i z| ≤
          C * (‖u ((chartAt FourSpace c).symm z)‖ +
            Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))) := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn
    ((twoFormChartControl_continuousOn g c).mono hKt)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun u hu z hz => ?_⟩
  have hbound : twoFormChartControl g c z ≤ max C 0 :=
    (le_abs_self _).trans ((hC _ ⟨z, hz, rfl⟩).trans (le_max_left _ _))
  refine ⟨fun a => (twoFormCoordinates_abs_le u c z (hKt hz) a).trans ?_, fun i a =>
    (hu.coordinate_partial_control c z (hKt hz) i a).trans
      (mul_le_mul_of_nonneg_right hbound (by positivity))⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply le_trans _ hbound
  unfold twoFormChartControl
  have hw : 0 ≤ twoFormChartConnectionWeight g c z :=
    Finset.sum_nonneg (fun _ _ => tensorSlotWeight_nonneg _ _)
  have h₂ := tensorTransportWeight_nonneg 2 (twoFormChartTransport g c z)
  have h₃ := tensorTransportWeight_nonneg 3 (twoFormChartTransport g c z)
  have hp := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hw) h₂
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reverse chart norm control. This recovers the intrinsic two-form
value from its finitely many compact coordinate components. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem frameTensor_sum_abs_le {n : ℕ} (P : Mat4) (T : CovariantCoordinates n) :
    (∑ a : Fin n → Fin 4, |frameTensor P T a|) ≤
      (Fintype.card (Fin n → Fin 4) : ℝ) * tensorTransportWeight n P *
        ∑ b : Fin n → Fin 4, |T b| := by
  have hsum : 0 ≤ ∑ b : Fin n → Fin 4, |T b| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc
    _ ≤ ∑ _a : Fin n → Fin 4, tensorTransportWeight n P * ∑ b : Fin n → Fin 4, |T b| :=
      Finset.sum_le_sum (fun a _ => frameTensor_abs_le_weight P T _ hsum
        (fun b => Finset.single_le_sum (fun c _ => abs_nonneg (T c)) (Finset.mem_univ b)) a)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartReverseControl (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  (Fintype.card (Fin 2 → Fin 4) : ℝ) * tensorTransportWeight 2 (chartGramMatrix g c 1 z)

theorem twoFormChartReverseControl_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (twoFormChartReverseControl g c) (chartAt FourSpace c).target := by
  apply continuousOn_const.mul
  apply (tensorTransportWeight_continuous 2).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j z hz
  exact (chartGramMatrix_contDiffAt g c 1 z hz i j).continuousAt.continuousWithinAt

theorem twoForm_chart_reverse_value (u : M → TwoFormFour) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (r : ℝ) :
    |r| * ‖u ((chartAt FourSpace c).symm z)‖ ≤ twoFormChartReverseControl g c z *
      ∑ a : Fin 2 → Fin 4, |r * twoFormCoordinates o u c z a| := by
  have h := twoForm_norm_le_tensor_sum (twoFormChartValue o u c 1 (by simp) z)
  rw [twoFormChartValue_norm o u c 1 (by simp) z hz,
    twoFormChartValue_tensor o u c 1 (by simp) z hz] at h
  have hb := h.trans (frameTensor_sum_abs_le (chartGramMatrix g c 1 z) (twoFormCoordinates o u c z))
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg r)
  calc
    _ ≤ |r| * (twoFormChartReverseControl g c z * ∑ a : Fin 2 → Fin 4, |twoFormCoordinates o u c z a|) := hm
    _ = _ := by simp only [abs_mul, ← Finset.mul_sum]; ring

theorem twoForm_chart_reverse_bound (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : M → TwoFormFour) (z : FourSpace), z ∈ K → ∀ r : ℝ,
      |r| * ‖u ((chartAt FourSpace c).symm z)‖ ≤
        C * ∑ a : Fin 2 → Fin 4, |r * twoFormCoordinates o u c z a| := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn
    ((twoFormChartReverseControl_continuousOn g c).mono hKt)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun u z hz r => ?_⟩
  have hbound : twoFormChartReverseControl g c z ≤ max C 0 :=
    (le_abs_self _).trans ((hC _ ⟨z, hz, rfl⟩).trans (le_max_left _ _))
  exact (twoForm_chart_reverse_value (o := o) u c z (hKt hz) r).trans
    (mul_le_mul_of_nonneg_right hbound (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_4
theorem twoFormFromContinuousTensor_pairing (F : C(FrameBundle g, TwoTensorEuclidean))
    (v : SmoothL2TwoForm o) :
    inner ℝ (twoFormFromContinuousTensor F) (smoothTwoFormToL2 v) =
      (1 / 2 : ℝ) * ∫ e, inner ℝ (F e) (smoothTwoFormEuclideanValue (v : smoothTwoForms o) e)
        ∂canonicalFrameMeasure g o := by
  change inner ℝ (twoFormFromTensorL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F))
    (smoothTwoFormToL2 v) = _
  rw [twoFormFromTensorL2_pairing, twoFormTensorL2_smooth]
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
      (smoothTwoFormEuclideanValue (v : smoothTwoForms o))] with e hF hv
  rw [hF]
  exact congrArg (inner ℝ (F e)) hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior-derivative and codifferential energy of a smooth
two-form, and its integrated Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_5
theorem smoothTwoFormDeRhamEnergy_cross (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = smoothTwoFormCovariantEnergy u u +
      (∑ i, ∑ j, ∑ k, ∫ e,
        twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
        twoFormFramedCovariantDerivative o u.val e ![j,j,k] ∂canonicalFrameMeasure g o) -
      (∑ i, ∑ j, ∑ k, ∫ e,
        twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
        twoFormFramedCovariantDerivative o u.val e ![j,i,k] ∂canonicalFrameMeasure g o) := by
  let μ := canonicalFrameMeasure g o
  let D := fun e i j k => twoFormFramedCovariantDerivative o u.val e ![i,j,k]
  let A := fun e => ∑ i, ∑ j, ∑ k, D e i j k * D e i j k
  let B := fun e => ∑ i, ∑ j, ∑ k, D e i i k * D e j j k
  let C := fun e => ∑ i, ∑ j, ∑ k, D e i j k * D e j i k
  have hi (a b : Fin 3 → Fin 4) := smoothTwoForm_derivative_product_integrable u u a b
  have hA : Integrable A μ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi ![i,j,k] ![i,j,k]
  have hB : Integrable B μ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi ![i,i,k] ![j,j,k]
  have hC : Integrable C μ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi ![i,j,k] ![j,i,k]
  have he : smoothTwoFormDeRhamEnergy u = ∫ e, (1 / 2 : ℝ) * A e + B e - C e ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with e
    simpa only [D, A, B, C, pow_two] using
      twoFormDeRhamQuadratic_eq (D e) (u.property.framedCovariant_skew hRic e)
  have hAB : Integrable (fun e => (1 / 2 : ℝ) * A e + B e) μ :=
    (hA.const_mul (1 / 2 : ℝ)).add hB
  rw [he, integral_sub hAB hC,
    integral_add (hA.const_mul (1 / 2 : ℝ)) hB, integral_const_mul]
  have ha : smoothTwoFormCovariantEnergy u u = (1 / 2 : ℝ) * ∫ e, A e ∂μ :=
    smoothTwoFormCovariantEnergy_eq_frame u u
  rw [← ha]
  congr 2
  · exact integral_frame_sum_three μ _ (fun i j k => hi ![i,i,k] ![j,j,k])
  · exact integral_frame_sum_three μ _ (fun i j k => hi ![i,j,k] ![j,i,k])

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual H1 completion embeds injectively in L2. The rough Green
identity makes the derivative graph closable; no injectivity premise is
imposed on the completion map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormH1_eq_zero_of_value_eq_zero (hRic : RicciThree g)
    (u : TwoFormH1 o) (hu : twoFormH1ToL2 u = 0) : u = 0 := by
  have htest (v : SmoothH1TwoForm o) : inner ℝ u (smoothTwoFormToH1 v) = 0 := by
    rw [twoFormH1_inner_smooth hRic, hu, map_zero]
  have hall : ∀ v : TwoFormH1 o, inner ℝ u v = 0 := by
    have heq : (fun v : TwoFormH1 o => inner ℝ u v) = fun _ => 0 :=
      (smoothTwoFormToH1_dense (o := o)).equalizer
        (continuous_const.inner continuous_id) continuous_const (funext htest)
    intro v
    exact congrFun heq v
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hall u)

theorem twoFormH1ToL2_injective (hRic : RicciThree g) :
    Function.Injective (twoFormH1ToL2 (o := o)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply twoFormH1_eq_zero_of_value_eq_zero hRic
  rw [map_sub, huv, sub_self]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated Weitzenböck identity for the actual smooth two-forms
on a closed Einstein four-manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_6
theorem smoothTwoForm_frame_inner_integrable (u v : smoothTwoForms o) :
    Integrable (fun e => inner ℝ (twoFormFrameValue o u.val e)
      (twoFormFrameValue o v.val e)) (canonicalFrameMeasure g o) := by
  have hc : Continuous (fun e => (1 / 2 : ℝ) * frameTensorPairing
      (twoFormFramedValue o u.val e) (twoFormFramedValue o v.val e)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro a _
    exact ((continuous_apply a).comp u.property.continuous_framedValue).mul
      ((continuous_apply a).comp v.property.continuous_framedValue)
  have he : (fun e => inner ℝ (twoFormFrameValue o u.val e) (twoFormFrameValue o v.val e)) =
      fun e => (1 / 2 : ℝ) * frameTensorPairing
        (twoFormFramedValue o u.val e) (twoFormFramedValue o v.val e) := by
    funext e
    rw [twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormTensor_pairing]
    ring
  rw [he]
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem smoothTwoForm_Weitzenbock (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = smoothTwoFormCovariantEnergy u u +
      6 * smoothTwoFormL2Inner u u - 2 * smoothTwoFormL2Inner (smoothTwoFormCurvature u) u := by
  let μ := canonicalFrameMeasure g o
  let F := fun i j k (e : FrameBundle g) => twoFormFramedValue o u.val e ![i,k] *
    tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
      (twoFormFramedValue o u.val e) ![j,k]
  have hi (a : Fin 2 → Fin 4) (b : Fin 4 → Fin 4) :
      Integrable (fun e => twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o u.val e b) μ :=
    (((continuous_apply a).comp u.property.continuous_framedValue).mul
      ((continuous_apply b).comp u.property.continuous_framedSecondDerivative)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hF (i j k : Fin 4) : Integrable (F i j k) μ := by
    apply ((hi ![i,k] ![i,j,j,k]).sub (hi ![i,k] ![j,i,j,k])).neg.congr
    filter_upwards [] with e
    have hc := u.property.framed_commutator e i j ![j,k]
    change twoFormFramedSecondDerivative o u.val e ![i,j,j,k] -
      twoFormFramedSecondDerivative o u.val e ![j,i,j,k] = _ at hc
    dsimp [F]
    rw [← mul_sub, hc]
    ring
  have hC := smoothTwoForm_cross_curvature hRic u u
  change _ - _ = ∑ i, ∑ j, ∑ k, ∫ e, F i j k e ∂μ at hC
  rw [← integral_frame_sum_three μ F hF] at hC
  have h0 := smoothTwoForm_frame_inner_integrable u u
  have h1 := smoothTwoForm_frame_inner_integrable (smoothTwoFormCurvature u) u
  change Integrable (fun e => inner ℝ
    (twoFormFrameValue o (twoFormCurvatureField o u.val) e)
    (twoFormFrameValue o u.val e)) μ at h1
  simp_rw [twoFormCurvatureField_frame] at h1
  have hf : (fun e => ∑ i, ∑ j, ∑ k, F i j k e) = fun e =>
      6 * inner ℝ (twoFormFrameValue o u.val e) (twoFormFrameValue o u.val e) -
        2 * inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
          (twoFormFrameValue o u.val e)) (twoFormFrameValue o u.val e) := by
    funext e
    exact twoFormMetricCurvature_slot_sum hRic u.val e
  rw [hf, integral_sub (h0.const_mul 6) (h1.const_mul 2), integral_const_mul,
    integral_const_mul, ← smoothTwoFormL2Inner_eq_frame u u,
    ← smoothTwoFormCurvatureInner_eq_frame u u] at hC
  rw [smoothTwoFormDeRhamEnergy_cross hRic u]
  linarith only [hC]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rough Green identity with its actual smooth trace section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_roughTrace_green (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v =
      -smoothTwoFormL2Inner u (smoothTwoFormRoughTrace hRic v) := by
  rw [smoothTwoForm_rough_green hRic, smoothTwoFormL2Inner_eq_frame]
  have he : (fun e : FrameBundle g =>
      frameTensorPairing (twoFormFramedValue o u.val e)
        (twoFormFramedRoughTrace o v.val e)) =
      fun e => 2 * inner ℝ (twoFormFrameValue o u.val e)
        (twoFormFrameValue o (smoothTwoFormRoughTrace hRic v).val e) := by
    funext e
    rw [← v.property.framedValue_roughTrace hRic e, twoFormFramedValue_eq,
      twoFormFramedValue_eq, twoFormTensor_pairing]
    rfl
  rw [he, integral_const_mul]
  ring

theorem smoothTwoForm_roughTrace_green_left (hRic : RicciThree g)
    (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v =
      -smoothTwoFormL2Inner (smoothTwoFormRoughTrace hRic u) v := by
  rw [smoothTwoFormCovariantEnergy_comm, smoothTwoForm_roughTrace_green hRic,
    smoothTwoFormL2Inner_comm]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatNormalAmplitudeL2_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : SmoothL2TwoForm o) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothTwoFormToL2 v) =
      (1 / 2 : ℝ) * ∫ f, inner ℝ (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f)
        (smoothTwoFormEuclideanValue (v : smoothTwoForms o) f) ∂canonicalFrameMeasure g o :=
  twoFormFromContinuousTensor_pairing _ v

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Quantitative comparison between local coordinate L² and the actual
normalized Riemannian L² norm. The constant depends only on the compact chart
set and metric, not on the scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalarChart_eLpNorm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ f : M → ℝ,
      eLpNorm (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) 2
        (volume.restrict K) ≤ C * eLpNorm f 2 (normalizedVolume g) := by
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let S : Set (ChartTarget c) := Subtype.val ⁻¹' K
  let φ : ChartTarget c → M := fun z => (chartAt FourSpace c).symm z.val
  have hS : MeasurableSet S := measurable_subtype_coe hK.isClosed.measurableSet
  have hφ : MeasurableEmbedding φ :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  obtain ⟨δ, hδ, hδK⟩ := scalarChart_density_lower_bound g c hK hKt
  let d := ENNReal.ofReal δ
  have hd₀ : d ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hdtop : d ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  obtain ⟨hF₀, hFtop⟩ := ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)
  have hmeasure : d • μ.restrict S ≤ (μ.withDensity ρ).restrict S := by
    rw [← withDensity_const, restrict_withDensity hS]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with z hz
    exact ENNReal.ofReal_le_ofReal (hδK z.val hz)
  have hdom : μ.restrict S ≤ d⁻¹ • μ.withDensity ρ := by
    calc
      μ.restrict S = d⁻¹ • (d • μ.restrict S) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hd₀ hdtop, one_smul]
      _ ≤ d⁻¹ • (μ.withDensity ρ).restrict S := smul_le_smul_left _ hmeasure
      _ ≤ d⁻¹ • μ.withDensity ρ := by
        gcongr
        exact Measure.restrict_le_self
  have hbase : Measure.map φ (μ.withDensity ρ) =
      (normalizedChartFactor g)⁻¹ • (normalizedVolume g).restrict (chartAt FourSpace c).source := by
    rw [normalizedVolume_restrict_chart, smul_smul,
      ENNReal.inv_mul_cancel hF₀.ne' hFtop.ne, one_smul]
  let D := d⁻¹ * (normalizedChartFactor g)⁻¹
  have hDtop : D ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr hd₀) (ENNReal.inv_ne_top.mpr hF₀.ne')
  have hmapdom : Measure.map φ (μ.restrict S) ≤ D • normalizedVolume g := by
    calc
      Measure.map φ (μ.restrict S) ≤ Measure.map φ (d⁻¹ • μ.withDensity ρ) :=
        Measure.map_mono hdom hφ.measurable
      _ = D • (normalizedVolume g).restrict (chartAt FourSpace c).source := by
        rw [Measure.map_smul, hbase, smul_smul]
      _ ≤ D • normalizedVolume g := by
        gcongr
        exact Measure.restrict_le_self
  have he := MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet
  have hmap : Measure.map (Subtype.val : ChartTarget c → FourSpace) (μ.restrict S) =
      volume.restrict K := by
    rw [← he.restrict_map]
    change (Measure.map Subtype.val (Measure.comap Subtype.val volume)).restrict K = _
    rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet,
      inter_eq_left.mpr hKt]
  refine ⟨D ^ (1 / (2 : ℝ≥0∞)).toReal, ?_, ?_⟩
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hDtop
  · intro f
    rw [← hmap, he.eLpNorm_map_measure]
    change eLpNorm (f ∘ φ) 2 (μ.restrict S) ≤ _
    rw [← hφ.eLpNorm_map_measure]
    exact eLpNorm_le_of_measure_le_smul hmapdom

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reverse chart norm control on a compact coordinate set. This is the
measure comparison needed to assemble local Sobolev estimates on the base. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalarChart_reverse_eLpNorm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ D : ℝ≥0∞, D ≠ (∞ : ℝ≥0∞) ∧ ∀ (p : ℝ≥0∞) (f : M → ℝ),
      support f ⊆ (chartAt FourSpace c).symm '' K →
      eLpNorm f p (normalizedVolume g) ≤ D ^ (1 / p).toReal *
        eLpNorm (fun z => f ((chartAt FourSpace c).symm z)) p (volume.restrict K) := by
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let T : Set (ChartTarget c) := Subtype.val ⁻¹' K
  let φ : ChartTarget c → M := fun z => (chartAt FourSpace c).symm z.val
  have hT : MeasurableSet T := measurable_subtype_coe hK.isClosed.measurableSet
  have hφ : MeasurableEmbedding φ :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  have hS : MeasurableSet (φ '' T) := hφ.measurableSet_image' hT
  have hsource : φ '' T ⊆ (chartAt FourSpace c).source := by
    rintro _ ⟨z, _, rfl⟩
    exact (chartAt FourSpace c).map_target z.property
  have himage : φ '' T = (chartAt FourSpace c).symm '' K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hKt hz⟩, hz, rfl⟩
  have hρcont : ContinuousOn (fun z => chartVolumeDensity g c z) K :=
    fun z hz => (chartVolumeDensity_contDiffAt g c z (hKt hz)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hρcont).isBounded.exists_norm_le
  let b := ENNReal.ofReal (max B 0)
  have hdom : (μ.withDensity ρ).restrict T ≤ b • μ.restrict T := by
    rw [← withDensity_const, restrict_withDensity hT]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hT] with z hz
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans ((hB _ ⟨z.val, hz, rfl⟩).trans (le_max_left _ _))
  have hbase : (normalizedVolume g).restrict (φ '' T) =
      normalizedChartFactor g • Measure.map φ ((μ.withDensity ρ).restrict T) := by
    calc
      _ = ((normalizedVolume g).restrict (chartAt FourSpace c).source).restrict (φ '' T) := by
        rw [Measure.restrict_restrict hS, inter_eq_left.mpr hsource]
      _ = _ := by
        rw [normalizedVolume_restrict_chart, Measure.restrict_smul, hφ.restrict_map,
          hφ.injective.preimage_image]
  let D := normalizedChartFactor g * b
  have hD : D ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top
    (ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)).2.ne ENNReal.ofReal_ne_top
  have hmeasure : (normalizedVolume g).restrict (φ '' T) ≤
      D • Measure.map φ (μ.restrict T) := by
    rw [hbase]
    calc
      _ ≤ normalizedChartFactor g • Measure.map φ (b • μ.restrict T) :=
        smul_le_smul_left _ (Measure.map_mono hdom hφ.measurable)
      _ = _ := by rw [Measure.map_smul, smul_smul]
  have he := MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet
  have hmap : Measure.map (Subtype.val : ChartTarget c → FourSpace) (μ.restrict T) =
      volume.restrict K := by
    rw [← he.restrict_map]
    change (Measure.map Subtype.val (Measure.comap Subtype.val volume)).restrict K = _
    rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_eq_left.mpr hKt]
  refine ⟨D, hD, fun p f hf => ?_⟩
  have hind : (φ '' T).indicator f = f := indicator_eq_self.mpr (himage.symm ▸ hf)
  have hn := eLpNorm_le_of_measure_le_smul (f := f) (p := p) hmeasure
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hS, hind,
    hφ.eLpNorm_map_measure] at hn
  have hright : eLpNorm (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) p
      (volume.restrict K) = eLpNorm (f ∘ φ) p (μ.restrict T) := by
    rw [← hmap, he.eLpNorm_map_measure]
    rfl
  rwa [hright]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual chart integral formulas for the L2 and covariant energy
pairings against a compactly supported orthonormal-frame test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set Function
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGramTest_support (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) :
    tsupport (twoFormGramTest o c S a ha hK hKt has).val ⊆ (chartAt FourSpace c).symm '' K :=
  twoFormChartTest_support c _ _ _ hK hKt _

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_gramTest (u : smoothTwoForms o)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) :
    smoothTwoFormL2Inner u (twoFormGramTest o c S a ha hK hKt has) =
      (normalizedChartFactor g).toReal * ∫ z in (chartAt FourSpace c).target,
        chartVolumeDensity g c z * inner ℝ (twoFormChartValue o u.val c S hS z) (a z) := by
  unfold smoothTwoFormL2Inner
  rw [normalizedVolume_integral_chart g c _ (by
    intro x hx
    have hn : x ∉ tsupport (twoFormGramTest o c S a ha hK hKt has).val := by
      intro h
      obtain ⟨z, hz, rfl⟩ := twoFormGramTest_support c S a ha hK hKt has h
      exact hx ((chartAt FourSpace c).map_target (hKt hz))
    rw [image_eq_zero_of_notMem_tsupport hn, inner_zero_right])]
  congr 1
  apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  have he := twoFormFrameValue_inner (o := o) u.val
    (twoFormGramTest o c S a ha hK hKt has).val (chartGramSection g c S hS ⟨z, hz⟩)
  change inner ℝ (twoFormFrameValue o u.val (chartGramSection g c S hS ⟨z, hz⟩))
    (twoFormFrameValue o (twoFormGramTest o c S a ha hK hKt has).val
      (chartGramSection g c S hS ⟨z, hz⟩)) =
    inner ℝ (u.val ((chartAt FourSpace c).symm z))
      ((twoFormGramTest o c S a ha hK hKt has).val ((chartAt FourSpace c).symm z)) at he
  have he' : inner ℝ (twoFormChartValue o u.val c S hS z)
      (twoFormChartValue o (twoFormGramTest o c S a ha hK hKt has).val c S hS z) =
      inner ℝ (u.val ((chartAt FourSpace c).symm z))
        ((twoFormGramTest o c S a ha hK hKt has).val ((chartAt FourSpace c).symm z)) := by
    simpa only [twoFormChartValue, dite_eq_left hz] using he
  rw [twoFormGramTest_value c S hS a ha hK hKt has z hz] at he'
  exact congrArg (fun r : ℝ => chartVolumeDensity g c z * r) he'.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded extension of the metric's actual curvature action to L2
two-forms. No bound on curvature is an additional input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormL2Curvature_smooth (u : SmoothL2TwoForm o) :
    twoFormL2Curvature (smoothTwoFormToL2 u) = smoothTwoFormToL2 (smoothL2Curvature u) :=
  ContinuousLinearMap.completion_apply_coe _ u

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer of the intrinsic two-form H1 control to supported scalar
functions on a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.twoFormLocalization_probability
theorem twoForm_chart_localization_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u : SmoothH1TwoForm o) (f : FourSpace → ℝ)
      (hf : MemLp f 2 (volume : Measure FourSpace)) (C : ℝ), 0 ≤ C →
      Function.support f ⊆ K →
      (∀ z ∈ K, |f z| ≤ C * twoFormControl (u : smoothTwoForms o) ((chartAt FourSpace c).symm z)) →
      ‖hf.toLp f‖ ≤ C * L * ‖u‖ := by
  obtain ⟨D, hD, hDb⟩ := scalarChart_eLpNorm_bound g c hK hKt
  refine ⟨2 * D.toReal, mul_nonneg (by norm_num) ENNReal.toReal_nonneg, ?_⟩
  intro u f hf C hC hs hb
  let F := twoFormControl (u : smoothTwoForms o)
  have hF : MemLp F 2 (normalizedVolume g) :=
    F.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfi : K.indicator f = f := indicator_eq_self.mpr hs
  have hlocal : eLpNorm f 2 volume ≤ ENNReal.ofReal C *
      eLpNorm (fun z => F ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) := by
    calc
      _ = eLpNorm f 2 (volume.restrict K) := by
        conv_lhs => rw [← hfi]
        exact eLpNorm_indicator_eq_eLpNorm_restrict hK.isClosed.measurableSet
      _ ≤ _ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
        filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ F ((chartAt FourSpace c).symm z) from twoFormControl_nonneg _ _)]
        exact hb z hz) 2
  have htotal := hlocal.trans (mul_le_mul' le_rfl (hDb F))
  have hfinite : ENNReal.ofReal C * (D * eLpNorm F 2 (normalizedVolume g)) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hD hF.eLpNorm_ne_top)
  have hr := ENNReal.toReal_mono hfinite htotal
  have hnorm : (eLpNorm F 2 (normalizedVolume g)).toReal =
      ‖twoFormControlL2 (u : smoothTwoForms o)‖ := by
    change (eLpNorm F 2 (normalizedVolume g)).toReal = ‖hF.toLp F‖
    exact (Lp.norm_toLp F hF).symm
  rw [← Lp.norm_toLp f hf] at hr
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, hnorm] at hr
  calc
    ‖hf.toLp f‖ ≤ C * (D.toReal * ‖twoFormControlL2 (u : smoothTwoForms o)‖) := hr
    _ ≤ C * (D.toReal * (2 * ‖u‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (twoFormControlL2_norm_le u) ENNReal.toReal_nonneg) hC
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature operator is self-adjoint for the intrinsic L2
pairing; symmetry follows from the metric curvature symmetries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormMetricCurvatureAction_symmetric (e : FrameBundle g) (a b : TwoFormFour) :
    inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) a) b =
      inner ℝ a (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) b) := by
  apply twoFormCurvatureAction_symmetric
  · intro i j k l
    change frameTensor e.frame.matrix _ ![i,j,l,k] = -frameTensor e.frame.matrix _ ![i,j,k,l]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  · intro i j k l
    change frameTensor e.frame.matrix _ ![k,l,i,j] = frameTensor e.frame.matrix _ ![i,j,k,l]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

theorem smoothL2Curvature_inner (u v : SmoothL2TwoForm o) :
    inner ℝ (smoothL2Curvature u) v = inner ℝ u (smoothL2Curvature v) := by
  change (∫ x, inner ℝ (twoFormCurvatureField o (u : smoothTwoForms o).val x)
    ((v : smoothTwoForms o).val x) ∂normalizedVolume g) =
      ∫ x, inner ℝ ((u : smoothTwoForms o).val x)
        (twoFormCurvatureField o (v : smoothTwoForms o).val x) ∂normalizedVolume g
  apply integral_congr_ae
  filter_upwards [] with x
  exact twoFormMetricCurvatureAction_symmetric ⟨x,o.frame x⟩ _ _

theorem twoFormL2Curvature_selfAdjoint (u v : TwoFormL2 o) :
    inner ℝ (twoFormL2Curvature u) v = inner ℝ u (twoFormL2Curvature v) := by
  have hs (b : SmoothL2TwoForm o) (a : TwoFormL2 o) :
      inner ℝ (twoFormL2Curvature a) (smoothTwoFormToL2 b) =
        inner ℝ a (twoFormL2Curvature (smoothTwoFormToL2 b)) := by
    refine UniformSpace.Completion.induction_on a
      (isClosed_eq (twoFormL2Curvature.continuous.inner continuous_const)
        (continuous_id.inner continuous_const)) ?_
    intro w
    change inner ℝ (twoFormL2Curvature (smoothTwoFormToL2 w)) (smoothTwoFormToL2 b) =
      inner ℝ (smoothTwoFormToL2 w) (twoFormL2Curvature (smoothTwoFormToL2 b))
    rw [twoFormL2Curvature_smooth, twoFormL2Curvature_smooth,
      smoothTwoFormToL2.inner_map_map, smoothTwoFormToL2.inner_map_map]
    exact smoothL2Curvature_inner w b
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner twoFormL2Curvature.continuous)) ?_
  intro b
  exact hs b u

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

/-! Uniform first-jet bounds for each compact chart cutoff of a two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCutoffC1_control (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (u : SmoothH1TwoForm o) (a : Fin 2 → Fin 4) (z : FourSpace), z ∈ K →
      |(twoFormCutoffC1 c hKt χ hχ hc hs a u).val z| ≤
        B * twoFormControl (u : smoothTwoForms o) ((chartAt FourSpace c).symm z) ∧
      ∀ i : Fin 4, |partialDeriv (twoFormCutoffC1 c hKt χ hχ hc hs a u).val i z| ≤
        B * twoFormControl (u : smoothTwoForms o) ((chartAt FourSpace c).symm z) := by
  obtain ⟨A, hA, hAb⟩ := twoFormChart_compact_control g o c hK hKt
  let J : FourSpace → ℝ := fun z => |χ z| + ∑ i : Fin 4, |partialDeriv χ i z|
  have hJ : Continuous J := hχ.continuous.abs.add
    (continuous_finsetSum _ (fun i _ =>
      (((hχ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).continuous).abs))
  obtain ⟨D₀, hD₀⟩ := (hK.image hJ).isBounded.exists_norm_le
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hj (z : FourSpace) (hz : z ∈ K) : J z ≤ D :=
    (le_abs_self _).trans ((hD₀ _ ⟨z, hz, rfl⟩).trans (le_max_left _ _))
  have hval (z : FourSpace) (hz : z ∈ K) : |χ z| ≤ D :=
    (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans (hj z hz)
  have hder (z : FourSpace) (hz : z ∈ K) (i : Fin 4) : |partialDeriv χ i z| ≤ D := by
    have hi : |partialDeriv χ i z| ≤ ∑ j : Fin 4, |partialDeriv χ j z| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (partialDeriv χ j z)) (Finset.mem_univ i)
    exact (hi.trans (le_add_of_nonneg_left (abs_nonneg (χ z)))).trans (hj z hz)
  refine ⟨2 * D * A, by positivity, fun u a z hz => ?_⟩
  have hu := hAb (u : smoothTwoForms o).val (u : smoothTwoForms o).property z hz
  let F := twoFormControl (u : smoothTwoForms o) ((chartAt FourSpace c).symm z)
  have hF : 0 ≤ F := twoFormControl_nonneg _ _
  have hV : ‖(u : smoothTwoForms o).val ((chartAt FourSpace c).symm z)‖ ≤ F :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hcoeff : |twoFormCoordinates o (u : smoothTwoForms o).val c z a| ≤ A * F :=
    (hu.1 a).trans (mul_le_mul_of_nonneg_left hV hA)
  have hpartial (i : Fin 4) :
      |partialDeriv (fun w => twoFormCoordinates o (u : smoothTwoForms o).val c w a) i z| ≤ A * F :=
    hu.2 i a
  refine ⟨?_, fun i => ?_⟩
  · change |χ z * twoFormCoordinates o (u : smoothTwoForms o).val c z a| ≤ _
    rw [abs_mul]
    calc
      _ ≤ D * (A * F) := mul_le_mul (hval z hz) hcoeff (abs_nonneg _) hD
      _ ≤ (2 * D * A) * F := by nlinarith [mul_nonneg hD (mul_nonneg hA hF)]
  · rw [twoFormCutoffC1_partial]
    calc
      _ ≤ |χ z * partialDeriv (fun w => twoFormCoordinates o (u : smoothTwoForms o).val c w a) i z| +
          |partialDeriv χ i z * twoFormCoordinates o (u : smoothTwoForms o).val c z a| := abs_add_le _ _
      _ ≤ D * (A * F) + D * (A * F) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (hval z hz) (hpartial i) (abs_nonneg _) hD)
          (mul_le_mul (hder z hz i) hcoeff (abs_nonneg _) hD)
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded reconstruction of a compactly supported Euclidean chart
function into the actual base L² space. Null sets are respected by the
proved reverse chart norm comparison. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.reconstruction_baseProbability
theorem scalarChartReconstruction_eLpNorm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ A : ℝ≥0∞, A ≠ (∞ : ℝ≥0∞) ∧ ∀ f : FourSpace → ℝ,
      eLpNorm (scalarChartReconstructionFun c K f) 2 (normalizedVolume g) ≤
        A * eLpNorm f 2 volume := by
  obtain ⟨D, hD, hDb⟩ := scalarChart_reverse_eLpNorm_bound g c hK hKt
  let A : ℝ≥0∞ := D ^ ((1 / (2 : ℝ≥0∞)).toReal)
  refine ⟨A, ENNReal.rpow_ne_top_of_nonneg (by norm_num) hD, fun f => ?_⟩
  have hs : support (scalarChartReconstructionFun c K f) ⊆
      (chartAt FourSpace c).symm '' K := by
    intro x hx
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  have he : (fun z => scalarChartReconstructionFun c K f ((chartAt FourSpace c).symm z))
      =ᵐ[volume.restrict K] f := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact scalarChartReconstructionFun_chart c hKt f hz
  calc
    _ ≤ A * eLpNorm (fun z => scalarChartReconstructionFun c K f
        ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) := hDb 2 _ hs
    _ = A * eLpNorm f 2 (volume.restrict K) := by rw [eLpNorm_congr_ae he]
    _ ≤ _ := mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)

theorem scalarChartReconstructionFun_ae (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    {f h : FourSpace → ℝ} (he : f =ᵐ[volume] h) :
    scalarChartReconstructionFun c K f =ᵐ[normalizedVolume g]
      scalarChartReconstructionFun c K h := by
  obtain ⟨A, _, hA⟩ := scalarChartReconstruction_eLpNorm_bound g c hK hKt
  -- route through a measurable null set (eLpNorm of a non-measurable function does not see its a.e. class)
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null
    (show (volume : Measure FourSpace) {x | f x ≠ h x} = 0 from he)
  have hv := hA (Z.indicator fun _ => (1 : ℝ))
  have hv0 : eLpNorm (Z.indicator fun _ => (1 : ℝ)) 2 (volume : Measure FourSpace) = 0 := by
    rw [eLpNorm_eq_zero_iff ((measurable_const.indicator hZm).aestronglyMeasurable) (by norm_num)]
    filter_upwards [compl_mem_ae_iff.mpr hZ0] with x hx
    simp [Set.indicator_of_notMem hx]
  have hz : eLpNorm (scalarChartReconstructionFun c K (Z.indicator fun _ => (1 : ℝ))) 2
      (normalizedVolume g) = 0 := by
    apply le_antisymm _ zero_le
    simpa [hv0] using hv
  have hmz : Measurable (Z.indicator fun _ : FourSpace => (1 : ℝ)) := measurable_const.indicator hZm
  have hzm : AEStronglyMeasurable (scalarChartReconstructionFun c K (Z.indicator fun _ : FourSpace => (1 : ℝ)))
      (normalizedVolume g) :=
    (scalarChartReconstructionFun_stronglyMeasurable c hK hKt hmz.stronglyMeasurable).aestronglyMeasurable
  have hz0 := (eLpNorm_eq_zero_iff hzm (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hz
  filter_upwards [hz0] with x hx
  by_cases hxK : x ∈ (chartAt FourSpace c).symm '' K
  · have hxZ : (chartAt FourSpace c x) ∉ Z := by
      intro hmem
      simp [scalarChartReconstructionFun, Set.indicator_of_mem hxK, Set.indicator_of_mem hmem] at hx
    have hfh : f (chartAt FourSpace c x) = h (chartAt FourSpace c x) := by
      by_contra hne
      exact hxZ (hZsub hne)
    simp [scalarChartReconstructionFun, Set.indicator_of_mem hxK, hfh]
  · simp [scalarChartReconstructionFun, Set.indicator_of_notMem hxK]

theorem scalarChartReconstruction_memLp (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    MemLp (scalarChartReconstructionFun c K f) 2 (normalizedVolume g) := by
  obtain ⟨A, hA, hAb⟩ := scalarChartReconstruction_eLpNorm_bound g c hK hKt
  exact ⟨(scalarChartReconstructionFun_stronglyMeasurable c hK hKt
    (Lp.stronglyMeasurable f)).aestronglyMeasurable, lt_of_le_of_lt (hAb f)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hA (Lp.eLpNorm_ne_top f)))⟩

def scalarChartReconstructionLp (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) : Lp ℝ 2 (normalizedVolume g) :=
  (scalarChartReconstruction_memLp g c hK hKt f).toLp _

theorem scalarChartReconstructionLp_coe (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarChartReconstructionLp g c hK hKt f =ᵐ[normalizedVolume g]
      scalarChartReconstructionFun c K f := MemLp.coeFn_toLp _

def scalarChartReconstructionLinear (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (volume : Measure FourSpace) →ₗ[ℝ] Lp ℝ 2 (normalizedVolume g) where
  toFun := scalarChartReconstructionLp g c hK hKt
  map_add' f h := by
    apply Lp.ext
    have he := scalarChartReconstructionFun_ae g c hK hKt (Lp.coeFn_add f h)
    filter_upwards [scalarChartReconstructionLp_coe g c hK hKt (f + h),
      scalarChartReconstructionLp_coe g c hK hKt f,
      scalarChartReconstructionLp_coe g c hK hKt h,
      Lp.coeFn_add (scalarChartReconstructionLp g c hK hKt f)
        (scalarChartReconstructionLp g c hK hKt h), he] with x hsum hf hh hLp heq
    rw [hsum, hLp, Pi.add_apply, hf, hh, heq]
    exact congrFun (scalarChartReconstructionFun_add c K f h) x
  map_smul' r f := by
    apply Lp.ext
    have he := scalarChartReconstructionFun_ae g c hK hKt (Lp.coeFn_smul r f)
    filter_upwards [scalarChartReconstructionLp_coe g c hK hKt (r • f),
      scalarChartReconstructionLp_coe g c hK hKt f,
      Lp.coeFn_smul r (scalarChartReconstructionLp g c hK hKt f), he]
        with x hrf hf hLp heq
    simp only [RingHom.id_apply]
    rw [hrf, hLp, Pi.smul_apply, hf, heq]
    exact congrFun (scalarChartReconstructionFun_smul c K r f) x

theorem scalarChartReconstructionLinear_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, ∀ f : Lp ℝ 2 (volume : Measure FourSpace),
      ‖scalarChartReconstructionLinear g c hK hKt f‖ ≤ C * ‖f‖ := by
  obtain ⟨A, hA, hAb⟩ := scalarChartReconstruction_eLpNorm_bound g c hK hKt
  refine ⟨A.toReal, fun f => ?_⟩
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.eLpNorm_ne_top f)) (hAb f)
  change ‖(scalarChartReconstruction_memLp g c hK hKt f).toLp
    (scalarChartReconstructionFun c K f)‖ ≤ _
  rw [Lp.norm_toLp]
  simpa only [Lp.norm_def, ENNReal.toReal_mul] using hr

/-- Reconstruction through a compact coordinate set, in actual base volume. -/
def scalarChartReconstruction (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarChartReconstructionLinear g c hK hKt).mkContinuousOfExistsBound
    (scalarChartReconstructionLinear_bound g c hK hKt)

theorem scalarChartReconstruction_coe (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarChartReconstruction g c hK hKt f =ᵐ[normalizedVolume g]
      scalarChartReconstructionFun c K f := scalarChartReconstructionLp_coe g c hK hKt f

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact chart first jet is bounded by the intrinsic
two-form H1 norm, uniformly over smooth sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCutoff_jet_bound (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SmoothH1TwoForm o) (a : Fin 2 → Fin 4),
      ‖ScalarEuclideanSobolev.valueL2 (twoFormCutoffC1 c hKt χ hχ hc hs a u)‖ ≤ C * ‖u‖ ∧
      ‖ScalarEuclideanSobolev.gradientL2 (twoFormCutoffC1 c hKt χ hχ hc hs a u)‖ ≤ C * ‖u‖ := by
  obtain ⟨B, hB, hBb⟩ := twoFormCutoffC1_control (o := o) c hK hKt χ hχ hc hs
  obtain ⟨L, hL, hLb⟩ := twoForm_chart_localization_bound g o c hK hKt
  refine ⟨4 * B * L, by positivity, fun u a => ?_⟩
  let f := twoFormCutoffC1 c hKt χ hχ hc hs a u
  have hfs : tsupport f.val ⊆ K := twoFormCutoffC1_support c hKt χ hχ hc hs a u
  have hval : ‖ScalarEuclideanSobolev.valueL2 f‖ ≤ B * L * ‖u‖ := by
    exact hLb u f.val (f.property.1.continuous.memLp_of_hasCompactSupport f.property.2)
      B hB ((subset_tsupport f.val).trans hfs) (fun z hz => (hBb u a z hz).1)
  have hpartial (i : Fin 4) : ‖ScalarEuclideanSobolev.partialL2 f i‖ ≤ B * L * ‖u‖ := by
    have hf : MemLp (partialDeriv f.val i) 2 (volume : Measure FourSpace) :=
      (ScalarEuclideanSobolev.continuous_partial f.property.1 i).memLp_of_hasCompactSupport
      (f.property.2.fderiv_apply ℝ (coordinateVector i))
    exact hLb u (partialDeriv f.val i) hf B hB
      ((subset_tsupport (partialDeriv f.val i)).trans
        ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hfs))
      (fun z hz => (hBb u a z hz).2 i)
  have hnonneg : 0 ≤ B * L * ‖u‖ := mul_nonneg (mul_nonneg hB hL) (norm_nonneg _)
  refine ⟨hval.trans (by nlinarith only [hnonneg]), ?_⟩
  calc
    _ ≤ ∑ i : Fin 4, ‖ScalarEuclideanSobolev.partialL2 f i‖ :=
      ScalarEuclideanSobolev.gradientL2_norm_le_sum f
    _ ≤ ∑ _i : Fin 4, B * L * ‖u‖ := Finset.sum_le_sum (fun i _ => hpartial i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Critical L4 control of the finite Bessel jets retaining one derivative. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv Set
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "L4" => Lp ℂ 4 (volume : Measure V)

variable (n : ℕ) (is : List (Fin 4)) (h1 : is.length + 1 ≤ n)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_8
def jetL4Linear : L2 →ₗ[ℂ] L4 where
  toFun f := (scalarBesselJetL2_memLp_four n is h1 f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(scalarBesselJetL2_memLp_four n is h1 (f + g)).coeFn_toLp,
      (scalarBesselJetL2_memLp_four n is h1 f).coeFn_toLp,
      (scalarBesselJetL2_memLp_four n is h1 g).coeFn_toLp,
      Lp.coeFn_add (l4JetL2 n is h1 f) (l4JetL2 n is h1 g),
      Lp.coeFn_add ((scalarBesselJetL2_memLp_four n is h1 f).toLp _)
        ((scalarBesselJetL2_memLp_four n is h1 g).toLp _)] with x hfg hf hg h2 h4
    rw [hfg, h4, Pi.add_apply, hf, hg, map_add]
    exact h2
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(scalarBesselJetL2_memLp_four n is h1 (c • f)).coeFn_toLp,
      (scalarBesselJetL2_memLp_four n is h1 f).coeFn_toLp,
      Lp.coeFn_smul c (l4JetL2 n is h1 f),
      Lp.coeFn_smul c ((scalarBesselJetL2_memLp_four n is h1 f).toLp _)] with x hcf hf h2 h4
    rw [hcf, h4, Pi.smul_apply, hf, map_smul]
    exact h2

theorem jetL4Linear_coe (f : L2) :
    (jetL4Linear n is h1 f : V → ℂ) =ᵐ[volume] l4JetL2 n is h1 f :=
  (scalarBesselJetL2_memLp_four n is h1 f).coeFn_toLp

def scalarBesselJetL4 : L2 →L[ℂ] L4 where
  toLinearMap := jetL4Linear n is h1
  cont := (jetL4Linear n is h1).continuous_of_seq_closed_graph (by
    intro f x y hfx hfy
    have hlow := tendstoInMeasure_of_tendsto_Lp
      ((l4JetL2 n is h1).continuous.continuousAt.tendsto.comp hfx)
    have hhigh := tendstoInMeasure_of_tendsto_Lp hfy
    have hlow' : TendstoInMeasure volume
        (fun k => (jetL4Linear n is h1 (f k) : V → ℂ)) atTop
        (l4JetL2 n is h1 x : V → ℂ) :=
      hlow.congr (fun k => (jetL4Linear_coe n is h1 (f k)).symm) Filter.EventuallyEq.rfl
    apply Lp.ext
    exact (tendstoInMeasure_ae_unique hhigh hlow').trans
      (jetL4Linear_coe n is h1 x).symm)

theorem scalarBesselJetL4_coe (f : L2) :
    (scalarBesselJetL4 n is h1 f : V → ℂ) =ᵐ[volume]
      scalarBesselJetL2 n is (by omega) f := jetL4Linear_coe n is h1 f

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFourSpace_1
local instance instBorelSpaceFourSpace_1 : BorelSpace FourSpace := ⟨rfl⟩
local instance instMeasureSpaceFourSpace_1 : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) {K : Set FourSpace} (hK : IsCompact K)
  (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4)

def smoothTwoFormCutoffJet : SmoothH1TwoForm o →ₗ[ℝ]
    Euclidean.H1Target (μ := (volume : Measure FourSpace)) :=
  (Euclidean.graph (μ := (volume : Measure FourSpace))).comp
    (twoFormCutoffC1 c hKt χ hχ hc hs a)

include hK in
theorem smoothTwoFormCutoffJet_bound : ∃ C : ℝ, ∀ u : SmoothH1TwoForm o,
    ‖smoothTwoFormCutoffJet c hKt χ hχ hc hs a u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, _, hC⟩ := twoFormCutoff_jet_bound (o := o) c hK hKt χ hχ hc hs
  refine ⟨C, fun u => ?_⟩
  let f := twoFormCutoffC1 c hKt χ hχ hc hs a u
  change ‖(Euclidean.toL2 (μ := (volume : Measure FourSpace)) f,
    Euclidean.toL2Grad (μ := (volume : Measure FourSpace)) f)‖ ≤ _
  rw [Prod.norm_def]
  apply max_le
  · rw [← scalarBorel_valueL2 f, (scalarBorelLpEquiv ℝ 2).norm_map]
    exact (hC u a).1
  · rw [← scalarBorel_gradientL2 f, (scalarBorelLpEquiv FourSpace 2).norm_map]
    exact (hC u a).2

def smoothTwoFormCutoffJetCLM : SmoothH1TwoForm o →L[ℝ]
    Euclidean.H1Target (μ := (volume : Measure FourSpace)) :=
  (smoothTwoFormCutoffJet c hKt χ hχ hc hs a).mkContinuousOfExistsBound
    (smoothTwoFormCutoffJet_bound c hK hKt χ hχ hc hs a)

def twoFormCutoffJet : TwoFormH1 o →L[ℝ]
    Euclidean.H1Target (μ := (volume : Measure FourSpace)) :=
  (smoothTwoFormCutoffJetCLM c hK hKt χ hχ hc hs a).fromCompletion

theorem twoFormCutoffJet_smooth (u : SmoothH1TwoForm o) :
    twoFormCutoffJet c hK hKt χ hχ hc hs a (smoothTwoFormToH1 u) =
      Euclidean.graph (μ := (volume : Measure FourSpace))
        (twoFormCutoffC1 c hKt χ hχ hc hs a u) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem twoFormCutoffJet_mem (u : TwoFormH1 o) :
    twoFormCutoffJet c hK hKt χ hχ hc hs a u ∈
      Euclidean.h1 (μ := (volume : Measure FourSpace)) := by
  refine UniformSpace.Completion.induction_on u
    ((Euclidean.isClosed_h1 (μ := (volume : Measure FourSpace))).preimage
      (twoFormCutoffJet c hK hKt χ hχ hc hs a).continuous) ?_
  intro v
  change twoFormCutoffJet c hK hKt χ hχ hc hs a (smoothTwoFormToH1 v) ∈ _
  rw [twoFormCutoffJet_smooth]
  exact Submodule.le_topologicalClosure _ ⟨_, rfl⟩

def twoFormCutoffEuclideanH1 : TwoFormH1 o →L[ℝ]
    ↥(Euclidean.h1 (μ := (volume : Measure FourSpace))) :=
  (twoFormCutoffJet c hK hKt χ hχ hc hs a).codRestrict _
    (twoFormCutoffJet_mem c hK hKt χ hχ hc hs a)

theorem twoFormCutoffEuclideanH1_supported (u : TwoFormH1 o) :
    twoFormCutoffEuclideanH1 c hK hKt χ hχ hc hs a u ∈
      Euclidean.h1On K hK.isClosed.measurableSet := by
  refine UniformSpace.Completion.induction_on u
    ((Euclidean.isClosed_range_extendByZero K hK.isClosed.measurableSet).preimage
      ((Euclidean.h1ToL2 (μ := (volume : Measure FourSpace))).comp
        (twoFormCutoffEuclideanH1 c hK hKt χ hχ hc hs a)).continuous) ?_
  intro v
  change (twoFormCutoffJet c hK hKt χ hχ hc hs a (smoothTwoFormToH1 v)).1 ∈
    LinearMap.range ((Lp.extendByZeroₗᵢ (μ := (volume : Measure FourSpace))
      (E := ℝ) (p := 2) (s := K) hK.isClosed.measurableSet).toLinearMap)
  rw [twoFormCutoffJet_smooth]
  exact Euclidean.mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset
    (μ := (volume : Measure FourSpace)) hK.isClosed.measurableSet _
    (Euclidean.memLp_of_mem_C1c (μ := (volume : Measure FourSpace))
      (twoFormCutoffC1 c hKt χ hχ hc hs a v).property)
    (twoFormCutoffC1_support c hKt χ hχ hc hs a v)

def twoFormCutoffSupportedH1 : TwoFormH1 o →L[ℝ]
    ↥(Euclidean.h1On K hK.isClosed.measurableSet) :=
  (twoFormCutoffEuclideanH1 c hK hKt χ hχ hc hs a).codRestrict _
    (twoFormCutoffEuclideanH1_supported c hK hKt χ hχ hc hs a)

def twoFormCutoffValueL2 : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (Euclidean.h1OnToL2 K hK.isClosed.measurableSet).comp
    (twoFormCutoffSupportedH1 c hK hKt χ hχ hc hs a)

theorem twoFormCutoffValueL2_compact :
    IsCompactOperator (twoFormCutoffValueL2 (o := o) c hK hKt χ hχ hc hs a) :=
  (Euclidean.isCompactOperator_h1OnToL2 hK hK.isClosed.measurableSet).comp_clm
    (twoFormCutoffSupportedH1 c hK hKt χ hχ hc hs a)

theorem twoFormCutoffValueL2_smooth (u : SmoothH1TwoForm o) :
    twoFormCutoffValueL2 c hK hKt χ hχ hc hs a (smoothTwoFormToH1 u) =
      Euclidean.toL2 (μ := (volume : Measure FourSpace))
        (twoFormCutoffC1 c hKt χ hχ hc hs a u) := by
  change (twoFormCutoffJet c hK hKt χ hχ hc hs a (smoothTwoFormToH1 u)).1 = _
  rw [twoFormCutoffJet_smooth]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth partitions and the self-adjoint scalar multiplication
identity in the actual two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_product_inner (ρ : SmoothScalar (M := M)) (u v : smoothTwoForms o) :
    inner ℝ (smoothTwoFormToL2 (smoothTwoFormProduct ρ u : SmoothL2TwoForm o))
      (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) =
    inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
      (smoothTwoFormToL2 (smoothTwoFormProduct ρ v : SmoothL2TwoForm o)) := by
  have he : @inner ℝ (SmoothL2TwoForm o) _ (smoothTwoFormProduct ρ u) v =
      @inner ℝ (SmoothL2TwoForm o) _ u (smoothTwoFormProduct ρ v) := by
    change smoothTwoFormL2Inner (smoothTwoFormProduct ρ u) v =
      smoothTwoFormL2Inner u (smoothTwoFormProduct ρ v)
    unfold smoothTwoFormL2Inner
    apply integral_congr_ae
    filter_upwards [] with x
    change inner ℝ (ρ.val x • u.val x) (v.val x) = inner ℝ (u.val x) (ρ.val x • v.val x)
    rw [real_inner_smul_left, real_inner_smul_right]
  exact (smoothTwoFormToL2.inner_map_map _ _).trans
    (he.trans (smoothTwoFormToL2.inner_map_map _ _).symm)

theorem twoFormL2_eq_of_smooth_pairings (u v : TwoFormL2 o)
    (h : ∀ w : SmoothL2TwoForm o,
      inner ℝ u (smoothTwoFormToL2 w) = inner ℝ v (smoothTwoFormToL2 w)) : u = v := by
  apply ext_inner_right ℝ
  have he : (fun w : TwoFormL2 o => inner ℝ u w) = fun w => inner ℝ v w :=
    (smoothTwoFormToL2_dense (o := o)).equalizer
      (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (funext h)
  exact congrFun he

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single smooth approximation controls all the finite jets used in the
nonlinear bootstrap, in L2, L4 and L-infinity at their required orders. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_11
theorem scalarSchwartzBesselJet_toLp_four (n : ℕ) (is : List (Fin 4))
    (h1 : is.length + 1 ≤ n) (φ : S) :
    (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).toLp 4 volume =
      scalarBesselJetL4 n is h1 (φ.toLp 2 volume) := by
  apply Lp.ext
  have h2 := (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).coeFn_toLp 2 volume
  rw [scalarSchwartzBesselJet_toLp n is (by omega)] at h2
  filter_upwards [(scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).coeFn_toLp 4 volume,
    scalarBesselJetL4_coe n is h1 (φ.toLp 2 volume), h2] with x hx h4 h2
  exact hx.trans (h2.symm.trans h4.symm)

/-- Density holds simultaneously for every required derivative of the same
smooth sequence, including almost-everywhere convergence of its values. -/
theorem scalar_integer_smooth_approximation (n : ℕ) (u : L2)
    (hu : MemSobolev (n : ℝ) 2 (u : T)) :
    ∃ (v : L2) (fs : ℕ → S), u = scalarIntegerBesselInverse n v ∧
      (∀ᵐ x ∂(volume : Measure V), Tendsto (fun k => fs k x) atTop (𝓝 (u x))) ∧
      Tendsto (fun k => (fs k).toLp 2 volume) atTop (𝓝 u) ∧
      (∀ is hle, Tendsto (fun k => (scalarSchwartzCoordinateJet is (fs k)).toLp 2 volume)
        atTop (𝓝 (scalarBesselJetL2 n is hle v))) ∧
      (∀ is h1, Tendsto (fun k => (scalarSchwartzCoordinateJet is (fs k)).toLp 4 volume)
        atTop (𝓝 (scalarBesselJetL4 n is h1 v))) ∧
      (∀ is h3, Tendsto (fun k => (scalarSchwartzCoordinateJet is (fs k)).toLp ∞ volume)
        atTop (𝓝 (scalarBesselJetUniform n is h3 v))) := by
  obtain ⟨v, φ, heq, hφ, hf⟩ := scalar_integer_Hn_schwartz_approximation n u hu
  let fs : ℕ → S := fun k => scalarSchwartzIntegerBesselInverse n (φ k)
  obtain ⟨ks, hks, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  refine ⟨v, fun k => fs (ks k), heq, ?_, hf.comp hks.tendsto_atTop, ?_, ?_, ?_⟩
  · have hco : ∀ᵐ x ∂(volume : Measure V), ∀ k, (fs (ks k)).toLp 2 volume x = fs (ks k) x :=
      ae_all_iff.mpr (fun k => (fs (ks k)).coeFn_toLp 2 volume)
    filter_upwards [hae, hco] with x hx he
    simpa only [fs, he] using hx
  · intro is hle
    simp only [fs, scalarSchwartzBesselJet_toLp n is hle]
    exact (scalarBesselJetL2 n is hle).continuous.continuousAt.tendsto.comp
      (hφ.comp hks.tendsto_atTop)
  · intro is h1
    simp only [fs, scalarSchwartzBesselJet_toLp_four n is h1]
    exact (scalarBesselJetL4 n is h1).continuous.continuousAt.tendsto.comp
      (hφ.comp hks.tendsto_atTop)
  · intro is h3
    simp only [fs, scalarSchwartzBesselJet_toLp_top n is h3]
    exact (scalarBesselJetUniform n is h3).continuous.continuousAt.tendsto.comp
      (hφ.comp hks.tendsto_atTop)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local two-form components in the original Lebesgue measurable space,
and their bounded reconstruction in the actual normalized base measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormLocalValueL2 (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) :
    TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarBorelLpEquiv ℝ 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (twoFormCutoffValueL2 c hK hKt χ hχ hc hs a)

theorem twoFormLocalValueL2_compact (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) :
    IsCompactOperator (twoFormLocalValueL2 (o := o) c hK hKt χ hχ hc hs a) :=
  (twoFormCutoffValueL2_compact c hK hKt χ hχ hc hs a).clm_comp
    (scalarBorelLpEquiv ℝ 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem twoFormLocalValueL2_smooth (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) (u : SmoothH1TwoForm o) :
    twoFormLocalValueL2 c hK hKt χ hχ hc hs a (smoothTwoFormToH1 u) =
      ScalarEuclideanSobolev.valueL2 (twoFormCutoffC1 c hKt χ hχ hc hs a u) := by
  change (scalarBorelLpEquiv ℝ 2).symm
    (twoFormCutoffValueL2 c hK hKt χ hχ hc hs a (smoothTwoFormToH1 u)) = _
  rw [twoFormCutoffValueL2_smooth, ← scalarBorel_valueL2]
  exact (scalarBorelLpEquiv ℝ 2).symm_apply_apply _

def twoFormReconstructedValue (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) (a : Fin 2 → Fin 4) :
    TwoFormH1 o →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs)).comp
      (twoFormLocalValueL2 c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs) (scalarChartCutoff c ρ)
        (scalarChartCutoff_smooth c ρ hs) (scalarChartCutoff_compact c ρ hs)
        (scalarChartCutoff_support c ρ hs) a)

theorem twoFormReconstructedValue_compact (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) (a : Fin 2 → Fin 4) :
    IsCompactOperator (twoFormReconstructedValue (o := o) c ρ hs a) :=
  (twoFormLocalValueL2_compact c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs) (scalarChartCutoff c ρ)
    (scalarChartCutoff_smooth c ρ hs) (scalarChartCutoff_compact c ρ hs)
    (scalarChartCutoff_support c ρ hs) a).clm_comp
      (scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs))

theorem twoFormReconstructedValue_smooth_coe (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) (a : Fin 2 → Fin 4)
    (u : SmoothH1TwoForm o) :
    twoFormReconstructedValue c ρ hs a (smoothTwoFormToH1 u) =ᵐ[normalizedVolume g]
      fun x => ρ.val x * twoFormCoordinates o (u : smoothTwoForms o).val c (chartAt FourSpace c x) a := by
  let K := scalarChartSupport c ρ
  let f := twoFormCutoffC1 c (scalarChartSupport_subset c ρ hs)
    (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ hs)
    (scalarChartCutoff_compact c ρ hs) (scalarChartCutoff_support c ρ hs) a u
  have hpoint : scalarChartReconstructionFun c K f.val =
      fun x => ρ.val x * twoFormCoordinates o (u : smoothTwoForms o).val c (chartAt FourSpace c x) a := by
    funext x
    by_cases hx : x ∈ (chartAt FourSpace c).symm '' K
    · have hxs : x ∈ (chartAt FourSpace c).source := by
        obtain ⟨z, hz, rfl⟩ := hx
        exact (chartAt FourSpace c).map_target (scalarChartSupport_subset c ρ hs hz)
      change ((chartAt FourSpace c).symm '' K).indicator _ x = _
      rw [indicator_of_mem hx]
      change scalarChartCutoff c ρ (chartAt FourSpace c x) * _ = _
      rw [scalarChartCutoff_apply c ρ hxs]
    · have hρ : ρ.val x = 0 := by
        by_contra hn
        have ht := subset_tsupport ρ.val hn
        exact hx ⟨chartAt FourSpace c x, ⟨x, ht, rfl⟩, (chartAt FourSpace c).left_inv (hs ht)⟩
      change ((chartAt FourSpace c).symm '' K).indicator _ x = _
      rw [indicator_of_notMem hx, hρ, zero_mul]
  change scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs)
    (twoFormLocalValueL2 c (scalarChartSupport_compact c ρ hs)
      (scalarChartSupport_subset c ρ hs) (scalarChartCutoff c ρ)
      (scalarChartCutoff_smooth c ρ hs) (scalarChartCutoff_compact c ρ hs)
      (scalarChartCutoff_support c ρ hs) a (smoothTwoFormToH1 u)) =ᵐ[_] _
  rw [twoFormLocalValueL2_smooth]
  exact (scalarChartReconstruction_coe g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs) (ScalarEuclideanSobolev.valueL2 f)).trans
      ((scalarChartReconstructionFun_ae g c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs) (ScalarEuclideanSobolev.valueL2_coe f)).trans
        (Filter.Eventually.of_forall (congrFun hpoint)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local six-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleFirst_gaussian (B : Fin 4 → HeatMat6)
    (t : ℝ) (ht : t ≠ 0) (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hu : ∀ l, DifferentiableAt ℝ (fun y => u y l) x)
    (hB : ∀ k l, (∑ i : Fin 4, x i * B i k l) = 0) (k : Fin 6) :
    fourHeatBundleFirst B (fun y l => fourHeatGaussian t y * u y l) x k =
      fourHeatGaussian t x * fourHeatBundleFirst B u x k := by
  have hz : (∑ i : Fin 4, ∑ l : Fin 6, x i * B i k l * u x l) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hB]
    simp
  unfold fourHeatBundleFirst
  simp_rw [fourHeatGaussian_amplitude_partial_at t ht _ x (hu _)]
  have he (i : Fin 4) (l : Fin 6) :
      B i k l * (fourHeatGaussian t x *
        (partialDeriv (fun y => u y l) i x - x i / (2 * t) * u x l)) =
      fourHeatGaussian t x * (B i k l * partialDeriv (fun y => u y l) i x) -
        (fourHeatGaussian t x / (2 * t)) * (x i * B i k l * u x l) := by ring
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hz]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real smooth approximations carrying the same higher-order derivative
limits as their complex Fourier construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "L4" => Lp ℝ 4 (volume : Measure V)
local notation "Linf" => Lp ℝ ∞ (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_14
/-- One real sequence controls all finite jets, with L4 and uniform control
at the Sobolev orders used in products. -/
theorem scalar_real_integer_approximation (n : ℕ) (u : L2)
    (hu : MemSobolev (n : ℝ) 2 (scalarComplexL2 u : T)) :
    ∃ (fs : ℕ → S) (G : List (Fin 4) → L2)
      (G4 : List (Fin 4) → L4) (Gtop : List (Fin 4) → Linf),
      (∀ᵐ x ∂(volume : Measure V), Tendsto (fun k => fs k x) atTop (𝓝 (u x))) ∧
      Tendsto (fun k => (fs k).toLp 2 volume) atTop (𝓝 u) ∧
      (∀ is, is.length ≤ n → Tendsto (fun k => (scalarRealSchwartzJet is (fs k)).toLp 2 volume)
        atTop (𝓝 (G is))) ∧
      (∀ is, is.length + 1 ≤ n → Tendsto (fun k => (scalarRealSchwartzJet is (fs k)).toLp 4 volume)
        atTop (𝓝 (G4 is))) ∧
      (∀ is, is.length + 3 ≤ n → Tendsto (fun k => (scalarRealSchwartzJet is (fs k)).toLp ∞ volume)
        atTop (𝓝 (Gtop is))) ∧
      (∀ is, is.length + 1 ≤ n → (G is : V → ℝ) =ᵐ[volume] G4 is) ∧
      (∀ is, is.length + 3 ≤ n → (G is : V → ℝ) =ᵐ[volume] Gtop is) := by
  obtain ⟨v, fs, _, hae, hf, hG, hG4, hGtop⟩ := scalar_integer_smooth_approximation n (scalarComplexL2 u) hu
  let R2 := Complex.reCLM.compLpL 2 (volume : Measure V)
  let R4 := Complex.reCLM.compLpL 4 (volume : Measure V)
  let Rt := Complex.reCLM.compLpL ∞ (volume : Measure V)
  let G : List (Fin 4) → L2 := fun is =>
    if h : is.length ≤ n then R2 (scalarBesselJetL2 n is h v) else 0
  let G4 : List (Fin 4) → L4 := fun is =>
    if h : is.length + 1 ≤ n then R4 (scalarBesselJetL4 n is h v) else 0
  let Gtop : List (Fin 4) → Linf := fun is =>
    if h : is.length + 3 ≤ n then Rt (scalarBesselJetUniform n is h v) else 0
  have hRu : R2 (scalarComplexL2 u) = u := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLp (scalarComplexL2 u), scalarComplexL2_coe u] with x hr hu
    change Complex.reCLM.compLp (scalarComplexL2 u) x = u x
    rw [hr, hu]
    rfl
  refine ⟨fun k => (fs k).postcompCLM Complex.reCLM, G, G4, Gtop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hae, scalarComplexL2_coe u] with x hx he
    have h := Complex.continuous_re.continuousAt.tendsto.comp hx
    change Tendsto (fun k => (fs k x).re) atTop (𝓝 (u x))
    simpa only [he, Complex.ofReal_re, Function.comp_def] using h
  · simp only [scalarSchwartz_re_toLp]
    have ht := R2.continuous.continuousAt.tendsto.comp hf
    simpa only [Function.comp_def, hRu] using! ht
  · intro is hs
    simp only [scalarRealSchwartzJet_re, scalarSchwartz_re_toLp, G, dite_eq_left hs]
    exact R2.continuous.continuousAt.tendsto.comp (hG is hs)
  · intro is hs
    simp only [scalarRealSchwartzJet_re, scalarSchwartz_re_toLp, G4, dite_eq_left hs]
    exact R4.continuous.continuousAt.tendsto.comp (hG4 is hs)
  · intro is hs
    simp only [scalarRealSchwartzJet_re, scalarSchwartz_re_toLp, Gtop, dite_eq_left hs]
    exact Rt.continuous.continuousAt.tendsto.comp (hGtop is hs)
  · intro is hs
    have hs0 : is.length ≤ n := by omega
    simp only [G, G4, dite_eq_left hs, dite_eq_left hs0]
    filter_upwards [Complex.reCLM.coeFn_compLp (scalarBesselJetL2 n is hs0 v),
      Complex.reCLM.coeFn_compLp (scalarBesselJetL4 n is hs v), scalarBesselJetL4_coe n is hs v]
      with x h2 h4 he
    change Complex.reCLM.compLp (scalarBesselJetL2 n is hs0 v) x =
      Complex.reCLM.compLp (scalarBesselJetL4 n is hs v) x
    rw [h2, h4, he]
  · intro is hs
    have hs0 : is.length ≤ n := by omega
    simp only [G, Gtop, dite_eq_left hs, dite_eq_left hs0]
    have heq : (scalarBesselJetUniform n is hs v : V → ℂ) =ᵐ[volume]
        scalarBesselJetL2 n is hs0 v := scalarBesselJetUniform_coe n is hs v
    filter_upwards [Complex.reCLM.coeFn_compLp (scalarBesselJetL2 n is hs0 v),
      Complex.reCLM.coeFn_compLp (scalarBesselJetUniform n is hs v), heq]
      with x h2 ht he
    change Complex.reCLM.compLp (scalarBesselJetL2 n is hs0 v) x =
      Complex.reCLM.compLp (scalarBesselJetUniform n is hs v) x
    rw [h2, ht, he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthonormal-frame coefficients of the actual H1 completion have
compact Euclidean H1 localizations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFourSpace_2
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFourSpace_2
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasureSpaceFourSpace_2
def twoFormGramCutoffJet (c : M) (S : Mat4) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) :
    TwoFormH1 o →L[ℝ] Euclidean.H1Target (μ := (volume : Measure FourSpace)) :=
  ∑ b : Fin 2 → Fin 4,
    twoFormCutoffJet c hK hKt (twoFormGramCutoffWeight g c S χ v b)
      (twoFormGramCutoffWeight_smooth g c S hKt χ hχ hs v b)
      (twoFormGramCutoffWeight_compact g c S χ hc v b)
      ((twoFormGramCutoffWeight_support g c S χ v b).trans hs) b

theorem twoFormGramCutoffJet_smooth (c : M) (S : Mat4) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (u : SmoothH1TwoForm o) :
    twoFormGramCutoffJet c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u) =
      Euclidean.graph (μ := (volume : Measure FourSpace))
        (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u) := by
  simp only [twoFormGramCutoffJet, sum_apply, twoFormCutoffJet_smooth,
    twoFormGramCutoffC1, LinearMap.sum_apply, map_sum]

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

theorem scalar_real_derivative_sobolev (n : ℕ) (u : L2)
    (hu : MemSobolev ((n : ℝ) + 1) 2 (scalarComplexL2 u : T)) (i : Fin 4) :
    ∃ v : L2, scalarCoordinateDerivative i (scalarComplexL2 u : T) =
      (scalarComplexL2 v : T) ∧ MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) := by
  obtain ⟨fs, G, _, _, _, hf, hG, _, _, _, _⟩ :=
    scalar_real_integer_approximation (n + 1) u (by simpa only [Nat.cast_add, Nat.cast_one] using hu)
  have he := scalar_real_jet_limit [i] fs u (G [i]) hf (hG [i] (by simp))
  have he' : scalarCoordinateDerivative i (scalarComplexL2 u : T) =
      (scalarComplexL2 (G [i]) : T) := he
  refine ⟨G [i], he', ?_⟩
  rw [← he']
  simpa only [scalarCoordinateDerivative, add_sub_cancel_right] using
    hu.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual localized orthonormal-frame components and their first
derivatives define complex H1 distributions for elliptic regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped SchwartzMap ENNReal LineDeriv Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace} (hK : IsCompact K)
  (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4)

def twoFormGramValueL2 : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarBorelLpEquiv ℝ 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ (scalarBorelLp ℝ 2) (scalarBorelLp FourSpace 2)).comp
      (twoFormGramCutoffJet c S hK hKt χ hχ hc hs v))

def twoFormGramGradientL2 : TwoFormH1 o →L[ℝ] Lp FourSpace 2 (volume : Measure FourSpace) :=
  (scalarBorelLpEquiv FourSpace 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℝ (scalarBorelLp ℝ 2) (scalarBorelLp FourSpace 2)).comp
      (twoFormGramCutoffJet c S hK hKt χ hχ hc hs v))

def twoFormGramPartialL2 (i : Fin 4) :
    TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarGradientCoordinateL2 i).comp (twoFormGramGradientL2 c S hK hKt χ hχ hc hs v)

theorem twoFormGramValueL2_smooth (u : SmoothH1TwoForm o) :
    twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u) =
      ScalarEuclideanSobolev.valueL2 (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u) := by
  change (scalarBorelLpEquiv ℝ 2).symm
    (twoFormGramCutoffJet c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u)).1 = _
  rw [twoFormGramCutoffJet_smooth]
  change (scalarBorelLpEquiv ℝ 2).symm
    (Euclidean.toL2 (μ := _) (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u)) = _
  rw [← scalarBorel_valueL2]
  exact (scalarBorelLpEquiv ℝ 2).symm_apply_apply _

theorem twoFormGramGradientL2_smooth (u : SmoothH1TwoForm o) :
    twoFormGramGradientL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u) =
      ScalarEuclideanSobolev.gradientL2 (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u) := by
  change (scalarBorelLpEquiv FourSpace 2).symm
    (twoFormGramCutoffJet c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u)).2 = _
  rw [twoFormGramCutoffJet_smooth]
  change (scalarBorelLpEquiv FourSpace 2).symm
    (Euclidean.toL2Grad (μ := _) (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u)) = _
  rw [← scalarBorel_gradientL2]
  exact (scalarBorelLpEquiv FourSpace 2).symm_apply_apply _

theorem twoFormGramPartialL2_smooth (u : SmoothH1TwoForm o) (i : Fin 4) :
    twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i (smoothTwoFormToH1 u) =
      ScalarEuclideanSobolev.partialL2 (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u) i := by
  change scalarGradientCoordinateL2 i
    (twoFormGramGradientL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u)) = _
  rw [twoFormGramGradientL2_smooth, scalarGradientCoordinateL2_smooth]

theorem twoFormGram_complex_derivative (u : TwoFormH1 o) (i : Fin 4) :
    scalarCoordinateDerivative i (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u) : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i u) :
        𝓢'(FourSpace, ℂ)) := by
  have hC : Continuous (fun f : Lp ℝ 2 (volume : Measure FourSpace) =>
      (scalarComplexL2 f : 𝓢'(FourSpace, ℂ))) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp
      (Complex.ofRealCLM.compLpL 2 volume).continuous
  have hL : Continuous (fun w : TwoFormH1 o => scalarCoordinateDerivative i
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v w) :
        𝓢'(FourSpace, ℂ))) :=
    (LineDeriv.continuous_lineDerivOp (EuclideanSpace.basisFun (Fin 4) ℝ i)).comp
      (hC.comp (twoFormGramValueL2 c S hK hKt χ hχ hc hs v).continuous)
  have hR : Continuous (fun w : TwoFormH1 o =>
      (scalarComplexL2 (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i w) :
        𝓢'(FourSpace, ℂ))) :=
    hC.comp (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i).continuous
  refine UniformSpace.Completion.induction_on u (isClosed_eq hL hR) ?_
  intro w
  change scalarCoordinateDerivative i (scalarComplexL2
    (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i (smoothTwoFormToH1 w)) :
        𝓢'(FourSpace, ℂ))
  rw [twoFormGramValueL2_smooth, twoFormGramPartialL2_smooth]
  exact scalarC1_complex_derivative _ i

theorem twoFormGram_memSobolev_one (u : TwoFormH1 o) :
    MemSobolev 1 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u) : 𝓢'(FourSpace, ℂ)) := by
  rw [← zero_add (1 : ℝ)]
  apply (scalar_memSobolev_succ_iff 0 _).mpr
  constructor
  · exact memSobolev_zero_iff.mpr ⟨_, rfl⟩
  · intro i
    rw [twoFormGram_complex_derivative c S hK hKt χ hχ hc hs v u i]
    exact memSobolev_zero_iff.mpr ⟨_, rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local covariant derivatives of intrinsic H1 two-forms as actual
bounded maps into Euclidean L2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (i : Fin 4)

def twoFormGramConnectionL2 : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  ∑ k : Fin 2, ∑ q : Fin 4,
    twoFormGramValueL2 c S hK hKt (twoFormConnectionCutoff (g := g) c S χ i q (v k))
      (twoFormConnectionCutoff_smooth c S hS hKt χ hχ hs i q (v k))
      hc.mul_right (tsupport_mul_subset_left.trans hs) (Function.update v k q)

def twoFormGramCovariantL2 : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i -
    twoFormGramValueL2 c S hK hKt (fun z => partialDeriv χ i z)
      (twoFormCutoffPartial_smooth χ hχ i) (hc.fderiv_apply ℝ (coordinateVector i))
      ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) v -
    twoFormGramConnectionL2 c S hS hK hKt χ hχ hc hs v i

theorem twoFormGramValueL2_coe (u : SmoothH1TwoForm o) :
    twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 u) =ᵐ[volume]
      fun z => χ z * frameTensor (chartGramMatrix g c S z)
        (twoFormCoordinates o (u : smoothTwoForms o).val c z) v := by
  rw [twoFormGramValueL2_smooth]
  exact (ScalarEuclideanSobolev.valueL2_coe _).trans
    (Filter.Eventually.of_forall (twoFormGramCutoffC1_apply c S hKt χ hχ hc hs v u))

theorem twoFormGramConnectionL2_coe (u : SmoothH1TwoForm o) :
    twoFormGramConnectionL2 c S hS hK hKt χ hχ hc hs v i (smoothTwoFormToH1 u) =ᵐ[volume]
      fun z => χ z * tensorSlotAction (chartTwoFormConnection (g := g) c S i z)
        (frameTensor (chartGramMatrix g c S z)
          (twoFormCoordinates o (u : smoothTwoForms o).val c z)) v := by
  let F := fun k q => twoFormGramValueL2 c S hK hKt
    (twoFormConnectionCutoff (g := g) c S χ i q (v k))
    (twoFormConnectionCutoff_smooth c S hS hKt χ hχ hs i q (v k))
    hc.mul_right (tsupport_mul_subset_left.trans hs) (Function.update v k q)
    (smoothTwoFormToH1 u)
  have he (k : Fin 2) (q : Fin 4) := twoFormGramValueL2_coe c S hK hKt
    (twoFormConnectionCutoff (g := g) c S χ i q (v k))
    (twoFormConnectionCutoff_smooth c S hS hKt χ hχ hs i q (v k))
    hc.mul_right (tsupport_mul_subset_left.trans hs) (Function.update v k q) u
  have hinner : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ k : Fin 2,
      (∑ q, F k q) z = ∑ q, F k q z :=
    Filter.eventually_all.mpr (fun k => Lp.coeFn_finsetSum Finset.univ (F k))
  have hall := Filter.eventually_all.mpr (fun k => Filter.eventually_all.mpr (he k))
  have hsumF : twoFormGramConnectionL2 c S hS hK hKt χ hχ hc hs v i (smoothTwoFormToH1 u) =
      ∑ k, ∑ q, F k q := by
    simp only [twoFormGramConnectionL2, F, ContinuousLinearMap.sum_apply]
  rw [hsumF]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => ∑ q, F k q), hinner, hall]
    with z hout hin hz
  rw [hout]
  change (∑ k, (∑ q, F k q) z) = _
  calc
    _ = ∑ k : Fin 2, ∑ q : Fin 4,
        twoFormConnectionCutoff (g := g) c S χ i q (v k) z *
          frameTensor (chartGramMatrix g c S z)
            (twoFormCoordinates o (u : smoothTwoForms o).val c z) (Function.update v k q) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hin k]
      exact Finset.sum_congr rfl (fun q _ => hz k q)
    _ = _ := by
      simp only [twoFormConnectionCutoff, tensorSlotAction, covariantSlotAction,
        Finset.mul_sum, mul_assoc]

theorem twoFormGramCovariantL2_coe (u : SmoothH1TwoForm o) :
    twoFormGramCovariantL2 c S hS hK hKt χ hχ hc hs v i (smoothTwoFormToH1 u) =ᵐ[volume]
      fun z => χ z * frameTensor (chartGramMatrix g c S z)
        (tensorCovariantDirection (connectionMatrix g c)
          (twoFormCoordinates o (u : smoothTwoForms o).val c) i z) v := by
  let D := twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i (smoothTwoFormToH1 u)
  let B := twoFormGramValueL2 c S hK hKt (fun z => partialDeriv χ i z)
    (twoFormCutoffPartial_smooth χ hχ i) (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) v (smoothTwoFormToH1 u)
  let A := twoFormGramConnectionL2 c S hS hK hKt χ hχ hc hs v i (smoothTwoFormToH1 u)
  have hD : D =ᵐ[volume] fun z =>
      partialDeriv (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u).val i z := by
    dsimp [D]
    rw [twoFormGramPartialL2_smooth]
    exact ScalarEuclideanSobolev.partialL2_coe _ i
  have hB := twoFormGramValueL2_coe c S hK hKt (fun z => partialDeriv χ i z)
    (twoFormCutoffPartial_smooth χ hχ i) (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) v u
  have hA := twoFormGramConnectionL2_coe c S hS hK hKt χ hχ hc hs v i u
  change D - B - A =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (D - B) A, Lp.coeFn_sub D B, hD, hB, hA]
    with z hsub hsub' hd hb ha
  rw [hsub, Pi.sub_apply, hsub', Pi.sub_apply, hd, hb, ha]
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · exact (twoFormGramCutoff_covariant c S hS hKt χ hχ hc hs v u i z hz).symm
  · have ht : z ∉ tsupport χ := fun h => hz (hKt (hs h))
    have hv : χ z = 0 := image_eq_zero_of_notMem_tsupport ht
    have hdχ : partialDeriv χ i z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => ht ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h))
    have hdv : partialDeriv (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u).val i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (hKt
        (twoFormGramCutoffC1_support c S hKt χ hχ hc hs v u
          ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h))))
    rw [hv, hdχ, hdv, zero_mul, zero_mul, zero_mul, sub_self, sub_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The difference between localized covariant and ordinary derivatives
is H1: it consists of smooth cutoff and connection coefficients times
localized components of the two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Matrix
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (i : Fin 4) (u : TwoFormH1 o)

def twoFormGramDerivativeCorrection : Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormGramValueL2 c S hK hKt (fun z => partialDeriv χ i z)
    (twoFormCutoffPartial_smooth χ hχ i) (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) v u +
    twoFormGramConnectionL2 c S hS hK hKt χ hχ hc hs v i u

theorem twoFormGramCovariant_add_correction :
    twoFormGramCovariantL2 c S hS hK hKt χ hχ hc hs v i u +
      twoFormGramDerivativeCorrection c S hS hK hKt χ hχ hc hs v i u =
    twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i u := by
  let P := twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i u
  let B := twoFormGramValueL2 c S hK hKt (fun z => partialDeriv χ i z)
    (twoFormCutoffPartial_smooth χ hχ i) (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) v u
  let A := twoFormGramConnectionL2 c S hS hK hKt χ hχ hc hs v i u
  change (P - B - A) + (B + A) = P
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! Six-component Euclidean L2 realizations of the local two-form and
its covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

def twoFormGramVectorL2 :
    TwoFormH1 o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  twoFormAssembleL2 (fun r => twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r))

theorem twoFormGramVectorL2_coe (u : SmoothH1TwoForm o) :
    twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 u) =ᵐ[volume]
      fun z => χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z := by
  apply twoFormAssembleL2_coe
  intro r
  rw [twoFormGramValueL2_smooth]
  filter_upwards [ScalarEuclideanSobolev.valueL2_coe
    (twoFormGramCutoffC1 c S hKt χ hχ hc hs (twoFormComponentIndex r) u)] with z hz
  rw [hz, twoFormGramCutoffC1_value c S hS, twoFormTensor_component]
  rfl

def twoFormGramNablaL2 (i : Fin 4) :
    TwoFormH1 o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  twoFormAssembleL2 (fun r =>
    twoFormGramCovariantL2 c S hS hK hKt χ hχ hc hs (twoFormComponentIndex r) i)

theorem twoFormGramNablaL2_coe (u : SmoothH1TwoForm o)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (i : Fin 4) :
    twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i (smoothTwoFormToH1 u) =ᵐ[volume]
      fun z => χ z • twoFormLocalNabla (g := g) c S
        (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z := by
  apply twoFormAssembleL2_coe
  intro r
  filter_upwards [twoFormGramCovariantL2_coe c S hS hK hKt χ hχ hc hs (twoFormComponentIndex r) i u]
    with z hz
  rw [hz]
  by_cases hzK : z ∈ K
  · rw [(u : smoothTwoForms o).property.localNabla_tensor c S hS U hU hUt hp z (hKU hzK) i,
      twoFormTensor_component]
    rfl
  · have hzero : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hs h))
    rw [hzero, zero_mul, zero_smul]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact chart value map extends from smooth sections to
the intrinsic L2 completion. Its bound uses only the chart volume density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

def smoothTwoFormGramL2Linear :
    SmoothL2TwoForm o →ₗ[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  (twoFormGramVectorL2 c S hK hKt χ hχ hc hs).toLinearMap.comp
    (smoothTwoFormToH1.toLinearMap.comp smoothL2AsH1)

theorem smoothTwoFormGramL2Linear_bound (hS : Sᵀ * S = 1) :
    ∃ C : ℝ, ∀ u : SmoothL2TwoForm o,
      ‖smoothTwoFormGramL2Linear c S hK hKt χ hχ hc hs u‖ ≤ C * ‖u‖ := by
  obtain ⟨D, hD, hDb⟩ := scalarChart_eLpNorm_bound g c hK hKt
  obtain ⟨B, hB⟩ := (hc.isCompact_range hχ.continuous).isBounded.exists_norm_le
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C * D.toReal, fun u => ?_⟩
  let X := smoothTwoFormGramL2Linear c S hK hKt χ hχ hc hs u
  let F := fun x => ‖(u : smoothTwoForms o).val x‖
  let G := fun z => χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z
  have he : X =ᵐ[volume] G :=
    twoFormGramVectorL2_coe c S hS hK hKt χ hχ hc hs (smoothL2AsH1 u)
  have hmem : AEStronglyMeasurable G volume := (Lp.aestronglyMeasurable X).congr he
  have hsupport : Function.support G ⊆ K := by
    intro z hz
    by_contra hzK
    apply hz
    change χ z • _ = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hzK (hs h)), zero_smul]
  have hi : K.indicator G = G := indicator_eq_self.mpr hsupport
  have hlocal : eLpNorm G 2 volume ≤ ENNReal.ofReal C *
      eLpNorm (fun z => F ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) := by
    calc
      _ = eLpNorm G 2 (volume.restrict K) := by
        conv_lhs => rw [← hi]
        exact eLpNorm_indicator_eq_eLpNorm_restrict hK.isClosed.measurableSet
      _ ≤ _ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by
        filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
        change ‖χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z‖ ≤ C * ‖F _‖
        rw [norm_smul, twoFormChartValue_norm o (u : smoothTwoForms o).val c S hS z (hKt hz)]
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact mul_le_mul_of_nonneg_right ((hB (χ z) (mem_range_self z)).trans (le_max_left _ _))
          (norm_nonneg _)) 2
  have hF : eLpNorm F 2 (normalizedVolume g) ≠ (∞ : ℝ≥0∞) := by
    rw [← eLpNorm_congr_ae (twoFormValueNormL2_coe (u : smoothTwoForms o))]
    exact Lp.eLpNorm_ne_top _
  have hb := hlocal.trans (mul_le_mul' le_rfl (hDb F))
  have ht : ENNReal.ofReal C * (D * eLpNorm F 2 (normalizedVolume g)) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hD hF)
  have hr := ENNReal.toReal_mono ht hb
  have hn : (eLpNorm F 2 (normalizedVolume g)).toReal = ‖u‖ := by
    rw [← eLpNorm_congr_ae (twoFormValueNormL2_coe (u : smoothTwoForms o)), ← Lp.norm_def,
      twoFormValueNormL2_eq_L2norm]
  rw [← eLpNorm_congr_ae he, ← Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, hn] at hr
  exact hr.trans_eq (by ring)

def smoothTwoFormGramL2 (hS : Sᵀ * S = 1) :
    SmoothL2TwoForm o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  (smoothTwoFormGramL2Linear c S hK hKt χ hχ hc hs).mkContinuousOfExistsBound
    (smoothTwoFormGramL2Linear_bound c S hK hKt χ hχ hc hs hS)

def twoFormL2GramValue (hS : Sᵀ * S = 1) :
    TwoFormL2 o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  (smoothTwoFormGramL2 c S hK hKt χ hχ hc hs hS).fromCompletion

theorem twoFormL2GramValue_smooth (hS : Sᵀ * S = 1) (u : SmoothL2TwoForm o) :
    twoFormL2GramValue c S hK hKt χ hχ hc hs hS (smoothTwoFormToL2 u) =
      smoothTwoFormGramL2Linear c S hK hKt χ hχ hc hs u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six L2 coordinates of the actual localized two-form inherit the
first-order distributional regularity of the H1 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGramVectorComponent (c : M) (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (u : TwoFormH1 o) (r : Fin 6) :
    twoFormVectorComponentL2 r (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u) =
      twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u :=
  twoFormVectorComponentL2_assemble _ u r

theorem twoFormGramVectorComponent_memSobolev_one (c : M) (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (u : TwoFormH1 o) (r : Fin 6) :
    MemSobolev 1 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)) :
        𝓢'(FourSpace, ℂ)) := by
  rw [twoFormGramVectorComponent]
  exact twoFormGram_memSobolev_one c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrary alternating tensor coordinates are fixed linear combinations
of the six actual two-form components, also after H1 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

theorem twoFormGramValue_tensor_coe (v : Fin 2 → Fin 4) (w : SmoothH1TwoForm o) :
    twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w) =ᵐ[volume] fun z =>
      χ z * twoFormTensor (twoFormChartValue o (w : smoothTwoForms o).val c S hS z) v := by
  rw [twoFormGramValueL2_smooth]
  exact (ScalarEuclideanSobolev.valueL2_coe _).trans (Filter.Eventually.of_forall
    (twoFormGramCutoffC1_value c S hS hKt χ hχ hc hs v w))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finitely many reconstructed coordinate components control each
partition piece in the intrinsic L2 norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormLocalNorm_probability_r171e3e_1 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem twoForm_product_coordinate_bound (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : smoothTwoForms o) (x : M),
      ‖(smoothTwoFormProduct ρ u).val x‖ ≤
        C * ∑ a : Fin 2 → Fin 4, |ρ.val x * twoFormCoordinates o u.val c (chartAt FourSpace c x) a| := by
  obtain ⟨C, hC, hCb⟩ := twoForm_chart_reverse_bound g o c
    (scalarChartSupport_compact c ρ hs) (scalarChartSupport_subset c ρ hs)
  refine ⟨C, hC, fun u x => ?_⟩
  by_cases hx : ρ.val x = 0
  · change ‖ρ.val x • u.val x‖ ≤ _
    simp only [hx, zero_smul, norm_zero, zero_mul, abs_zero, Finset.sum_const_zero, mul_zero, le_refl]
  · have ht := subset_tsupport ρ.val hx
    have hz : chartAt FourSpace c x ∈ scalarChartSupport c ρ := ⟨x, ht, rfl⟩
    have hb := hCb u.val (chartAt FourSpace c x) hz (ρ.val x)
    rw [(chartAt FourSpace c).left_inv (hs ht)] at hb
    change ‖ρ.val x • u.val x‖ ≤ _
    simpa only [norm_smul, Real.norm_eq_abs] using hb

theorem twoForm_product_local_norm (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothH1TwoForm o,
      ‖twoFormValueNormL2 (smoothTwoFormProduct ρ (u : smoothTwoForms o))‖ ≤
        C * ∑ a : Fin 2 → Fin 4,
          ‖twoFormReconstructedValue c ρ hs a (smoothTwoFormToH1 u)‖ := by
  obtain ⟨C, hC, hCb⟩ := twoForm_product_coordinate_bound (o := o) c ρ hs
  refine ⟨C, hC, fun u => ?_⟩
  let R := fun a : Fin 2 → Fin 4 => twoFormReconstructedValue c ρ hs a (smoothTwoFormToH1 u)
  let S : Lp ℝ 2 (normalizedVolume g) := ∑ a : Fin 2 → Fin 4, scalarLpAbs (R a)
  have hall : ∀ᵐ x ∂normalizedVolume g, ∀ a : Fin 2 → Fin 4,
      scalarLpAbs (R a) x = |ρ.val x * twoFormCoordinates o (u : smoothTwoForms o).val c (chartAt FourSpace c x) a| := by
    apply Filter.eventually_all.mpr
    intro a
    filter_upwards [scalarLpAbs_coe (R a), twoFormReconstructedValue_smooth_coe c ρ hs a u] with x ha hr
    exact ha.trans (congrArg abs hr)
  have hdom : ‖twoFormValueNormL2 (smoothTwoFormProduct ρ (u : smoothTwoForms o))‖ ≤ C * ‖S‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hall, Lp.coeFn_finsetSum Finset.univ (fun a => scalarLpAbs (R a)),
      twoFormValueNormL2_coe (smoothTwoFormProduct ρ (u : smoothTwoForms o))] with x hx hsum hval
    change ‖twoFormValueNormL2 (smoothTwoFormProduct ρ (u : smoothTwoForms o)) x‖ ≤ C * ‖S x‖
    have hvalue : ‖twoFormValueNormL2 (smoothTwoFormProduct ρ (u : smoothTwoForms o)) x‖ =
        ‖(smoothTwoFormProduct ρ (u : smoothTwoForms o)).val x‖ := by
      rw [hval, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hS : S x = ∑ a : Fin 2 → Fin 4,
        |ρ.val x * twoFormCoordinates o (u : smoothTwoForms o).val c (chartAt FourSpace c x) a| := by
      exact (show S x = ∑ a : Fin 2 → Fin 4, scalarLpAbs (R a) x from
        by simpa only [Finset.sum_apply] using hsum).trans
          (Finset.sum_congr rfl (fun a _ => hx a))
    calc
      _ = ‖(smoothTwoFormProduct ρ (u : smoothTwoForms o)).val x‖ := hvalue
      _ ≤ C * ∑ a : Fin 2 → Fin 4,
          |ρ.val x * twoFormCoordinates o (u : smoothTwoForms o).val c (chartAt FourSpace c x) a| :=
        hCb (u : smoothTwoForms o) x
      _ = C * ‖S x‖ := by
        rw [Real.norm_eq_abs, hS, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
  apply hdom.trans
  apply mul_le_mul_of_nonneg_left _ hC
  calc
    ‖S‖ ≤ ∑ a : Fin 2 → Fin 4, ‖scalarLpAbs (R a)‖ := norm_sum_le _ _
    _ = _ := by simp only [scalarLpAbs_norm]; rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite family of compact coordinate maps controls the global
two-form L2 value map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormValueNormL2_eq_H1value_norm (u : SmoothH1TwoForm o) :
    ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ =
      ‖twoFormH1ToL2 (smoothTwoFormToH1 u)‖ := by
  rw [twoFormH1ToL2_smooth, smoothTwoFormToL2.norm_map]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := twoFormValueNormL2_norm_sq (u : smoothTwoForms o)
  have hi : ‖smoothH1ToL2 u‖ ^ 2 = smoothTwoFormL2Inner (u : smoothTwoForms o) u := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  exact h.trans hi.symm

theorem twoFormH1_partition_bound (P : ScalarPartition M) :
    ∃ C : P.ι → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ u : TwoFormH1 o,
      ‖twoFormH1ToL2 u‖ ≤ ∑ i : P.ι, C i * ∑ a : Fin 2 → Fin 4,
        ‖twoFormReconstructedValue (P.center i) (scalarPartitionFunction P i)
          (scalarPartitionFunction_support P i) a u‖ := by
  choose C hC hb using (fun i : P.ι => twoForm_product_local_norm (o := o)
    (P.center i) (scalarPartitionFunction P i) (scalarPartitionFunction_support P i))
  refine ⟨C, hC, fun u => ?_⟩
  refine UniformSpace.Completion.induction_on u
    (isClosed_le (continuous_norm.comp twoFormH1ToL2.continuous)
      (continuous_finsetSum _ (fun i _ => continuous_const.mul
        (continuous_finsetSum _ (fun a _ => continuous_norm.comp
          (twoFormReconstructedValue (P.center i) (scalarPartitionFunction P i)
            (scalarPartitionFunction_support P i) a).continuous))))) ?_
  intro v
  change ‖twoFormH1ToL2 (smoothTwoFormToH1 v)‖ ≤ _
  rw [← twoFormValueNormL2_eq_H1value_norm]
  exact (twoFormValueNormL2_partition P (v : smoothTwoForms o)).trans
    (Finset.sum_le_sum (fun i _ => hb i v))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth compact coefficients of the actual localized weak two-form
have L2 distributional derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace} (hK : IsCompact K)
  (hKt : K ⊆ (chartAt FourSpace c).target) (χ : FourSpace → ℝ)
  (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hs : tsupport χ ⊆ K)
  (u : TwoFormH1 o) (b : FourSpace → TwoFormFour) (hb : ContDiff ℝ ∞ b) (hcb : HasCompactSupport b)

theorem twoFormGramCoefficient_memSobolev_one :
    MemSobolev 1 2 (scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hcb
      (twoFormGramVectorL2 c S hK hKt χ hχ hcχ hs u)) : 𝓢'(FourSpace, ℂ)) :=
  twoFormCoefficientPair_memSobolev_one b hb hcb _
    (fun r => twoFormGramVectorComponent_memSobolev_one c S hK hKt χ hχ hcχ hs u r)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Replacing the covariant flux by the ordinary principal flux leaves
an actual H1 correction with L2 divergence. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Matrix
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

def twoFormGramPartialVectorL2 (i : Fin 4) :
    TwoFormH1 o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  twoFormAssembleL2 (fun r => twoFormGramPartialL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) i)

def twoFormGramCorrectionVectorL2 (i : Fin 4) :
    TwoFormH1 o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  twoFormGramPartialVectorL2 c S hK hKt χ hχ hc hs i -
    twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i

theorem twoFormGramCorrectionVector_component (i : Fin 4) (u : TwoFormH1 o) (r : Fin 6) :
    twoFormVectorComponentL2 r (twoFormGramCorrectionVectorL2 c S hS hK hKt χ hχ hc hs i u) =
      twoFormGramDerivativeCorrection c S hS hK hKt χ hχ hc hs (twoFormComponentIndex r) i u := by
  change twoFormVectorComponentL2 r (twoFormGramPartialVectorL2 c S hK hKt χ hχ hc hs i u -
    twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u) = _
  rw [map_sub]
  dsimp only [twoFormGramPartialVectorL2, twoFormGramNablaL2]
  rw [twoFormVectorComponentL2_assemble, twoFormVectorComponentL2_assemble]
  apply sub_eq_iff_eq_add.mpr
  exact (twoFormGramCovariant_add_correction c S hS hK hKt χ hχ hc hs
    (twoFormComponentIndex r) i u).symm.trans (add_comm _ _)

def twoFormPrincipalFlux (b : TwoFormFour) (u : TwoFormH1 o) (j : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  ∑ i : Fin 4, twoFormFluxPair (g := g) c χ hχ hc (hs.trans hKt) b i j
    (twoFormGramPartialVectorL2 c S hK hKt χ hχ hc hs i u)

def twoFormFluxCorrection (b : TwoFormFour) (u : TwoFormH1 o) (j : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  ∑ i : Fin 4, twoFormFluxPair (g := g) c χ hχ hc (hs.trans hKt) b i j
    (twoFormGramCorrectionVectorL2 c S hS hK hKt χ hχ hc hs i u)

theorem twoFormPrincipalFlux_eq (b : TwoFormFour) (u : TwoFormH1 o) (j : Fin 4) :
    twoFormDivergenceFlux (g := g) c χ hχ hc (hs.trans hKt) b
      (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u) j +
      twoFormFluxCorrection c S hS hK hKt χ hχ hc hs b u j =
    twoFormPrincipalFlux c S hK hKt χ hχ hc hs b u j := by
  change (∑ i : Fin 4, _) + (∑ i : Fin 4, _) = ∑ i : Fin 4, _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change _ + twoFormFluxPair (g := g) c χ hχ hc (hs.trans hKt) b i j
    (twoFormGramPartialVectorL2 c S hK hKt χ hχ hc hs i u -
      twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u) = _
  rw [map_sub]
  abel

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Rellich compactness for intrinsic two-forms on a closed manifold.
Finite chart localization reduces the inclusion to the scalar Euclidean
Rellich theorem; the partition estimate controls the intrinsic L2 norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormH1ToL2_compact : IsCompactOperator (twoFormH1ToL2 (o := o)) := by
  obtain ⟨P⟩ := scalarPartition_exists (M := M)
  obtain ⟨C, hC, hb⟩ := twoFormH1_partition_bound (o := o) P
  let J := P.ι × (Fin 2 → Fin 4)
  let R : J → TwoFormH1 o →L[ℝ] Lp ℝ 2 (normalizedVolume g) := fun j =>
    twoFormReconstructedValue (P.center j.1) (scalarPartitionFunction P j.1)
      (scalarPartitionFunction_support P j.1) j.2
  let Q := ContinuousLinearMap.pi R
  have hQ : IsCompactOperator Q := compact_finite_pi R (fun j =>
    twoFormReconstructedValue_compact (P.center j.1) (scalarPartitionFunction P j.1)
      (scalarPartitionFunction_support P j.1) j.2)
  let D : ℝ := (∑ i : P.ι, C i) * Fintype.card (Fin 2 → Fin 4)
  have hD : 0 ≤ D := mul_nonneg (Finset.sum_nonneg (fun i _ => hC i)) (Nat.cast_nonneg _)
  apply compact_of_norm_domination twoFormH1ToL2 Q hQ D hD
  intro u
  apply (hb u).trans
  calc
    _ ≤ ∑ i : P.ι, C i * ((Fintype.card (Fin 2 → Fin 4) : ℝ) * ‖Q u‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hC i)
      calc
        _ ≤ ∑ a : Fin 2 → Fin 4, ‖Q u‖ := by
          apply Finset.sum_le_sum
          intro a _
          exact norm_le_pi_norm (Q u) (i, a)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = D * ‖Q u‖ := by rw [← Finset.sum_mul]; dsimp [D]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact weak solution operator for one plus the rough two-form
Laplacian, defined by the actual H1 and L2 pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormH1ToL2_dense : DenseRange (twoFormH1ToL2 (o := o)) := by
  refine Dense.mono ?_ (smoothTwoFormToL2_dense (o := o))
  rintro _ ⟨u, rfl⟩
  refine ⟨smoothTwoFormToH1 (show SmoothH1TwoForm o from u), ?_⟩
  exact twoFormH1ToL2_smooth _

theorem twoFormRoughSolution_weak (f : TwoFormL2 o) (v : TwoFormH1 o) :
    inner ℝ (twoFormRoughSolution f) v = inner ℝ f (twoFormH1ToL2 v) :=
  ContinuousLinearMap.adjoint_inner_left twoFormH1ToL2 v f

theorem twoFormRoughSolution_unique (f : TwoFormL2 o) (u : TwoFormH1 o)
    (hu : ∀ v, inner ℝ u v = inner ℝ f (twoFormH1ToL2 v)) :
    u = twoFormRoughSolution f := by
  apply ext_inner_right ℝ
  intro v
  exact (hu v).trans (twoFormRoughSolution_weak f v).symm

theorem twoFormRoughSolution_injective : Function.Injective (twoFormRoughSolution (o := o)) := by
  suffices hz : ∀ f : TwoFormL2 o, twoFormRoughSolution f = 0 → f = 0 by
    intro f h he
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, he, sub_self]
  intro f hf
  have hall : ∀ v : TwoFormH1 o, inner ℝ f (twoFormH1ToL2 v) = 0 := by
    intro v
    rw [← twoFormRoughSolution_weak, hf, inner_zero_left]
  have heq : (fun x : TwoFormL2 o => inner ℝ f x) = fun _ => 0 :=
    twoFormH1ToL2_dense.equalizer (continuous_const.inner continuous_id)
      continuous_const (funext hall)
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (congrFun heq f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The lifted tensor's pairing is the intrinsic normal-frame pairing
at the base point. No choice of reference-frame regularity is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalLift_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (v : M → TwoFormFour) (f : FrameBundle g) :
    inner ℝ (WithLp.toLp 2
      (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) : TwoTensorEuclidean)
      (WithLp.toLp 2 (twoFormFramedValue o v f)) =
    2 * heatNormalScalarLift C
      (fun x => inner ℝ (a x) (heatNormalTwoFormValue o c D.point v x)) f.base := by
  classical
  rw [heat_euclideanTensor_inner]
  by_cases hf : f.base ∈ C.target
  · let x := C.symm f.base
    have hx : x ∈ C.source := C.map_target hf
    have hxb := hD hx
    have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
      rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
    have hF := frameChartMatrix_normalizes g c f (hCt hf)
    rw [← hbase] at hF
    rw [heatNormalFrameTensorLift, ite_eq_left hf, heatNormalScalarLift_on_target C _ hf,
      heatNormalCoordinateTensor, heat_framedValue_chart o v c f (hCt hf)]
    change frameTensorPairing
      (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))))
      (frameTensor (frameChartMatrix g c f) (twoFormCoordinates o v c (chartAt FourSpace c f.base))) = _
    rw [← hbase, heat_normal_frame_pairing _ _ _ (D.orthonormal x hxb) hF,
      ← heatNormalTwoFormValue_tensor, twoFormTensor_pairing]
  · rw [heatNormalFrameTensorLift, ite_eq_right hf, heatNormalScalarLift]
    rw [ite_eq_right hf]
    simp only [frameTensorPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global L2 amplitude has the expected scalar base integral against
every actual smooth test section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.heatNormalAmplitudePairing_probability
theorem heatNormalAmplitudeL2_pairing_base (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : SmoothL2TwoForm o) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothTwoFormToL2 v) =
      ∫ y, heatNormalScalarLift C
        (fun x => inner ℝ (a x) (heatNormalTwoFormValue o c D.point
          (v : smoothTwoForms o).val x)) y ∂normalizedVolume g := by
  let ψ := fun x => inner ℝ (a x) (heatNormalTwoFormValue o c D.point
    (v : smoothTwoForms o).val x)
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have ha0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    simp only [ψ, ha0, inner_zero_left]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := by
    intro x hx
    have hv := heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))
    exact (ha.continuous.continuousAt.inner hv.continuousAt).continuousWithinAt
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [heatNormalAmplitudeL2_pairing]
  have hp (f : FrameBundle g) :
      inner ℝ (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f)
        (smoothTwoFormEuclideanValue (v : smoothTwoForms o) f) =
      2 * heatNormalScalarLift C ψ f.base :=
    heatNormalLift_pairing D C hE hCt hD a (v : smoothTwoForms o).val f
  simp_rw [hp]
  rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairings of the actual global L2 amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalAmplitudeL2_pairing_normal (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : SmoothL2TwoForm o) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothTwoFormToL2 v) =
      (normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalTwoFormValue o c D.point
          (v : smoothTwoForms o).val x) := by
  rw [heatNormalAmplitudeL2_pairing_base D C hE]
  apply heatNormalScalarLift_integral D C hE hCt hP hD
  apply subset_trans (closure_mono ?_) hs
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx, inner_zero_left]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The closed nonnegative Hodge form on the actual H1 completion. Its
zero-energy space is the finite weak harmonic kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHodgeForm (u v : TwoFormH1 o) : ℝ :=
  inner ℝ u v - inner ℝ (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) (twoFormH1ToL2 v)

theorem twoFormWeitzenbockPotential_symmetric (u v : TwoFormL2 o) :
    inner ℝ (twoFormWeitzenbockPotential u) v =
      inner ℝ (twoFormWeitzenbockPotential v) u := by
  simp only [twoFormWeitzenbockPotential, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    real_inner_smul_left]
  rw [twoFormL2Curvature_selfAdjoint, real_inner_comm u (twoFormL2Curvature v),
    real_inner_comm u v]

theorem twoFormHodgeForm_comm (u v : TwoFormH1 o) :
    twoFormHodgeForm u v = twoFormHodgeForm v u := by
  unfold twoFormHodgeForm
  rw [twoFormWeitzenbockPotential_symmetric, real_inner_comm u v]

theorem twoFormHodgeForm_smul_left (r : ℝ) (u v : TwoFormH1 o) :
    twoFormHodgeForm (r • u) v = r * twoFormHodgeForm u v := by
  simp only [twoFormHodgeForm, map_smul, real_inner_smul_left]
  ring

theorem twoFormHodgeForm_smooth (hRic : RicciThree g) (u : SmoothH1TwoForm o) :
    twoFormHodgeForm (smoothTwoFormToH1 u) (smoothTwoFormToH1 u) =
      smoothTwoFormDeRhamEnergy (u : smoothTwoForms o) := by
  unfold twoFormHodgeForm
  rw [twoFormH1ToL2_smooth, smoothTwoFormToH1.inner_map_map]
  simp only [twoFormWeitzenbockPotential, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_sub_left,
    real_inner_smul_left]
  rw [twoFormL2Curvature_smooth, smoothTwoFormToL2.inner_map_map,
    smoothTwoFormToL2.inner_map_map]
  have hw := smoothTwoForm_Weitzenbock hRic (u : smoothTwoForms o)
  change (smoothTwoFormL2Inner (u : smoothTwoForms o) (u : smoothTwoForms o) +
      smoothTwoFormCovariantEnergy (u : smoothTwoForms o) (u : smoothTwoForms o)) -
    (2 * smoothTwoFormL2Inner (smoothTwoFormCurvature (u : smoothTwoForms o)) (u : smoothTwoForms o) -
      5 * smoothTwoFormL2Inner (u : smoothTwoForms o) (u : smoothTwoForms o)) =
    smoothTwoFormDeRhamEnergy (u : smoothTwoForms o)
  linarith only [hw]

theorem twoFormHodgeForm_nonneg (hRic : RicciThree g) (u : TwoFormH1 o) :
    0 ≤ twoFormHodgeForm u u := by
  have hc : Continuous (fun v : TwoFormH1 o => twoFormHodgeForm v v) :=
    (continuous_id.inner continuous_id).sub
      ((twoFormWeitzenbockPotential.continuous.comp twoFormH1ToL2.continuous).inner
        twoFormH1ToL2.continuous)
  refine UniformSpace.Completion.induction_on u (isClosed_le continuous_const hc) ?_
  intro v
  change 0 ≤ twoFormHodgeForm (smoothTwoFormToH1 v) (smoothTwoFormToH1 v)
  rw [twoFormHodgeForm_smooth hRic]
  exact smoothTwoFormDeRhamEnergy_nonneg _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Hodge operator becomes invertible after adding its
finite harmonic projection. This is the needed Fredholm step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeCompact_compact : IsCompactOperator (twoFormHodgeCompact (o := o)) :=
  (twoFormH1ToL2_compact.clm_comp twoFormWeitzenbockPotential).clm_comp twoFormRoughSolution

def twoFormHodgeOperator : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  ContinuousLinearMap.id ℝ (TwoFormH1 o) - twoFormHodgeCompact

theorem twoFormHodgeOperator_inner (u v : TwoFormH1 o) :
    inner ℝ (twoFormHodgeOperator u) v = twoFormHodgeForm u v := by
  change inner ℝ (u - twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) v = _
  rw [inner_sub_left, twoFormRoughSolution_weak]
  rfl

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual smooth Hodge Laplacian in the normalization Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeForm_smooth_pairing (u v : SmoothH1TwoForm o) :
    twoFormHodgeForm (smoothTwoFormToH1 u) (smoothTwoFormToH1 v) =
      smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v +
        6 * smoothTwoFormL2Inner (u : smoothTwoForms o) v -
        2 * smoothTwoFormL2Inner (smoothTwoFormCurvature (u : smoothTwoForms o)) v := by
  unfold twoFormHodgeForm
  rw [twoFormH1ToL2_smooth, twoFormH1ToL2_smooth, smoothTwoFormToH1.inner_map_map]
  simp only [twoFormWeitzenbockPotential, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left]
  rw [twoFormL2Curvature_smooth, smoothTwoFormToL2.inner_map_map,
    smoothTwoFormToL2.inner_map_map]
  change (smoothTwoFormL2Inner (u : smoothTwoForms o) v +
      smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v) -
      (2 * smoothTwoFormL2Inner (smoothTwoFormCurvature (u : smoothTwoForms o)) v -
        5 * smoothTwoFormL2Inner (u : smoothTwoForms o) v) = _
  ring

theorem smoothHodgeLaplacian_pairing (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v =
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o))
        (smoothTwoFormToH1 (v : SmoothH1TwoForm o)) := by
  apply Eq.trans ?_ (twoFormHodgeForm_smooth_pairing
    (u : SmoothH1TwoForm o) (v : SmoothH1TwoForm o)).symm
  rw [smoothHodgeLaplacian, smoothTwoFormL2Inner_sub, smoothTwoFormL2Inner_sub,
    smoothTwoFormL2Inner_smul, smoothTwoFormL2Inner_smul,
    smoothTwoForm_roughTrace_green_left hRic]
  ring

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

/-! The actual compact resolvent of one plus the two-form Hodge
Laplacian, constructed from the proved nonnegative weak Hodge form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedHodgeCompact_compact : IsCompactOperator (twoFormShiftedHodgeCompact (o := o)) :=
  twoFormHodgeCompact_compact.sub (twoFormH1ToL2_compact.clm_comp twoFormRoughSolution)

theorem twoFormShiftedHodge_inner (u v : TwoFormH1 o) :
    inner ℝ (twoFormShiftedHodge u) v =
      twoFormHodgeForm u v + inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v) := by
  change inner ℝ (u - (twoFormHodgeCompact u - twoFormRoughSolution (twoFormH1ToL2 u))) v = _
  rw [inner_sub_left, inner_sub_left, twoFormRoughSolution_weak]
  have he := twoFormHodgeOperator_inner u v
  change inner ℝ (u - twoFormHodgeCompact u) v = _ at he
  rw [inner_sub_left] at he
  linarith only [he]

theorem twoFormShiftedHodge_eq_zero (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : twoFormShiftedHodge u = 0) : u = 0 := by
  have h := congrArg (fun v : TwoFormH1 o => inner ℝ v u) hu
  rw [twoFormShiftedHodge_inner, inner_zero_left] at h
  have hQ := twoFormHodgeForm_nonneg hRic u
  have hn := real_inner_self_nonneg (x := twoFormH1ToL2 u)
  have hz : inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 u) = 0 := by linarith only [h, hQ, hn]
  exact twoFormH1_eq_zero_of_value_eq_zero hRic u (inner_self_eq_zero.mp hz)

theorem twoFormShiftedHodge_injective (hRic : RicciThree g) :
    Function.Injective (twoFormShiftedHodge (o := o)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply twoFormShiftedHodge_eq_zero hRic
  rw [map_sub, huv, sub_self]

theorem twoFormShiftedHodge_surjective (hRic : RicciThree g) :
    Function.Surjective (twoFormShiftedHodge (o := o)) := by
  rcases (twoFormShiftedHodgeCompact_compact (o := o)).hasEigenvalue_or_mem_resolventSet
      (one_ne_zero : (1 : ℝ) ≠ 0) with hv | hr
  · obtain ⟨u, hu⟩ := hv.exists_hasEigenvector
    have he := Module.End.mem_eigenspace_iff.mp hu.1
    change twoFormShiftedHodgeCompact u = (1 : ℝ) • u at he
    rw [one_smul] at he
    have hz : twoFormShiftedHodge u = 0 := by
      change u - twoFormShiftedHodgeCompact u = 0
      rw [he, sub_self]
    exact (hu.2 (twoFormShiftedHodge_eq_zero hRic u hz)).elim
  · have hi := spectrum.mem_resolventSet_iff.mp hr
    simp only [map_one] at hi
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hi).2

def twoFormShiftedHodgeEquiv (hRic : RicciThree g) : TwoFormH1 o ≃L[ℝ] TwoFormH1 o :=
  ContinuousLinearEquiv.ofBijective twoFormShiftedHodge
    (LinearMap.ker_eq_bot.mpr (twoFormShiftedHodge_injective hRic))
    (LinearMap.range_eq_top.mpr (twoFormShiftedHodge_surjective hRic))

def twoFormShiftedSolution (hRic : RicciThree g) : TwoFormL2 o →L[ℝ] TwoFormH1 o :=
  (twoFormShiftedHodgeEquiv hRic).symm.toContinuousLinearMap.comp twoFormRoughSolution

theorem twoFormShiftedSolution_equation (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedHodge (twoFormShiftedSolution hRic f) = twoFormRoughSolution f :=
  (twoFormShiftedHodgeEquiv hRic).apply_symm_apply _

theorem twoFormShiftedSolution_weak (hRic : RicciThree g) (f : TwoFormL2 o) (v : TwoFormH1 o) :
    twoFormHodgeForm (twoFormShiftedSolution hRic f) v +
      inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) (twoFormH1ToL2 v) =
        inner ℝ f (twoFormH1ToL2 v) := by
  rw [← twoFormShiftedHodge_inner, twoFormShiftedSolution_equation, twoFormRoughSolution_weak]

def twoFormShiftedResolvent (hRic : RicciThree g) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormH1ToL2.comp (twoFormShiftedSolution hRic)

theorem twoFormShiftedResolvent_compact (hRic : RicciThree g) :
    IsCompactOperator (twoFormShiftedResolvent (o := o) hRic) :=
  twoFormH1ToL2_compact.comp_clm (twoFormShiftedSolution hRic)

theorem twoFormShiftedResolvent_selfAdjoint (hRic : RicciThree g) (f h : TwoFormL2 o) :
    inner ℝ (twoFormShiftedResolvent hRic f) h =
      inner ℝ f (twoFormShiftedResolvent hRic h) := by
  have hf := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic h)
  have hh := twoFormShiftedSolution_weak hRic h (twoFormShiftedSolution hRic f)
  change inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) h = _
  calc
    _ = inner ℝ h (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) := real_inner_comm _ _
    _ = twoFormHodgeForm (twoFormShiftedSolution hRic h) (twoFormShiftedSolution hRic f) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic h))
          (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) := hh.symm
    _ = twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic h) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f))
          (twoFormH1ToL2 (twoFormShiftedSolution hRic h)) := by
      rw [twoFormHodgeForm_comm, real_inner_comm]
    _ = _ := hf

theorem twoFormShiftedResolvent_injective (hRic : RicciThree g) :
    Function.Injective (twoFormShiftedResolvent (o := o) hRic) := by
  intro f h he
  have hu := twoFormH1ToL2_injective hRic he
  have hv := congrArg (twoFormShiftedHodge (o := o)) hu
  exact twoFormRoughSolution_injective ((twoFormShiftedSolution_equation hRic f).symm.trans
    (hv.trans (twoFormShiftedSolution_equation hRic h)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Spectral bounds and the actual weak Hodge equation for eigenvectors
of the shifted resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedResolvent_norm_le (hRic : RicciThree g) (f : TwoFormL2 o) :
    ‖twoFormShiftedResolvent hRic f‖ ≤ ‖f‖ := by
  have he := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  have hQ := twoFormHodgeForm_nonneg hRic (twoFormShiftedSolution hRic f)
  rw [real_inner_self_eq_norm_sq] at he
  have hC := real_inner_le_norm f (twoFormShiftedResolvent hRic f)
  change ‖twoFormH1ToL2 (twoFormShiftedSolution hRic f)‖ ≤ ‖f‖
  change inner ℝ f (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) ≤
    ‖f‖ * ‖twoFormH1ToL2 (twoFormShiftedSolution hRic f)‖ at hC
  nlinarith only [he, hQ, hC, norm_nonneg f,
    norm_nonneg (twoFormH1ToL2 (twoFormShiftedSolution hRic f))]

theorem twoFormShiftedResolvent_pos (hRic : RicciThree g) (f : TwoFormL2 o) (hf : f ≠ 0) :
    0 < inner ℝ (twoFormShiftedResolvent hRic f) f := by
  have hn : twoFormShiftedResolvent hRic f ≠ 0 := by
    intro h
    exact hf (twoFormShiftedResolvent_injective hRic (h.trans (map_zero _).symm))
  have he := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  have hQ := twoFormHodgeForm_nonneg hRic (twoFormShiftedSolution hRic f)
  have hp : 0 < inner ℝ (twoFormShiftedResolvent hRic f) (twoFormShiftedResolvent hRic f) :=
    by simpa only [real_inner_self_eq_norm_sq, sq_pos_iff, norm_ne_zero_iff] using hn
  have hc := real_inner_comm f (twoFormShiftedResolvent hRic f)
  change twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic f) +
    inner ℝ (twoFormShiftedResolvent hRic f) (twoFormShiftedResolvent hRic f) =
      inner ℝ f (twoFormShiftedResolvent hRic f) at he
  linarith only [he, hQ, hp, hc]

theorem twoFormShiftedResolvent_eigenvalue (hRic : RicciThree g) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ) :
    0 < μ ∧ μ ≤ 1 := by
  obtain ⟨f, hf⟩ := hμ.exists_hasEigenvector
  have he := Module.End.mem_eigenspace_iff.mp hf.1
  change twoFormShiftedResolvent hRic f = μ • f at he
  have hp := twoFormShiftedResolvent_pos hRic f hf.2
  rw [he, real_inner_smul_left] at hp
  have hμpos : 0 < μ := by nlinarith only [hp, real_inner_self_nonneg (x := f)]
  have hn := twoFormShiftedResolvent_norm_le hRic f
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos] at hn
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf.2
  exact ⟨hμpos, by nlinarith only [hn, hfpos]⟩

theorem twoFormResolvent_eigenvector_weak (hRic : RicciThree g) {μ : ℝ} {f : TwoFormL2 o}
    (hf : Module.End.HasEigenvector (twoFormShiftedResolvent hRic).toLinearMap μ f) :
    ∃ u : TwoFormH1 o, twoFormH1ToL2 u = f ∧
      ∀ v : TwoFormH1 o, twoFormHodgeForm u v =
        (μ⁻¹ - 1) * inner ℝ f (twoFormH1ToL2 v) := by
  have hm : μ ≠ 0 := ne_of_gt
    (twoFormShiftedResolvent_eigenvalue hRic (Module.End.hasEigenvalue_of_hasEigenvector hf)).1
  have he := Module.End.mem_eigenspace_iff.mp hf.1
  change twoFormShiftedResolvent hRic f = μ • f at he
  let u := μ⁻¹ • twoFormShiftedSolution hRic f
  have hu : twoFormH1ToL2 u = f := by
    change twoFormH1ToL2 (μ⁻¹ • twoFormShiftedSolution hRic f) = f
    rw [map_smul]
    change μ⁻¹ • twoFormShiftedResolvent hRic f = f
    rw [he, smul_smul, inv_mul_cancel₀ hm, one_smul]
  refine ⟨u, hu, fun v => ?_⟩
  have hw := twoFormShiftedSolution_weak hRic f v
  change twoFormHodgeForm (twoFormShiftedSolution hRic f) v +
    inner ℝ (twoFormShiftedResolvent hRic f) (twoFormH1ToL2 v) = _ at hw
  rw [he, real_inner_smul_left] at hw
  change twoFormHodgeForm (μ⁻¹ • twoFormShiftedSolution hRic f) v = _
  rw [twoFormHodgeForm_smul_left]
  calc
    _ = μ⁻¹ * ((1 - μ) * inner ℝ f (twoFormH1ToL2 v)) := by
      congr 1
      linarith only [hw]
    _ = _ := by field_simp [hm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local weak rough equation: the H1 pairing against a
compact chart test equals the Euclidean L2 mass and covariant pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)

include hon

theorem twoFormGramVectorL2_mass (u : SmoothH1TwoForm o) :
    inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 u))
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        inner ℝ (twoFormChartValue o (u : smoothTwoForms o).val c S hS z) (a z) := by
  rw [L2.inner_def]
  have he : (fun z => inner ℝ
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 u) z)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt) z)) =ᵐ[volume]
      fun z => inner ℝ (χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z)
        (twoFormMassTest (g := g) c a z) := by
    filter_upwards [twoFormGramVectorL2_coe c S hS hK hKt χ hχ hc hs u,
      twoFormMassTestL2_coe (g := g) c a ha
        (hK.of_isClosed_subset (isClosed_tsupport a) has) (has.trans hKt)] with z hv hb
    rw [hv, hb]
  rw [integral_congr_ae he]
  have hm : (fun z => inner ℝ (χ z • twoFormChartValue o (u : smoothTwoForms o).val c S hS z)
      (twoFormMassTest (g := g) c a z)) =
      fun z => chartVolumeDensity g c z *
        inner ℝ (twoFormChartValue o (u : smoothTwoForms o).val c S hS z) (a z) :=
    funext (mass_pairing c χ a hon _)
  rw [hm]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hez := image_eq_zero_of_notMem_tsupport (fun h => hz (hKt (has h)))
  rw [hez, inner_zero_right, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form L2 space is the Hilbert sum of the finite
eigenspaces of its compact shifted Hodge resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedResolvent_symmetric (hRic : RicciThree g) :
    (twoFormShiftedResolvent (o := o) hRic).IsSymmetric :=
  twoFormShiftedResolvent_selfAdjoint hRic

abbrev TwoFormSpectralValue (hRic : RicciThree g) :=
  Module.End.Eigenvalues (twoFormShiftedResolvent (o := o) hRic).toLinearMap

abbrev TwoFormSpectralSpace (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :=
  Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ.val

theorem twoFormSpectralValue_bounds (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : 0 < μ.val ∧ μ.val ≤ 1 :=
  twoFormShiftedResolvent_eigenvalue hRic μ.property

instance twoFormSpectralSpaceFinite (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    FiniteDimensional ℝ (TwoFormSpectralSpace hRic μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (twoFormShiftedResolvent_compact hRic) μ.val
    (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1)

theorem twoFormSpectral_orthogonal_bot (hRic : RicciThree g) :
    (⨆ μ : TwoFormSpectralValue (o := o) hRic, TwoFormSpectralSpace hRic μ)ᗮ = ⊥ := by
  change (⨆ μ : {μ // Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ ≠ ⊥},
    Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ.val)ᗮ = ⊥
  rw [iSup_ne_bot_subtype]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (twoFormShiftedResolvent_compact hRic) (twoFormShiftedResolvent_symmetric hRic)

theorem twoFormSpectral_total (hRic : RicciThree g) :
    (⨆ μ : TwoFormSpectralValue (o := o) hRic,
      TwoFormSpectralSpace hRic μ).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, twoFormSpectral_orthogonal_bot hRic]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic weak rough equation in actual local orthonormal-frame
coefficients. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

def twoFormLocalTestH1 : SmoothH1TwoForm o := twoFormGramTest o c S a ha hK hKt has

def twoFormLocalPairing (u : TwoFormH1 o) : ℝ :=
  (normalizedChartFactor g).toReal *
    (inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) +
    ∑ i : Fin 4, inner ℝ (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u)
      (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt) i))

theorem twoFormLocalPairing_continuous :
    Continuous (twoFormLocalPairing (o := o) c S hS hK hKt χ hχ hc hs a ha has) :=
  continuous_const.mul
    (((twoFormGramVectorL2 c S hK hKt χ hχ hc hs).continuous.inner continuous_const).add
      (continuous_finsetSum _ (fun i _ =>
        (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i).continuous.inner continuous_const)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local weak two-form equation with actual L2 coefficients on
both sides, including the localized forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

theorem twoFormL2GramValue_H1 (u : TwoFormH1 o) :
    twoFormL2GramValue c S hK hKt χ hχ hc hs hS (twoFormH1ToL2 u) =
      twoFormGramVectorL2 c S hK hKt χ hχ hc hs u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((twoFormL2GramValue c S hK hKt χ hχ hc hs hS).continuous.comp
      twoFormH1ToL2.continuous) (twoFormGramVectorL2 c S hK hKt χ hχ hc hs).continuous) ?_
  intro v
  change twoFormL2GramValue c S hK hKt χ hχ hc hs hS (twoFormH1ToL2 (smoothTwoFormToH1 v)) =
    twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 v)
  rw [twoFormH1ToL2_smooth, twoFormL2GramValue_smooth]
  rfl

variable (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)

include hon in
theorem twoFormL2_localTest (f : TwoFormL2 o) :
    inner ℝ f (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) =
      (normalizedChartFactor g).toReal * inner ℝ
        (twoFormL2GramValue c S hK hKt χ hχ hc hs hS f)
        (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt)) := by
  refine UniformSpace.Completion.induction_on f
    (isClosed_eq (continuous_id.inner continuous_const)
      (continuous_const.mul ((twoFormL2GramValue c S hK hKt χ hχ hc hs hS).continuous.inner
        continuous_const))) ?_
  intro v
  change inner ℝ (smoothTwoFormToL2 v)
    (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) =
      (normalizedChartFactor g).toReal * inner ℝ
        (twoFormL2GramValue c S hK hKt χ hχ hc hs hS (smoothTwoFormToL2 v))
        (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt))
  rw [smoothTwoFormToL2.inner_map_map, twoFormL2GramValue_smooth]
  change smoothTwoFormL2Inner (v : smoothTwoForms o) (twoFormGramTest o c S a ha hK hKt has) =
    (normalizedChartFactor g).toReal * inner ℝ
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 (smoothL2AsH1 v))) _
  rw [smoothTwoFormL2Inner_gramTest (v : smoothTwoForms o) c S hS a ha hK hKt has,
    twoFormGramVectorL2_mass c S hS hK hKt χ hχ hc hs a ha has hon (smoothL2AsH1 v)]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The completed Weitzenböck potential has the actual smooth chart
coefficients. In particular its compact chart coordinates are H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormWeitzenbockPotential_smooth (w : SmoothL2TwoForm o) :
    twoFormWeitzenbockPotential (smoothTwoFormToL2 w) =
      smoothTwoFormToL2 ((2 : ℝ) • smoothL2Curvature w - (5 : ℝ) • w) := by
  change (2 : ℝ) • twoFormL2Curvature (smoothTwoFormToL2 w) -
    (5 : ℝ) • smoothTwoFormToL2 w = _
  rw [twoFormL2Curvature_smooth, map_sub, map_smul, map_smul]

theorem twoFormChartValue_potential (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (w : SmoothL2TwoForm o) (z : FourSpace) :
    twoFormChartValue o
      (((2 : ℝ) • smoothL2Curvature w - (5 : ℝ) • w : SmoothL2TwoForm o) :
        smoothTwoForms o).val c S hS z =
      twoFormChartPotential (g := g) c S z
        (twoFormChartValue o (w : smoothTwoForms o).val c S hS z) := by
  change twoFormChartValue o
    ((2 : ℝ) • twoFormCurvatureField o (w : smoothTwoForms o).val -
      (5 : ℝ) • (w : smoothTwoForms o).val) c S hS z = _
  have hcurv : twoFormChartValue o (twoFormCurvatureField o (w : smoothTwoForms o).val)
      c S hS z = twoFormCurvatureOperator
        (frameTensor (chartGramMatrix g c S z) (curvatureCoordinates g c z))
        (twoFormChartValue o (w : smoothTwoForms o).val c S hS z) := by
    by_cases hz : z ∈ (chartAt FourSpace c).target
    · simp only [twoFormChartValue, dite_eq_left hz]
      rw [twoFormCurvatureField_frame, twoFormMetricCurvatureTensor_chart]
      rfl
    · simp only [twoFormChartValue, dite_eq_right hz, map_zero]
  rw [sub_eq_add_neg, ← neg_smul]
  rw [twoFormChartValue_add, twoFormChartValue_smul, twoFormChartValue_smul]
  simp only [Pi.add_apply, Pi.smul_apply, hcurv]
  let a := twoFormChartValue o (w : smoothTwoForms o).val c S hS z
  let R := twoFormCurvatureOperator
    (frameTensor (chartGramMatrix g c S z) (curvatureCoordinates g c z))
  change (2 : ℝ) • R a + (-5 : ℝ) • a = (2 : ℝ) • R a - (5 : ℝ) • a
  rw [neg_smul, sub_eq_add_neg]

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηK : tsupport η ⊆ K) (hon : ∀ z ∈ tsupport η, χ z = 1)

include hon in
theorem twoFormPotential_chart_pair (u : TwoFormH1 o) (r : Fin 6) :
    twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) =
      twoFormCoefficientPairL2 (twoFormPotentialCoefficient (g := g) c S η r)
        (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
        (twoFormPotentialCoefficient_compact c S η hcη r)
        (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq
      ((twoFormVectorComponentL2 r).continuous.comp
        ((twoFormL2GramValue c S hK hKt η hη hcη hηK hS).continuous.comp
          (twoFormWeitzenbockPotential.continuous.comp twoFormH1ToL2.continuous)))
      ((twoFormCoefficientPairL2 _ _ _).continuous.comp
        (twoFormGramVectorL2 c S hK hKt χ hχ hc hs).continuous)) ?_
  intro w
  change twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 (smoothTwoFormToH1 w)))) =
    twoFormCoefficientPairL2 (twoFormPotentialCoefficient (g := g) c S η r)
      (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
      (twoFormPotentialCoefficient_compact c S η hcη r)
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w))
  rw [twoFormH1ToL2_smooth, twoFormWeitzenbockPotential_smooth, twoFormL2GramValue_smooth]
  apply Lp.ext
  have hl := twoFormGramVectorL2_coe c S hS hK hKt η hη hcη hηK
    (smoothL2AsH1 ((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w))
  have hr := twoFormGramVectorL2_coe c S hS hK hKt χ hχ hc hs w
  filter_upwards [twoFormVectorComponentL2_coe r
      (smoothTwoFormGramL2Linear c S hK hKt η hη hcη hηK
        ((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w)),
    hl, twoFormCoefficientPair_coe (twoFormPotentialCoefficient (g := g) c S η r)
      (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
      (twoFormPotentialCoefficient_compact c S η hcη r)
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w)), hr]
      with z hz hlz hp hrz
  rw [hz]
  change (twoFormGramVectorL2 c S hK hKt η hη hcη hηK
    (smoothTwoFormToH1 (smoothL2AsH1
      ((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w)))) z r = _
  rw [hlz]
  change η z * twoFormChartValue o
    (((2 : ℝ) • smoothL2Curvature (smoothH1ToL2 w) - (5 : ℝ) • smoothH1ToL2 w :
      SmoothL2TwoForm o) : smoothTwoForms o).val c S hS z r = _
  have hp' : (twoFormCoefficientPairL2 (twoFormPotentialCoefficient (g := g) c S η r)
      (twoFormPotentialCoefficient_smooth c S η hη (hηK.trans hKt) r).continuous
      (twoFormPotentialCoefficient_compact c S η hcη r)
      (twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w))) z =
    inner ℝ ((twoFormGramVectorL2 c S hK hKt χ hχ hc hs (smoothTwoFormToH1 w)) z)
      (twoFormPotentialCoefficient (g := g) c S η r z) := hp
  rw [hp', hrz, twoFormChartValue_potential]
  rw [inner_smul_left, twoFormPotentialCoefficient_pair]
  change η z * _ = χ z * (η z * _)
  by_cases he : η z = 0
  · simp only [he, zero_mul, mul_zero]
  · rw [hon z (subset_tsupport η he), one_mul]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary derivative of each localized coefficient, tested against
actual smooth compact scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGram_weak_partial (c : M) (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (i : Fin 4)
    (u : TwoFormH1 o) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z) (twoFormCutoffPartial_smooth ψ hψ i)
        (hcψ.fderiv_apply ℝ (coordinateVector i))) =
      -inner ℝ (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i u)
        (twoFormScalarTestL2 ψ hψ hcψ) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((twoFormGramValueL2 c S hK hKt χ hχ hc hs v).continuous.inner continuous_const)
      ((twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i).continuous.inner continuous_const).neg) ?_
  intro w
  change inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) _ =
    -inner ℝ (twoFormGramPartialL2 c S hK hKt χ hχ hc hs v i (smoothTwoFormToH1 w)) _
  rw [twoFormGramValueL2_smooth, twoFormGramPartialL2_smooth]
  exact scalarC1_compact_test _ ψ hψ hcψ i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integer-order control of the actual localized connection corrections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (v : Fin 2 → Fin 4) (i : Fin 4)

include hreg in
theorem twoFormGramConnection_memSobolev_integer :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramConnectionL2 c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  change MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ k : Fin 2, ∑ q : Fin 4,
    twoFormGramValueL2 c S hK hKt (twoFormConnectionCutoff (g := g) c S η i q (v k))
      (twoFormConnectionCutoff_smooth c S hS hKt η hη (hηV.trans hVK) i q (v k))
      hcη.mul_right (tsupport_mul_subset_left.trans (hηV.trans hVK)) (Function.update v k q) u) :
        𝓢'(FourSpace, ℂ))
  apply scalarReal_memSobolev_finset n
  intro k _
  apply scalarReal_memSobolev_finset n
  intro q _
  exact hreg _ _ _ (tsupport_mul_subset_left.trans hηV) _

include hreg in
theorem twoFormGramDerivativeCorrection_memSobolev_integer :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramDerivativeCorrection c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev (n : ℝ) 2 (C (_ + _))
  rw [map_add]
  exact (hreg _ _ _ ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hηV) v).add
    (twoFormGramConnection_memSobolev_integer n c S hS hK hKt hVK u hreg η hη hcη hηV v i)

theorem twoFormGramCovariant_memSobolev_integer
    (hregSucc : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramCovariantL2 c S hS hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
  have hvalue := hregSucc η hη hcη hηV v
  have hp : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormGramPartialL2 c S hK hKt η hη hcη
      (hηV.trans hVK) v i u) : 𝓢'(FourSpace, ℂ)) := by
    have hd := hvalue.lineDerivOp (m := EuclideanSpace.basisFun (Fin 4) ℝ i)
    change MemSobolev (((n + 1 : ℕ) : ℝ) - 1) 2 (scalarCoordinateDerivative i (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η hη hcη (hηV.trans hVK) v u) : 𝓢'(FourSpace, ℂ))) at hd
    rw [twoFormGram_complex_derivative] at hd
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hd
  have hc := (twoFormGramDerivativeCorrection_memSobolev_integer (n + 1) c S hS hK hKt hVK u
    hregSucc η hη hcη hηV v i).mono
      (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
  have he := eq_sub_of_add_eq (twoFormGramCovariant_add_correction c S hS hK hKt
    η hη hcη (hηV.trans hVK) v i u)
  rw [he]
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  exact hp.sub hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature potential preserves local integer Sobolev
regularity, with its outer cutoff constructed inside the given open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hreg in
theorem twoFormPotential_local_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))) : 𝓢'(FourSpace, ℂ)) := by
  obtain ⟨χ, hχ, hcχ, hχV, hone⟩ := exists_scalar_compact_cutoff hcη hV hηV
  rw [twoFormPotential_chart_pair c S hS hK hKt χ hχ hcχ (hχV.trans hVK)
    η hη hcη (hηV.trans hVK) hone]
  apply twoFormCoefficientPair_memSobolev_integer
    (twoFormPotentialCoefficient (g := g) c S η r)
    (twoFormPotentialCoefficient_smooth c S η hη ((hηV.trans hVK).trans hKt) r)
    (twoFormPotentialCoefficient_compact c S η hcη r) n
  intro k
  rw [twoFormGramVectorComponent]
  exact hreg χ hχ hcχ hχV (twoFormComponentIndex k)

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

/-! The connection correction of a locally Sobolev two-form has one lower order
divergence. The witnesses are actual Euclidean L2 functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) (hVK : V ⊆ K)
  (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hreg in
theorem twoFormFluxCorrection_memSobolev_successor (j : Fin 4) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2 (twoFormFluxCorrection c S hS hK hKt
      η hη hcη (hηV.trans hVK) b u j) : 𝓢'(FourSpace, ℂ)) := by
  apply scalarReal_memSobolev_finset (n + 1)
  intro i _
  apply twoFormCoefficientPair_memSobolev_integer
    (twoFormFluxCoefficient (g := g) c η b i j)
    (twoFormFluxCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b i j)
    hcη.mul_right.smul_right (n + 1)
  intro r
  rw [twoFormGramCorrectionVector_component]
  exact twoFormGramDerivativeCorrection_memSobolev_integer (n + 1) c S hS hK hKt hVK u hreg
    η hη hcη hηV (twoFormComponentIndex r) i

include hreg in
theorem twoFormFluxCorrection_integer_derivatives :
    ∃ D : Fin 4 → Lp ℝ 2 (volume : Measure FourSpace),
      (∀ j, scalarCoordinateDerivative j (scalarComplexL2
        (twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j) :
          𝓢'(FourSpace, ℂ)) = (scalarComplexL2 (D j) : 𝓢'(FourSpace, ℂ))) ∧
      ∀ j, MemSobolev (n : ℝ) 2 (scalarComplexL2 (D j) : 𝓢'(FourSpace, ℂ)) := by
  have he (j : Fin 4) : ∃ D : Lp ℝ 2 (volume : Measure FourSpace),
      scalarCoordinateDerivative j (scalarComplexL2
        (twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j) :
          𝓢'(FourSpace, ℂ)) = (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) ∧
      MemSobolev (n : ℝ) 2 (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) := by
    exact scalar_real_derivative_sobolev n _
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        twoFormFluxCorrection_memSobolev_successor n c S hS hK hKt hVK u hreg η hη hcη hηV b j) j
  choose D hD hregD using he
  exact ⟨D, hD, hregD⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The lower-order harmonic source has one fewer derivative than the
locally controlled two-form, at every finite order used by the bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hreg in
theorem twoFormInnerNabla_component_integer (i : Fin 4) (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
        𝓢'(FourSpace, ℂ)) := by
  dsimp only [twoFormGramNablaL2]
  rw [twoFormVectorComponentL2_assemble]
  exact twoFormGramCovariant_memSobolev_integer n c S hS hK hKt hVK u η hη hcη hηV
    (twoFormComponentIndex r) i hreg

end
end PositiveEinsteinFour.Geometry
end


section

/-! The linear eigenvalue source in the actual Hodge equation has the finite
Sobolev regularity required by the local elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o) (κ : ℝ)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hreg in
theorem twoFormEigen_forcing_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
          κ • twoFormH1ToL2 u))) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))))
  simp only [map_add]
  exact ((twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
    η hη hcη hηV r).mono hle).add
      (by
        rw [map_smul, map_smul, twoFormL2GramValue_H1 c S hS, twoFormGramVectorComponent]
        exact scalar_real_sobolev_smul (n : ℝ) κ _
          ((hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle))

include hV hreg in
theorem twoFormEigenDivergenceSource_integer (b : TwoFormFour) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
            κ • twoFormH1ToL2 u))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact (twoFormEigen_forcing_integer n c S hS hK hKt hV hVK u κ hreg η hη hcη hηV r).sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Hodge operator as a densely defined operator on L2.
Its domain is the range of the shifted resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHodgeDomain (hRic : RicciThree g) : Submodule ℝ (TwoFormL2 o) :=
  (twoFormShiftedResolvent hRic).range

def twoFormHodgeDomainEquiv (hRic : RicciThree g) :
    TwoFormL2 o ≃ₗ[ℝ] twoFormHodgeDomain (o := o) hRic :=
  LinearEquiv.ofInjective (twoFormShiftedResolvent hRic).toLinearMap
    (twoFormShiftedResolvent_injective hRic)

def twoFormHodgeGenerator (hRic : RicciThree g) :
    twoFormHodgeDomain (o := o) hRic →ₗ[ℝ] TwoFormL2 o :=
  (twoFormHodgeDomainEquiv hRic).symm.toLinearMap - (twoFormHodgeDomain hRic).subtype

end
end PositiveEinsteinFour.Geometry
end


section

/-! A complete orthonormal basis of actual smooth Hodge eigenforms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev TwoFormEigenIndex (hRic : RicciThree g) :=
  Σ μ : TwoFormSpectralValue (o := o) hRic, Fin (Module.finrank ℝ (TwoFormSpectralSpace hRic μ))

def twoFormEigenvector (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) : TwoFormL2 o :=
  (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic i.1) i.2).val

theorem twoFormEigenvector_orthonormal (hRic : RicciThree g) :
    Orthonormal ℝ (twoFormEigenvector (o := o) hRic) :=
  (twoFormShiftedResolvent_symmetric hRic).orthogonalFamily_eigenspaces'.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic μ)).orthonormal)

theorem twoFormEigenvector_span (hRic : RicciThree g) :
    Submodule.span ℝ (Set.range (twoFormEigenvector (o := o) hRic)) =
      ⨆ μ : TwoFormSpectralValue (o := o) hRic, TwoFormSpectralSpace hRic μ := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (fun μ => TwoFormSpectralSpace hRic μ) i.1)
      (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic i.1) i.2).property
  · apply iSup_le
    intro μ x hx
    let b := stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic μ)
    have he := congrArg (TwoFormSpectralSpace hRic μ).subtype
      (b.sum_repr (⟨x, hx⟩ : TwoFormSpectralSpace hRic μ))
    simp only [map_sum, map_smul] at he
    change (∑ j, (b.repr ⟨x, hx⟩) j • (b j : TwoFormL2 o)) = x at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩

def twoFormEigenbasis (hRic : RicciThree g) :
    HilbertBasis (TwoFormEigenIndex (o := o) hRic) ℝ (TwoFormL2 o) :=
  HilbertBasis.mk (twoFormEigenvector_orthonormal hRic) (by
    rw [twoFormEigenvector_span, twoFormSpectral_total hRic])

theorem twoFormEigenvector_hasEigenvector (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    Module.End.HasEigenvector (twoFormShiftedResolvent hRic).toLinearMap i.1.val
      (twoFormEigenvector hRic i) := by
  refine ⟨(stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic i.1) i.2).property, ?_⟩
  have hn := (twoFormEigenvector_orthonormal hRic).1 i
  intro h
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

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

/-! The second-order image of a compact C4 normal amplitude is an actual
compact C2 amplitude, so it can be realized in the same global L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOperatorAmplitude_regular (E : HeatNormalBundleExtension D)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) :
    ContDiff ℝ 2 (heatNormalOperatorAmplitude E a) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  apply fourHeatBundleOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · exact fun i j => (E.base.a_regular i j).of_le (by norm_num)
  · exact fun i => (E.base.b_regular i).of_le (by norm_num)
  · exact fun i k l => (E.B_regular i k l).of_le (by norm_num)
  · exact fun k l => (E.C_regular k l).of_le (by norm_num)
  · intro l
    exact (contDiff_piLp (p := 2)).mp ha l

theorem heatNormalOperatorAmplitude_support (E : HeatNormalBundleExtension D)
    (a : FourSpace → TwoFormFour) :
    tsupport (heatNormalOperatorAmplitude E a) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra hn
  have hz : a =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hk (k : Fin 6) : (fun y => a y k) =ᶠ[𝓝 x] (fun _ => 0) :=
    hz.mono fun y hy => by change a y k = 0; rw [hy]; rfl
  apply hx
  apply WithLp.ofLp_injective 2
  funext k
  exact fourHeatBundleOperator_zero_of_locally_zero (E.base.a x) (E.base.b x) (E.B x)
    (E.C x) hk k

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact C4 normal amplitude and its actual coefficient image lie
in the global L2 space, and the former belongs to the Hodge generator domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalHodgeImage (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D C hCt hP hD (heatNormalOperatorAmplitude E a)
    (heatNormalOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOperatorAmplitude_support E a))
    ((heatNormalOperatorAmplitude_support E a).trans hs)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


