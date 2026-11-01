-- Prove2me | Definitions.Def_OAIQ091C013
-- name    : OAIQ091C013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:04:45.879387+00:00
-- url     : https://prove2.me/theorems/7508e380-e552-41ce-8086-4f655c8aa34b
-- title:
--   Definitions bundle OAIQ091C013 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 9 definitions and 33 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.CoordinateFrameSpace`, `OAI.PositiveEinsteinFour.Geometry.EuclideanUnitSphere`, `OAI.PositiveEinsteinFour.Geometry.frameChartMatrix`, `OAI.PositiveEinsteinFour.Geometry.gramColumnOne`, `OAI.PositiveEinsteinFour.Geometry.gramColumnTwo`, `OAI.PositiveEinsteinFour.Geometry.gramRemove`, `OAI.PositiveEinsteinFour.Geometry.orientationFrameClass`, `OAI.PositiveEinsteinFour.Geometry.parallelFrameConnection`, `OAI.PositiveEinsteinFour.Geometry.twoFormFrameValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_AngularClifford`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularClifford.lean), [`EinsteinFour_AngularCurvature`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularCurvature.lean), [`EinsteinFour_AngularDerivativeMoments`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularDerivativeMoments.lean), [`EinsteinFour_AngularGradient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularGradient.lean), [`EinsteinFour_AngularNormal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularNormal.lean), [`EinsteinFour_AngularRotation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularRotation.lean), [`EinsteinFour_AngularTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularTrace.lean), [`EinsteinFour_Bianchi`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/Bianchi.lean), [`EinsteinFour_CurvatureContraction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureContraction.lean), [`EinsteinFour_CurvatureTensors02`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/CurvatureTensors02.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C036`, `OAIQ091C007` and `OAIQ091C008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C017` and `OAIQ091C018`; the proofs of `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi`, `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_matrix`, `OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost` and `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C036
import Definitions.Def_OAIQ091C007
import Definitions.Def_OAIQ091C008

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Bianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

/-- Completeness relation of the two orthogonal normalized spectral vectors. -/
theorem Shape.frame (S : Shape) (i j : Fin 3) :
    S.s i * S.s j / 6 + difference S.s i * difference S.s j / 18 =
      (if i = j then 1 else 0) - 1 / 3 := by
  have ht := S.trace
  have hn := S.square
  simp [Fin.sum_univ_succ] at ht hn
  have ht2 : S.s 2 = -S.s 0 - S.s 1 := by linarith
  have hn2 : S.s 0 ^ 2 + S.s 0 * S.s 1 + S.s 1 ^ 2 = 3 := by
    rw [ht2] at hn
    nlinarith
  fin_cases i <;> fin_cases j <;> simp [difference, next, previous, ht2] <;> nlinarith

/-- Every trace-free diagonal triple is recovered by the two coordinates. -/
theorem diagonal_reconstruction (S : Shape) (T : Tensor) (ht : T.traceFree) (i : Fin 3) :
    T.diagonal i = S.s i • radialCoordinate S T - difference S.s i • secondCoordinate S T := by
  unfold radialCoordinate secondCoordinate
  calc
    T.diagonal i = ∑ j : Fin 3, ((if i = j then (1 : ℝ) else 0) - 1 / 3) • T.diagonal j := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      have ht0 : ∑ j, T.diagonal j = 0 := ht
      simp [ht0]
    _ = ∑ j : Fin 3, (S.s i * S.s j / 6 + difference S.s i * difference S.s j / 18) •
        T.diagonal j := by simp only [S.frame]
    _ = _ := by
      ext j
      simp [Fin.sum_univ_succ]
      ring

/-- A quaternionic Bianchi tensor is exactly the explicit parameter tensor;
this also gives uniqueness by the three coordinate recovery identities. -/
theorem parameters_reconstruction (S : Shape) (T : Tensor)
    (ht : T.traceFree) (hb : T.bianchi) :
    parameters S (radialCoordinate S T) (secondCoordinate S T) (thirdCoordinate S T) = T := by
  have hd := diagonal_reconstruction S T ht
  have hc := (T.bianchi_iff).mp hb
  let p := radialCoordinate S T
  let k := secondCoordinate S T
  let l := thirdCoordinate S T
  have hres (i : Fin 3) :
      T.auxiliary (next i) - S.s (next i) • k - (difference S.s (next i) / 3) • p =
      T.auxiliary (previous i) - S.s (previous i) • k - (difference S.s (previous i) / 3) • p := by
    apply sub_eq_zero.mp
    calc
      _ = T.auxiliary (next i) - T.auxiliary (previous i) -
          (S.s (next i) - S.s (previous i)) • k -
          ((difference S.s (next i) - difference S.s (previous i)) / 3) • p := by module
      _ = S.s i • p - difference S.s i • k +
          T.auxiliary (next i) - T.auxiliary (previous i) := by
        rw [S.difference_next_sub_previous]
        dsimp [difference]
        module
      _ = 0 := by
        change S.s i • radialCoordinate S T - difference S.s i • secondCoordinate S T +
          T.auxiliary (next i) - T.auxiliary (previous i) = 0
        rw [← hd i]
        exact hc i
  have hcommon (i : Fin 3) :
      T.auxiliary i - S.s i • k - (difference S.s i / 3) • p = l := by
    have h0 := hres 0
    have h1 := hres 1
    simp only [next, previous, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hl := thirdCoordinate_eq S T
    change l = T.auxiliary 0 - S.s 0 • k - (difference S.s 0 / 3) • p at hl
    fin_cases i
    · exact hl.symm
    · exact h0.trans (h1.trans hl.symm)
    · exact h1.trans hl.symm
  have hoff (i : Fin 3) : T.auxiliary i = l + S.s i • k + (difference S.s i / 3) • p := by
    calc
      _ = (T.auxiliary i - S.s i • k - (difference S.s i / 3) • p) +
          S.s i • k + (difference S.s i / 3) • p := by module
      _ = _ := by rw [hcommon]
  apply Tensor.ext
  · funext i
    exact (hd i).symm
  · funext i
    apply quaternion_injective i
    change (parameters S (radialCoordinate S T) (secondCoordinate S T)
      (thirdCoordinate S T)).auxiliary i = T.auxiliary i
    rw [parameters_auxiliary]
    exact (hoff i).symm

/-- The refined Kato inequality follows from the full parametrization for
every symmetric tensor satisfying the actual Bianchi constraint. -/
theorem refined_kato (S : Shape) (T : Tensor) (ht : T.traceFree) (hb : T.bianchi) :
    (5 / 3) * ‖radialCoordinate S T‖ ^ 2 ≤ T.squaredNorm / 6 := by
  have h := parameters_energy S (radialCoordinate S T) (secondCoordinate S T) (thirdCoordinate S T)
  rw [parameters_reconstruction S T ht hb] at h
  nlinarith [sq_nonneg ‖secondCoordinate S T‖, sq_nonneg ‖thirdCoordinate S T‖]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual change of normal bases `I_s q` and `J_t q`. Its spherical
orthogonality is a consequence of the fourth monomial moment. -/

namespace PositiveEinsteinFour.Angular

open Matrix

noncomputable section

theorem mixingCoefficient_symmetric (r s : Fin 3) :
    (mixingCoefficient r s)ᵀ = mixingCoefficient r s := by
  rw [mixingCoefficient_eq_table]
  ext i j
  change coefficientTable r s j i = coefficientTable r s i j
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [coefficientTable]

theorem mixingCoefficient_trace (r s : Fin 3) :
    (mixingCoefficient r s).trace = 0 := by
  rw [mixingCoefficient_eq_table]
  fin_cases r <;> fin_cases s <;>
    norm_num [coefficientTable, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem integral_mixing_mul (h : FollandMoments) (r s t u : Fin 3) :
    (∫ q, mixing r s q * mixing t u q ∂sphereMeasure) =
      if r = t then (if s = u then (1 / 3 : ℝ) else 0) else 0 := by
  unfold mixing
  rw [integral_quadratic_mul_traceFree h _ _ (mixingCoefficient_trace r s)
    (mixingCoefficient_trace t u) (mixingCoefficient_symmetric t u),
    mixingCoefficient_pairing]
  split_ifs <;> norm_num

/-- The two triples give orthonormal normal bases for every unit direction. -/
theorem mixing_orthogonal (q : Directions) :
    mixingMatrix q * (mixingMatrix q)ᵀ = 1 := by
  ext i j
  change (∑ s, mixing i s q * mixing j s q) = if i = j then 1 else 0
  calc
    _ = (∑ a, q.val a ^ 2) ^ 2 * (if i = j then 1 else 0) := by
      simp only [mixing, quadratic, mixingCoefficient_eq_table]
      fin_cases i <;> fin_cases j <;>
        simp [coefficientTable, Fin.sum_univ_succ]
      all_goals ring
    _ = _ := by rw [direction_sum_sq]; simp

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularClifford
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion matrix identities for the sixth-moment mixed contraction. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

theorem oppositeMatrix_anticommutator_zero (j : Fin 3) :
    oppositeMatrix 0 * oppositeMatrix j + oppositeMatrix j * oppositeMatrix 0 =
      (if (0 : Fin 3) = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ] <;> norm_num

theorem oppositeMatrix_anticommutator_two (j : Fin 3) :
    oppositeMatrix 2 * oppositeMatrix j + oppositeMatrix j * oppositeMatrix 2 =
      (if (2 : Fin 3) = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  ext a b
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ] <;> norm_num

theorem oppositeMatrix_anticommutator (i j : Fin 3) :
    oppositeMatrix i * oppositeMatrix j + oppositeMatrix j * oppositeMatrix i =
      (if i = j then (-2 : ℝ) else 0) • (1 : Mat4) := by
  fin_cases i
  · exact oppositeMatrix_anticommutator_zero j
  · exact oppositeMatrix_anticommutator_one j
  · exact oppositeMatrix_anticommutator_two j

/-- The symmetrized product collapses to the scalar Clifford relation. -/
theorem mixingCoefficient_product_symm (i j k l : Fin 3) :
    mixingCoefficient i k * mixingCoefficient j l +
      mixingCoefficient j l * mixingCoefficient i k +
      mixingCoefficient j k * mixingCoefficient i l +
      mixingCoefficient i l * mixingCoefficient j k =
        (if i = j then (if k = l then (4 : ℝ) else 0) else 0) • (1 : Mat4) := by
  simp only [mixingCoefficient_product]
  calc
    _ = (quaternionMatrix i * quaternionMatrix j + quaternionMatrix j * quaternionMatrix i) *
        (oppositeMatrix k * oppositeMatrix l + oppositeMatrix l * oppositeMatrix k) := by
      noncomm_ring
    _ = _ := by
      rw [quaternionMatrix_anticommutator, oppositeMatrix_anticommutator]
      by_cases hij : i = j <;> by_cases hkl : k = l <;>
        norm_num [hij, hkl, smul_smul]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

theorem squareNorm_rotated (U : Mat3) (q : Directions) :
    squareNorm (rotated U q) = squareNorm U :=
  squareNorm_conjugate _ _ (mixing_orthogonal q)

theorem squareNorm_normalDeviation (T U : Mat3) (q : Directions) :
    squareNorm (normalDeviation T U q) =
      (squareNorm T + squareNorm U + 2 * pairing T (rotated U q)) / 4 := by
  rw [← squareNorm_rotated U q]
  simpa only [squareNorm, pairing, normalDeviation, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul] using! norm_add_half T (rotated U q)

theorem integral_mixed_pairing (h : FollandMoments) (T U : Mat3)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (∫ q, pairing T (rotated U q) ∂sphereMeasure) = 0 := by
  have he : (fun q => pairing T (rotated U q)) = fun q =>
      ∑ i, ∑ j, ∑ k, ∑ l, T i j * U k l * (mixing i k q * mixing j l q) := by
    funext q
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    simp only [mixingMatrix]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_sum4 h _ (fun _ _ _ _ => by unfold mixing quadratic; fun_prop)]
  simp_rw [integral_const_mul, integral_mixing_mul h]
  have ht : ∑ i, T i i = 0 := hT
  have hu : ∑ i, U i i = 0 := hU
  have hs := pairing_delta_sum T U
  rw [ht, hu] at hs
  simpa only [zero_mul, zero_div] using! hs

/-- The first identity in the manuscript's geodesic averages, on each
individual unit tangent sphere. -/
theorem integral_squareNorm_normalDeviation (h : FollandMoments) (T U : Mat3)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (∫ q, squareNorm (normalDeviation T U q) ∂sphereMeasure) =
      (squareNorm T + squareNorm U) / 4 := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  have hc : Continuous (fun q => pairing T (rotated U q)) := by
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply]
    simp only [mixingMatrix, mixing, quadratic]
    fun_prop
  have hi := continuous_integrable h hc
  have he : (fun q => squareNorm (normalDeviation T U q)) =
      fun q => (squareNorm T + squareNorm U + 2 * pairing T (rotated U q)) / 4 :=
    funext (squareNorm_normalDeviation T U)
  rw [he, integral_div, integral_add (integrable_const _) (hi.const_mul 2),
    integral_const_mul, integral_mixed_pairing h T U hT hU]
  simp

theorem integral_squareNorm_normalDeviation_normalized (h : FollandMoments) (T U : Mat3)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (∫ q, squareNorm (normalDeviation T U q) ∂sphereMeasure) =
      (3 / 2) * (Geometry.normalizedBlockNorm T ^ 2 +
        Geometry.normalizedBlockNorm U ^ 2) := by
  rw [integral_squareNorm_normalDeviation h T U hT hU,
    Geometry.normalizedBlockNorm_sq, Geometry.normalizedBlockNorm_sq]
  unfold squareNorm
  ring

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal Jacobi form of the actual quaternion curvature decomposition. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

theorem twoFormNormal_plus (q : Directions) (i s : Fin 3) :
    twoFormNormal (quaternionMatrix s) q i = if i = s then 1 else 0 := by
  calc
    _ = (∑ a, q.val a ^ 2) * (if i = s then 1 else 0) := by
      fin_cases i <;> fin_cases s <;>
        simp [twoFormNormal, normalVector, quaternionMatrix, Fin.sum_univ_succ]
      all_goals ring
    _ = _ := by rw [direction_sum_sq]; simp

theorem twoFormNormal_minus (q : Directions) (i s : Fin 3) :
    twoFormNormal (oppositeMatrix s) q i = mixing i s q := by
  simp only [mixing, quadratic, mixingCoefficient_eq_table]
  fin_cases i <;> fin_cases s <;>
    simp [twoFormNormal, normalVector, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, coefficientTable, Fin.sum_univ_succ]
  all_goals ring

/-- Curvature decomposition gives the normal matrix used by the Jacobi ODE. -/
theorem normalEvaluation_einstein (T U : Mat3) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (einsteinCurvatureTensor T U) =
      (1 + normalDeviation T U q) i j := by
  rw [einsteinCurvatureTensor, map_add, normalEvaluation_blockTensor,
    normalEvaluation_blockTensor]
  simp_rw [twoFormNormal_plus, twoFormNormal_minus]
  have ho := congrArg (fun A : Mat3 => A i j) (mixing_orthogonal q)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, mixingMatrix] at ho
  have hm : (∑ s, ∑ t, U s t * (mixing i s q * mixing j t q)) =
      (∑ t, (∑ s, mixing i s q * U s t) * mixing j t q) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp only [Matrix.add_apply, Matrix.one_apply, normalDeviation,
    Matrix.smul_apply, smul_eq_mul, rotated, Matrix.mul_apply,
    Matrix.transpose_apply, mixingMatrix, add_mul, Finset.sum_add_distrib,
    mul_add, mul_ite, ite_mul, mul_zero, zero_mul, one_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [ho, hm]
  simp only [Matrix.one_apply]
  by_cases hij : i = j <;> simp only [hij, ite_true, if_true, ite_false, if_false] <;> ring

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularGradient
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The directional-derivative part of the angular average. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

/-- The two individual terms are exact directional averages; the mixed
term is retained explicitly. -/
theorem integral_normalDerivative_squareNorm (h : FollandMoments) (Z W : Gradient) :
    (∫ q, squareNorm (normalDerivative Z W q) ∂sphereMeasure) =
      (gradientSquareNorm Z + gradientSquareNorm W) / 16 +
        (∫ q, pairing (directional Z q) (rotated (directional W q) q)
          ∂sphereMeasure) / 2 := by
  have hZ : Integrable (fun q => squareNorm (directional Z q)) sphereMeasure :=
    continuous_integrable h (by
      simp only [squareNorm, directional, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop)
  have hW : Integrable (fun q => squareNorm (directional W q)) sphereMeasure :=
    continuous_integrable h (by
      simp only [squareNorm, directional, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      fun_prop)
  have hP : Integrable
      (fun q => pairing (directional Z q) (rotated (directional W q) q)) sphereMeasure :=
    continuous_integrable h (by
      simp only [pairing, directional, rotated, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      simp only [mixingMatrix, mixing, quadratic]
      fun_prop)
  have he : (fun q => squareNorm (normalDerivative Z W q)) =
      fun q => (squareNorm (directional Z q) + squareNorm (directional W q) +
        2 * pairing (directional Z q) (rotated (directional W q) q)) / 4 := by
    funext q
    exact squareNorm_normalDeviation _ _ q
  have hZW : Integrable (fun q =>
      squareNorm (directional Z q) + squareNorm (directional W q)) sphereMeasure := hZ.add hW
  rw [he, integral_div, integral_add hZW (hP.const_mul 2),
    integral_add hZ hW, integral_const_mul,
    integral_directional_squareNorm h Z, integral_directional_squareNorm h W]
  ring

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularDerivativeMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.QuaternionFrame.rawField_fieldRaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite Weyl blocks have zero mixed directional energy. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

theorem weightedMixingMoment_symm (h : FollandMoments)
    (a b : Fin 4) (i j k l : Fin 3) :
    weightedMixingMoment a b i j k l + weightedMixingMoment a b j i k l =
      if i = j then (if k = l then delta a b / 6 else 0) else 0 := by
  unfold weightedMixingMoment mixing
  rw [integral_weighted_quadratic_mul_traceFree h _ _
    (mixingCoefficient_trace i k) (mixingCoefficient_trace j l)
    (mixingCoefficient_symmetric i k) (mixingCoefficient_symmetric j l),
    integral_weighted_quadratic_mul_traceFree h _ _
    (mixingCoefficient_trace j k) (mixingCoefficient_trace i l)
    (mixingCoefficient_symmetric j k) (mixingCoefficient_symmetric i l)]
  rw [mixingCoefficient_pairing, mixingCoefficient_pairing]
  have hp := congrArg (fun A : Mat4 => A a b) (mixingCoefficient_product_symm i j k l)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at hp
  simp only [Matrix.add_apply]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> by_cases hab : a = b <;>
    simp [hij, hkl, hab, eq_comm, delta] at hp ⊢ <;> linarith

/-- The sixth moment cancels against a symmetric trace-free plus block.
No differential Bianchi premise is needed for this angular identity. -/
theorem weighted_mixing_contraction_zero (h : FollandMoments)
    (T U : Fin 3 → Fin 3 → ℝ) (hT : ∀ i j, T i j = T j i)
    (ht : ∑ i, T i i = 0) (a b : Fin 4) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      T i j * U k l * weightedMixingMoment a b i j k l) = 0 := by
  have hz (k l : Fin 3) :
      (∑ i, ∑ j, T i j * weightedMixingMoment a b i j k l) = 0 := by
    have hs := symmetric_contraction T (fun i j => weightedMixingMoment a b i j k l) hT
    simp_rw [weightedMixingMoment_symm h] at hs
    by_cases hkl : k = l
    · simp [hkl, mul_ite, ← Finset.sum_mul, ht] at hs
      simpa only [hkl] using hs
    · simp [hkl] at hs
      linarith
  rw [sum4_swap]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  calc
    (∑ i, ∑ j, T i j * U k l * weightedMixingMoment a b i j k l) =
        U k l * (∑ i, ∑ j, T i j * weightedMixingMoment a b i j k l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hz, mul_zero]

/-- A weighted mixed contraction vanishes pointwise over the base. -/
theorem integral_weighted_pairing_zero (h : FollandMoments) (T U : Mat3)
    (hTs : Tᵀ = T) (hTt : T.trace = 0) (a b : Fin 4) :
    (∫ q, q.val a * q.val b * pairing T (rotated U q) ∂sphereMeasure) = 0 := by
  have he : (fun q : Directions => q.val a * q.val b * pairing T (rotated U q)) =
      fun q => ∑ i, ∑ j, ∑ k, ∑ l, T i j * U k l *
        (q.val a * q.val b * (mixing i k q * mixing j l q)) := by
    funext q
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    simp only [mixingMatrix]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_sum4 h _ (fun _ _ _ _ => by unfold mixing quadratic; fun_prop)]
  simp_rw [integral_const_mul]
  have hs (i j : Fin 3) : T i j = T j i :=
    (congrFun (congrFun hTs i) j).symm
  have ht : ∑ i, T i i = 0 := hTt
  simpa only [weightedMixingMoment] using!
    weighted_mixing_contraction_zero h T U hs ht a b

/-- The exact derivative mixed cancellation uses only symmetry and zero trace. -/
theorem integral_directional_pairing_zero (h : FollandMoments) (Z W : Gradient)
    (hZs : ∀ a, (Z a)ᵀ = Z a) (hZt : ∀ a, (Z a).trace = 0) :
    (∫ q, pairing (directional Z q) (rotated (directional W q) q) ∂sphereMeasure) = 0 := by
  have he : (fun q => pairing (directional Z q) (rotated (directional W q) q)) =
      fun q => ∑ a, ∑ b, q.val a * q.val b * pairing (Z a) (rotated (W b) q) :=
    funext (directional_pairing Z W)
  have hc (a b : Fin 4) : Continuous (fun q : Directions =>
      q.val a * q.val b * pairing (Z a) (rotated (W b) q)) := by
    simp only [pairing, rotated, Matrix.mul_apply, Matrix.transpose_apply]
    simp only [mixingMatrix, mixing, quadratic]
    fun_prop
  rw [he, integral_sum h _ (fun a => by fun_prop)]
  have hi (a : Fin 4) :
      (∫ q, ∑ b, q.val a * q.val b * pairing (Z a) (rotated (W b) q) ∂sphereMeasure) = 0 := by
    rw [integral_sum h _ (hc a)]
    simp_rw [integral_weighted_pairing_zero h _ _ (hZs a) (hZt a)]
    simp
  simp only [hi, Finset.sum_const_zero]

/-- The second exact angular energy identity used by the radial estimate. -/
theorem integral_normalDerivative_squareNorm_exact (h : FollandMoments) (Z W : Gradient)
    (hZs : ∀ a, (Z a)ᵀ = Z a) (hZt : ∀ a, (Z a).trace = 0) :
    (∫ q, squareNorm (normalDerivative Z W q) ∂sphereMeasure) =
      (gradientSquareNorm Z + gradientSquareNorm W) / 16 := by
  rw [integral_normalDerivative_squareNorm h,
    integral_directional_pairing_zero h Z W hZs hZt]
  ring

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularTrace
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal Jacobi trace follows from the classical Einstein curvature
decomposition and the two trace-free Weyl blocks. -/

namespace PositiveEinsteinFour.Angular

open Matrix

theorem rotated_trace (U : Mat3) (q : Directions) : (rotated U q).trace = U.trace := by
  have hO : (mixingMatrix q)ᵀ * mixingMatrix q = 1 :=
    mul_eq_one_comm.mp (mixing_orthogonal q)
  rw [rotated, Matrix.trace_mul_cycle, hO, one_mul]

theorem normalDeviation_trace (T U : Mat3) (q : Directions)
    (hT : T.trace = 0) (hU : U.trace = 0) :
    (normalDeviation T U q).trace = 0 := by
  simp [normalDeviation, Matrix.trace_smul, Matrix.trace_add, rotated_trace, hT, hU]

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureContraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion contractions in the derivative-slot Green formula. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi Angular

noncomputable section

theorem opposite_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, oppositeMatrix s i k * oppositeMatrix r i k) =
      if s = r then (4 : ℝ) else 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;> simp [oppositeMatrix, Geometry.oppositeQuaternion, TraceHessian.quaternionMatrix] <;> (try split_ifs) <;> norm_num

end

end PositiveEinsteinFour.CurvatureContraction

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A four-column Gram--Schmidt normalizer with entrywise smooth dependence
on the positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def gramRemove (G : Mat4) (u v : CoordinateColumn) : CoordinateColumn :=
  v - (metricPair G u v / metricPair G u u) • u

def gramColumnOne (G : Mat4) : CoordinateColumn :=
  gramRemove G (gramColumnZero G) (Pi.single 1 1)

def gramColumnTwo (G : Mat4) : CoordinateColumn :=
  gramRemove G (gramColumnOne G) (gramRemove G (gramColumnZero G) (Pi.single 2 1))

end
end PositiveEinsteinFour.Geometry
end


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

/-! Continuity of actual covariant tensors on the intrinsic orthonormal-frame
bundle, using one fixed tangent-bundle trivialization near each frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Components of an actual frame in the fixed chart at `c`. -/
def frameChartMatrix (g : SmoothMetric M) (c : M) (e : FrameBundle g) : Mat4 :=
  fun a b => ((trivializationAt FourSpace (TangentSpace I4 : M → Type _) c)
    (⟨e.base, e.frame.vector b⟩ : TangentBundle I4 M)).2 a

end
end PositiveEinsteinFour.Geometry
end


section

/-! A two-form written in the chosen oriented frame, with its values in
every other frame recovered by actual tensor pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormFrameValue (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) : TwoFormFour :=
  twoFormFrameAction ((o.frame e.base).changeMatrix e.frame) (u e.base)

theorem twoFormFrameValue_add (o : FrameOrientation g) (u v : M → TwoFormFour)
    (e : FrameBundle g) :
    twoFormFrameValue o (u + v) e = twoFormFrameValue o u e + twoFormFrameValue o v e :=
  (twoFormFrameActionLinear _).map_add _ _

theorem twoFormFrameValue_zero (o : FrameOrientation g) (e : FrameBundle g) :
    twoFormFrameValue o (0 : M → TwoFormFour) e = 0 :=
  (twoFormFrameActionLinear _).map_zero

theorem twoFormFrameValue_smul (o : FrameOrientation g) (r : ℝ) (u : M → TwoFormFour)
    (e : FrameBundle g) :
    twoFormFrameValue o (r • u) e = r • twoFormFrameValue o u e :=
  (twoFormFrameActionLinear _).map_smul r _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local horizontal frame vector field is smooth and preserves the
metric Gram matrix. The defining equations are ordinary finite-dimensional
ODEs in one coordinate chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

abbrev CoordinateFrameSpace := FourSpace × Mat4

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def parallelFrameConnection (g : SmoothMetric M) (c : M) (k : Fin 4)
    (p : CoordinateFrameSpace) : Mat4 :=
  ∑ r, p.2 r k • connectionMatrix g c r p.1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every orthonormal frame determines a continuous point of the actual
orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set Filter _root_.Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientationFrameClass (g : SmoothMetric M) (e : FrameBundle g) : OrientationCover M :=
  ⟨e.base, decide (0 < e.frame.matrix.det)⟩

@[simp] theorem orientationFrameClass_proj (g : SmoothMetric M) (e : FrameBundle g) :
    (orientationFrameClass g e).proj = e.base := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The angular measure in the actual four-dimensional Euclidean polar
decomposition, identified with the spherical measure used by the curvature
averages. No surface-area formula is needed for this identification. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set Metric
open scoped Pointwise

noncomputable section

abbrev EuclideanUnitSphere := sphere (0 : FourSpace) 1

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


