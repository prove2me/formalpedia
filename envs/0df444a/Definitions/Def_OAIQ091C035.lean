-- Prove2me | Definitions.Def_OAIQ091C035
-- name    : OAIQ091C035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:58:10.529416+00:00
-- url     : https://prove2.me/theorems/29832bc5-b0f6-4404-bade-f0cc67148ccd
-- title:
--   Definitions bundle OAIQ091C035 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 5 definitions and 25 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Angular.gradientSquareNorm`, `OAI.PositiveEinsteinFour.Angular.mixingMatrix`, `OAI.PositiveEinsteinFour.Angular.rotated`, `OAI.PositiveEinsteinFour.Angular.rotatedLinear`, `OAI.PositiveEinsteinFour.Angular.squareNorm`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_AngularClifford`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularClifford.lean), [`EinsteinFour_AngularDerivativeMoments`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularDerivativeMoments.lean), [`EinsteinFour_AngularGradient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularGradient.lean), [`EinsteinFour_AngularNormal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularNormal.lean), [`EinsteinFour_AngularQuadratic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularQuadratic.lean), [`EinsteinFour_AngularRotation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularRotation.lean), [`EinsteinFour_AngularSixth`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularSixth.lean), [`EinsteinFour_SphericalMoments`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/SphericalMoments.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C036` and `OAIQ091C053`; the proofs of `OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_0_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_1`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_1_2`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_0`, `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_1` and `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C006

section
-- module Solutions.OAIQ091_EF.Compat
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite sphere moments needed for the angular Jacobi calculation.
The conditional input below is precisely the degree 2, 4 and 6 specialization
of Folland, *How to Integrate a Polynomial over a Sphere*, American
Mathematical Monthly 108 (2001), 446–448, Theorem on p.447, after division by
the area of S³. DOI: 10.1080/00029890.2001.11919774.
It contains no curvature or geometric inequality.
-/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

theorem integral_sum {ι : Type*} [Fintype ι] (h : FollandMoments)
    (f : ι → Directions → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ q, ∑ i, f i q ∂sphereMeasure) = ∑ i, ∫ q, f i q ∂sphereMeasure := by
  exact integral_finsetSum _ (fun i _ => continuous_integrable h (hf i))

theorem integral_sum4 {ι κ ρ τ : Type*} [Fintype ι] [Fintype κ]
    [Fintype ρ] [Fintype τ] (h : FollandMoments)
    (f : ι → κ → ρ → τ → Directions → ℝ)
    (hf : ∀ i j k l, Continuous (f i j k l)) :
    (∫ q, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l q ∂sphereMeasure) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∫ q, f i j k l q ∂sphereMeasure := by
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_sum h _ (hf i j k)

theorem integral_quadratic (h : FollandMoments) (C : Fin 4 → Fin 4 → ℝ) :
    (∫ q : Directions, ∑ i, ∑ j, C i j * (q.val i * q.val j) ∂sphereMeasure) =
      (∑ i, C i i) / 4 := by
  let : IsProbabilityMeasure sphereMeasure := h.probability
  have hi (i j : Fin 4) : Integrable
      (fun q : Directions => C i j * (q.val i * q.val j)) sphereMeasure :=
    ((continuous_coordinate i).mul (continuous_coordinate j)).const_mul _ |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul, h.second]
  simp [momentTwo, delta, div_eq_mul_inv, mul_ite, ite_mul, Finset.sum_mul]

/-- A directional derivative has one fourth of its full squared norm on S³. -/
theorem integral_directional_square (h : FollandMoments) (v : Fin 4 → ℝ) :
    (∫ q : Directions, (∑ i, q.val i * v i) ^ 2 ∂sphereMeasure) =
      (∑ i, v i ^ 2) / 4 := by
  have heq : (fun q : Directions => (∑ i, q.val i * v i) ^ 2) =
      (fun q => ∑ i, ∑ j, (v i * v j) * (q.val i * q.val j)) := by
    funext q
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_quadratic h]
  simp only [pow_two]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularQuadratic
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular averages of two quadratic forms, from the precise fourth
spherical moment. This is used for the two Weyl blocks in the normal Jacobi
matrix; no curvature average is an input. -/

namespace PositiveEinsteinFour.Angular

open MeasureTheory Matrix

noncomputable section

theorem integral_quadratic_mul (h : FollandMoments) (C D : Mat4) :
    (∫ q, quadratic C q * quadratic D q ∂sphereMeasure) =
      ∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l := by
  have hexp : (fun q => quadratic C q * quadratic D q) =
      (fun q => ∑ i, ∑ j, ∑ k, ∑ l,
        C i j * D k l * (q.val i * q.val j * q.val k * q.val l)) := by
    funext q
    unfold quadratic
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hexp, integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, h.fourth]

/-- The finite contraction is stated on functions so that no matrix
coercion is unfolded inside the simplifier. -/
theorem fourth_sum_formula (C D : Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l) =
      ((∑ i, C i i) * (∑ j, D j j) + (∑ i, ∑ j, C i j * D i j) +
        (∑ i, ∑ j, C i j * D j i)) / 24 := by
  have hm (i j k l : Fin 4) : C i j * D k l * momentFour i j k l =
      (C i j * D k l * delta i j * delta k l +
       C i j * D k l * delta i k * delta j l +
       C i j * D k l * delta i l * delta j k) / 24 := by
    unfold momentFour
    ring
  simp_rw [hm, ← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  simp [delta, mul_ite, Finset.sum_mul_sum]

/-- Fourth moments give the complete bilinear quadratic-form formula. -/
theorem integral_quadratic_mul_formula (h : FollandMoments) (C D : Mat4) :
    (∫ q, quadratic C q * quadratic D q ∂sphereMeasure) =
      (C.trace * D.trace + (∑ i, ∑ j, C i j * D i j) +
        (∑ i, ∑ j, C i j * D j i)) / 24 := by
  rw [integral_quadratic_mul h]
  simpa only [Matrix.trace, Matrix.diag] using! fourth_sum_formula C D

theorem integral_quadratic_mul_traceFree (h : FollandMoments) (C D : Mat4)
    (hC : C.trace = 0) (hD : D.trace = 0) (hDs : Dᵀ = D) :
    (∫ q, quadratic C q * quadratic D q ∂sphereMeasure) =
      (∑ i, ∑ j, C i j * D i j) / 12 := by
  rw [integral_quadratic_mul_formula h, hC, hD]
  have hd (i j : Fin 4) : D j i = D i j := congrFun (congrFun hDs i) j
  simp_rw [hd]
  ring

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

theorem mixingCoefficient_eq_table (r s : Fin 3) :
    mixingCoefficient r s = coefficientTable r s := by
  ext i j
  simp only [mixingCoefficient, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [TraceHessian.quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, coefficientTable, Fin.sum_univ_succ]

def mixingMatrix (q : Directions) : Geometry.Mat3 := fun r s => mixing r s q

theorem mixingCoefficient_pairing (r s t u : Fin 3) :
    (∑ i, ∑ j, mixingCoefficient r s i j * mixingCoefficient t u i j) =
      if r = t then (if s = u then (4 : ℝ) else 0) else 0 := by
  simp only [mixingCoefficient_eq_table]
  fin_cases r <;> fin_cases s <;> fin_cases t <;> fin_cases u <;>
    norm_num [coefficientTable, Fin.sum_univ_succ]

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

theorem oppositeMatrix_commute (i j : Fin 3) :
    oppositeMatrix i * quaternionMatrix j = quaternionMatrix j * oppositeMatrix i := by
  ext a b
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [oppositeMatrix, Geometry.oppositeQuaternion, quaternionMatrix,
      Fin.sum_univ_succ] <;> norm_num

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def squareNorm (T : Mat3) : ℝ := ∑ i, ∑ j, T i j ^ 2

def rotated (U : Mat3) (q : Directions) : Mat3 :=
  mixingMatrix q * U * (mixingMatrix q)ᵀ

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularGradient
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The directional-derivative part of the angular average. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def gradientSquareNorm (Z : Gradient) : ℝ := ∑ i, squareNorm (Z i)

theorem integral_directional_entries (h : FollandMoments)
    (Z : Fin 4 → Fin 3 → Fin 3 → ℝ) :
    (∫ q : Directions, ∑ r, ∑ s, (∑ a, q.val a * Z a r s) ^ 2 ∂sphereMeasure) =
      (∑ a, ∑ r, ∑ s, Z a r s ^ 2) / 4 := by
  calc
    _ = ∑ r, ∫ q : Directions, ∑ s, (∑ a, q.val a * Z a r s) ^ 2 ∂sphereMeasure :=
      integral_sum h _ (fun _ => by fun_prop)
    _ = ∑ r, ∑ s, ∫ q : Directions, (∑ a, q.val a * Z a r s) ^ 2 ∂sphereMeasure := by
      apply Finset.sum_congr rfl
      intro r _
      exact integral_sum h _ (fun _ => by fun_prop)
    _ = ∑ r, ∑ s, (∑ a, Z a r s ^ 2) / 4 := by
      simp_rw [integral_directional_square h]
    _ = _ := by
      simp_rw [← Finset.sum_div]
      congr 1
      calc
        _ = ∑ r, ∑ a, ∑ s, Z a r s ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

theorem integral_directional_squareNorm (h : FollandMoments) (Z : Gradient) :
    (∫ q, squareNorm (directional Z q) ∂sphereMeasure) = gradientSquareNorm Z / 4 := by
  simpa only [squareNorm, directional, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, gradientSquareNorm] using!
      integral_directional_entries h (fun a r s => Z a r s)

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularSixth
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sixth spherical moments for the directional derivative of normal curvature.
All moments are the explicit Folland specialization from `SphericalMoments`. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

/-- Contracting one fourth moment with a matrix. -/
theorem fourth_single_contraction (D : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    (∑ k, ∑ l, D k l * momentFour a b k l) =
      (delta a b * (∑ k, D k k) + D a b + D b a) / 24 := by
  have hm (k l : Fin 4) : D k l * momentFour a b k l =
      (D k l * delta a b * delta k l + D k l * delta a k * delta b l +
        D k l * delta a l * delta b k) / 24 := by
    unfold momentFour
    ring
  simp_rw [hm, ← Finset.sum_div, Finset.sum_add_distrib]
  congr 1
  simp [delta, mul_ite, ite_mul, Finset.mul_sum]

theorem momentFour_cycle (a b c d : Fin 4) :
    momentFour a b c d = momentFour a d b c := by
  unfold momentFour
  rw [delta_symm d c, delta_symm d b]
  ring

/-- Group the fifteen pairings by the partner of the first index. -/
theorem sixth_sum_recursion (C D : Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentSix a b i j k l) =
      (delta a b * (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l) +
        (∑ j, C a j * (∑ k, ∑ l, D k l * momentFour b j k l)) +
        (∑ i, C i a * (∑ k, ∑ l, D k l * momentFour b i k l)) +
        (∑ l, D a l * (∑ i, ∑ j, C i j * momentFour b l i j)) +
        (∑ k, D k a * (∑ i, ∑ j, C i j * momentFour b k i j))) / 8 := by
  have hm (i j k l : Fin 4) : C i j * D k l * momentSix a b i j k l =
      (delta a b * (C i j * D k l * momentFour i j k l) +
       C i j * D k l * delta a i * momentFour b j k l +
       C i j * D k l * delta a j * momentFour b i k l +
       C i j * D k l * delta a k * momentFour b l i j +
       C i j * D k l * delta a l * momentFour b k i j) / 8 := by
    unfold momentSix
    rw [momentFour_cycle b i j l, momentFour_cycle b i j k]
    ring
  have h0 : (∑ i, ∑ j, ∑ k, ∑ l,
      delta a b * (C i j * D k l * momentFour i j k l)) =
      delta a b * (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentFour i j k l) := by
    simp only [Finset.mul_sum]
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a i * momentFour b j k l) =
      ∑ j, C a j * (∑ k, ∑ l, D k l * momentFour b j k l) := by
    simp [delta, mul_ite, ite_mul, Finset.sum_ite_irrel, Finset.mul_sum, mul_assoc]
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a j * momentFour b i k l) =
      ∑ i, C i a * (∑ k, ∑ l, D k l * momentFour b i k l) := by
    simp [delta, mul_ite, ite_mul, Finset.sum_ite_irrel, Finset.mul_sum, mul_assoc]
  have hr (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
    calc
      _ = ∑ i, ∑ k, ∑ j, f i j k := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  have h3 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a k * momentFour b l i j) =
      ∑ l, D a l * (∑ i, ∑ j, C i j * momentFour b l i j) := by
    simp only [delta, mul_ite, ite_mul, mul_zero, mul_one, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true]
    rw [hr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h4 : (∑ i, ∑ j, ∑ k, ∑ l,
      C i j * D k l * delta a l * momentFour b k i j) =
      ∑ k, D k a * (∑ i, ∑ j, C i j * momentFour b k i j) := by
    simp only [delta, mul_ite, ite_mul, mul_zero, mul_one, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
    rw [hr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hm, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [h0, h1, h2, h3, h4]

theorem fourth_single_contraction_traceFree (D : Fin 4 → Fin 4 → ℝ)
    (hD : ∑ k, D k k = 0) (hDs : ∀ i j, D i j = D j i) (a b : Fin 4) :
    (∑ k, ∑ l, D k l * momentFour a b k l) = D a b / 12 := by
  rw [fourth_single_contraction, hD, hDs b a]
  ring

/-- A fourth-degree harmonic has no second-degree spherical moment. -/
theorem sixth_sum_traceFree (C D : Fin 4 → Fin 4 → ℝ)
    (hC : ∑ k, C k k = 0) (hD : ∑ k, D k k = 0)
    (hCs : ∀ i j, C i j = C j i) (hDs : ∀ i j, D i j = D j i)
    (a b : Fin 4) :
    (∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentSix a b i j k l) =
      delta a b * (∑ i, ∑ j, C i j * D i j) / 96 +
        ((∑ k, C a k * D k b) + (∑ k, D a k * C k b)) / 48 := by
  rw [sixth_sum_recursion, fourth_sum_formula, hC, hD]
  simp_rw [fourth_single_contraction_traceFree D hD hDs,
    fourth_single_contraction_traceFree C hC hCs]
  have hp : (∑ i, ∑ j, C i j * D j i) = ∑ i, ∑ j, C i j * D i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hDs j i]
  rw [hp]
  have h1 : (∑ j, C a j * (D b j / 12)) = (∑ j, C a j * D j b) / 12 := by
    simp_rw [hDs b, ← mul_div_assoc, ← Finset.sum_div]
  have h2 : (∑ i, C i a * (D b i / 12)) = (∑ i, C a i * D i b) / 12 := by
    simp_rw [← hCs a, hDs b, ← mul_div_assoc, ← Finset.sum_div]
  have h3 : (∑ l, D a l * (C b l / 12)) = (∑ l, D a l * C l b) / 12 := by
    simp_rw [hCs b, ← mul_div_assoc, ← Finset.sum_div]
  have h4 : (∑ k, D k a * (C b k / 12)) = (∑ k, D a k * C k b) / 12 := by
    simp_rw [← hDs a, hCs b, ← mul_div_assoc, ← Finset.sum_div]
  rw [h1, h2, h3, h4]
  ring

/-- The raw weighted quadratic product is exactly a sixth-moment contraction. -/
theorem integral_weighted_quadratic_mul (h : FollandMoments)
    (C D : Mat4) (a b : Fin 4) :
    (∫ q, q.val a * q.val b * (quadratic C q * quadratic D q) ∂sphereMeasure) =
      ∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l * momentSix a b i j k l := by
  have he : (fun q : Directions =>
      q.val a * q.val b * (quadratic C q * quadratic D q)) =
      fun q => ∑ i, ∑ j, ∑ k, ∑ l, C i j * D k l *
        (q.val a * q.val b * q.val i * q.val j * q.val k * q.val l) := by
    funext q
    have hp : quadratic C q * quadratic D q =
        ∑ i, ∑ j, ∑ k, ∑ l,
          C i j * D k l * (q.val i * q.val j * q.val k * q.val l) := by
      unfold quadratic
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hp]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_sum h _ (fun _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul, h.sixth]

/-- The useful matrix form of the sixth moment. -/
theorem integral_weighted_quadratic_mul_traceFree (h : FollandMoments)
    (C D : Mat4) (hC : C.trace = 0) (hD : D.trace = 0)
    (hCs : Cᵀ = C) (hDs : Dᵀ = D) (a b : Fin 4) :
    (∫ q, q.val a * q.val b * (quadratic C q * quadratic D q) ∂sphereMeasure) =
      delta a b * (∑ i, ∑ j, C i j * D i j) / 96 +
        (C * D + D * C) a b / 48 := by
  rw [integral_weighted_quadratic_mul h]
  have hc : ∑ k, C k k = 0 := hC
  have hd : ∑ k, D k k = 0 := hD
  have hcs (i j : Fin 4) : C i j = C j i :=
    (congrFun (congrFun hCs i) j).symm
  have hds (i j : Fin 4) : D i j = D j i :=
    (congrFun (congrFun hDs i) j).symm
  simpa only [Matrix.add_apply, Matrix.mul_apply] using!
    sixth_sum_traceFree C D hc hd hcs hds a b

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularDerivativeMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite Weyl blocks have zero mixed directional energy. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

def rotatedLinear (q : Directions) : Mat3 →ₗ[ℝ] Mat3 :=
  (LinearMap.mulRight ℝ (mixingMatrix q)ᵀ).comp (LinearMap.mulLeft ℝ (mixingMatrix q))

theorem directional_pairing (Z W : Gradient) (q : Directions) :
    pairing (directional Z q) (rotated (directional W q) q) =
      ∑ a, ∑ b, q.val a * q.val b * pairing (Z a) (rotated (W b) q) := by
  let B := angularPairingLinear.compl₂ (rotatedLinear q)
  change B (∑ a, q.val a • Z a) (∑ b, q.val b • W b) =
    ∑ a, ∑ b, q.val a * q.val b * B (Z a) (W b)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end

end PositiveEinsteinFour.Angular

end OAI
end


