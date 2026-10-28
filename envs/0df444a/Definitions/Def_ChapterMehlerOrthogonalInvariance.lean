-- Prove2me | Definitions.Def_ChapterMehlerOrthogonalInvariance
-- name    : ChapterMehlerOrthogonalInvariance
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T12:07:30.798626+00:00
-- url     : https://prove2.me/theorems/106b2989-053d-49a0-afae-2c34c1e1a37f
-- title:
--   The Lean 4 theorem `dotProduct_mulVec_orthogonal` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMehlerOrthogonalInvariance.lean`): generated def bundle for ChapterMehlerOrthogonalInvariance. See BookProof/ChapterMehlerOrthogonalInvariance.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMehlerOrthogonalInvariance.lean

import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Theorems.Thm_BookProof_ChapterSolovayCoordinates_tailSplitEquiv_map


/-!
# Coordinate-level orthogonal invariance of the Mehler (Gaussian) prior

`BookProof.ChapterSolovay` states the invariance of the Mehler tail prior under
finite orthogonal symmetries *at the measurable interface*: a transformation is
admitted when it is measure preserving.  That formulation is honest but weak —
it does not exhibit a single concrete orthogonal transformation.

This file supplies the missing concrete, coordinate-level content.  Working with
the explicit coordinate realization of `BookProof.ChapterSolovayCoordinates`
(the tail is the countable product of standard Gaussians), we prove:

* `charFun_stdGaussianEuclidean` — the characteristic function of the standard
  `k`-dimensional Gaussian is `t ↦ exp (-‖t‖²/2)`, which depends on `t` only
  through its norm;
* `stdGaussianEuclidean_map_isometry` — hence the standard `k`-dimensional
  Gaussian is invariant under **every** linear isometry of `ℝᵏ`, i.e. under the
  full orthogonal group `O(k)`;
* `gaussianHead_map_orthogonal` — the same statement in raw coordinates, for an
  orthogonal matrix `O` acting by `x ↦ O *ᵥ x`;
* `coordinateTailMeasure_map_headRotation` — the **headline**: the infinite
  Mehler coordinate prior is invariant under an orthogonal transformation acting
  on the first `k` coordinates and leaving the remaining coordinates fixed.  This
  is the concrete coordinate-level form of
  `BookProof.ChapterSolovay.mehler_invariant_under_finite_orthogonal`;
* `isFiniteOrthogonalTailSymmetry_headRotation` — consequently such a rotation is
  measure preserving, so it is an admissible finite orthogonal tail symmetry in
  the sense used by the abstract chapter.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace BookProof.ChapterMehlerOrthogonalInvariance

open BookProof.ChapterSolovayCoordinates

/-! ## 1. The standard Gaussian on Euclidean `k`-space -/

/-- The standard `k`-dimensional Gaussian measure, read on the Euclidean space
`EuclideanSpace ℝ (Fin k)` (the same product of standard Gaussians as
`gaussianHead k`, transported along the `ℓ²` labelling of the coordinates). -/
def stdGaussianEuclidean (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (gaussianHead k).map (WithLp.toLp 2)

instance stdGaussianEuclidean_isProbability (k : ℕ) :
    IsProbabilityMeasure (stdGaussianEuclidean k) := by
  rw [stdGaussianEuclidean]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The characteristic function transforms contravariantly under a linear
isometry of the underlying space. -/
theorem charFun_map_isometryEquiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) (L : E ≃ₗᵢ[ℝ] E) (t : E) :
    charFun (mu.map L) t = charFun mu (L.symm t) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  congr 2
  simpa using L.inner_map_map x (L.symm t)

/-- **The characteristic function of the standard `k`-dimensional Gaussian.**
It is `exp (-‖t‖²/2)`, a function of the norm of `t` alone — the analytic reason
for rotation invariance. -/
theorem charFun_stdGaussianEuclidean (k : ℕ) (t : EuclideanSpace ℝ (Fin k)) :
    charFun (stdGaussianEuclidean k) t = Complex.exp (-(‖t‖ ^ 2 : ℝ) / 2) := by
  rw [stdGaussianEuclidean, gaussianHead, charFun_pi]
  simp only [standardGaussian, charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  have h : ‖t‖ ^ 2 = ∑ i, (t i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [sq_abs]
  rw [h]
  push_cast
  simp [Finset.sum_div, neg_div]

/-- **Rotation invariance of the standard Gaussian.**  The standard
`k`-dimensional Gaussian measure is invariant under every linear isometry of
`ℝᵏ`, that is, under the whole orthogonal group `O(k)`. -/
theorem stdGaussianEuclidean_map_isometry (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (stdGaussianEuclidean k).map L = stdGaussianEuclidean k := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_isometryEquiv, charFun_stdGaussianEuclidean,
    charFun_stdGaussianEuclidean, L.symm.norm_map]

/-! ## 2. Orthogonal matrices as isometries -/

/-- An orthogonal matrix preserves the Euclidean dot product. -/
theorem dotProduct_mulVec_orthogonal {k : ℕ} {O : Matrix (Fin k) (Fin k) ℝ}
    (hO : Oᵀ * O = 1) (x y : Fin k → ℝ) :
    (O *ᵥ x) ⬝ᵥ (O *ᵥ y) = x ⬝ᵥ y := by
  have h : Oᵀ *ᵥ (O *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]

/-- The linear isometry of Euclidean `k`-space determined by an orthogonal
matrix. -/
def orthEquiv {k : ℕ} (O : Matrix (Fin k) (Fin k) ℝ) (hO : Oᵀ * O = 1) :
    EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := by
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  refine LinearEquiv.isometryOfInner
    { toFun := fun x => (WithLp.toLp 2 (O *ᵥ (WithLp.ofLp x)))
      invFun := fun y => (WithLp.toLp 2 (Oᵀ *ᵥ (WithLp.ofLp y)))
      map_add' := by intro x y; simp [Matrix.mulVec_add]
      map_smul' := by intro c x; simp [Matrix.mulVec_smul]
      left_inv := by intro x; simp [Matrix.mulVec_mulVec, hO]
      right_inv := by intro y; simp [Matrix.mulVec_mulVec, hO'] } ?_
  intro x y
  simpa [PiLp.inner_apply, dotProduct] using
    dotProduct_mulVec_orthogonal hO (WithLp.ofLp y) (WithLp.ofLp x)

@[simp] theorem orthEquiv_apply {k : ℕ} (O : Matrix (Fin k) (Fin k) ℝ) (hO : Oᵀ * O = 1)
    (x : EuclideanSpace ℝ (Fin k)) :
    orthEquiv O hO x = WithLp.toLp 2 (O *ᵥ (WithLp.ofLp x)) := rfl

/-- **Orthogonal invariance of the finite Gaussian head, in coordinates.**  For
an orthogonal matrix `O`, the finite product of standard Gaussians is invariant
under `x ↦ O *ᵥ x`. -/
theorem gaussianHead_map_orthogonal {k : ℕ} (O : Matrix (Fin k) (Fin k) ℝ)
    (hO : Oᵀ * O = 1) :
    (gaussianHead k).map (fun x => O *ᵥ x) = gaussianHead k := by
  refine (MeasurableEquiv.toLp 2 (Fin k → ℝ)).map_measurableEquiv_injective ?_
  have hmeas : Measurable fun x : Fin k → ℝ => O *ᵥ x := by fun_prop
  rw [MeasurableEquiv.coe_toLp, Measure.map_map (by fun_prop) hmeas]
  have hcomp : (WithLp.toLp 2) ∘ (fun x : Fin k → ℝ => O *ᵥ x)
      = (orthEquiv O hO) ∘ (WithLp.toLp 2) := by
    ext x i
    simp
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  exact stdGaussianEuclidean_map_isometry k (orthEquiv O hO)

/-! ## 3. The infinite Mehler prior under a finite-rank rotation -/

/-- Rotate the first `k` coordinates of an infinite sequence by an orthogonal
matrix, leaving all further coordinates untouched. -/
def headRotation (k : ℕ) (O : Matrix (Fin k) (Fin k) ℝ) :
    CoordinateTail → CoordinateTail :=
  fun x => (tailSplitEquiv k).symm (Prod.map (fun h => O *ᵥ h) id ((tailSplitEquiv k) x))

theorem measurable_headRotation (k : ℕ) (O : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (headRotation k O) := by
  unfold headRotation
  exact (tailSplitEquiv k).symm.measurable.comp
    (((by fun_prop : Measurable fun h : Fin k → ℝ => O *ᵥ h).comp measurable_fst).prodMk
      (measurable_id.comp measurable_snd) |>.comp (tailSplitEquiv k).measurable)

/-- **Headline (coordinate-level Mehler invariance).**  The infinite Mehler
coordinate prior — the countable product of standard Gaussians — is invariant
under a finite-rank orthogonal transformation: rotating the first `k`
coordinates by any orthogonal matrix leaves the law unchanged. -/
theorem coordinateTailMeasure_map_headRotation {k : ℕ} (O : Matrix (Fin k) (Fin k) ℝ)
    (hO : Oᵀ * O = 1) :
    coordinateTailMeasure.map (headRotation k O) = coordinateTailMeasure := by
  have hmeasO : Measurable fun h : Fin k → ℝ => O *ᵥ h := by fun_prop
  have hprod : Measurable (Prod.map (fun h : Fin k → ℝ => O *ᵥ h) (id : CoordinateTail → _)) :=
    (hmeasO.comp measurable_fst).prodMk (measurable_id.comp measurable_snd)
  have hab : Measurable ((tailSplitEquiv k).symm ∘ Prod.map (fun h : Fin k → ℝ => O *ᵥ h) id) :=
    (tailSplitEquiv k).symm.measurable.comp hprod
  unfold headRotation
  rw [← Function.comp_def, ← Function.comp_def, ← Function.comp_assoc,
    ← Measure.map_map hab (tailSplitEquiv k).measurable, tailSplitEquiv_map,
    ← Measure.map_map (tailSplitEquiv k).symm.measurable hprod,
    ← Measure.map_prod_map _ _ hmeasO measurable_id, gaussianHead_map_orthogonal O hO,
    Measure.map_id, ← tailSplitEquiv_map,
    Measure.map_map (tailSplitEquiv k).symm.measurable (tailSplitEquiv k).measurable]
  simp

/-- The finite-rank rotation is measure preserving for the Mehler coordinate
prior, i.e. it is an admissible finite orthogonal tail symmetry in the sense of
the abstract chapter. -/
theorem measurePreserving_headRotation {k : ℕ} (O : Matrix (Fin k) (Fin k) ℝ)
    (hO : Oᵀ * O = 1) :
    MeasurePreserving (headRotation k O) coordinateTailMeasure coordinateTailMeasure :=
  ⟨measurable_headRotation k O, coordinateTailMeasure_map_headRotation O hO⟩

end BookProof.ChapterMehlerOrthogonalInvariance


