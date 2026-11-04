-- Prove2me | Definitions.Def_QMCLeafB_EllipsoidVolume
-- name    : QMCLeafB_EllipsoidVolume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:00:47.909643+00:00
-- url     : https://prove2.me/theorems/5cbb4056-be68-4f9a-a296-6c92f56e1a2d
-- title:
--   QMCLeafB EllipsoidVolume
-- statement:
--   # `brick-ellipsoid-volume`: the measure of a Gram-parametrised ellipsoid,
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# `brick-ellipsoid-volume`: the measure of a Gram-parametrised ellipsoid,
# and why the shallow-cut loop must stop

The leaf-B engine searches a `d`-dimensional (matrix) space with a GLS shallow-cut ellipsoid.
The geometry of one step is `brick-ellipsoid-step`'s business (determinant lemma, containment,
log-det drop) and the contraction-to-count bookkeeping is `LeafB_IterBound`'s.  Two links are in
neither, and they are what this file supplies.

**Link 1: `det` means *volume*.**  For an invertible `B` the ellipsoid
`E(B,c) = {c + B z | z ⬝ z ≤ 1}` (i.e. `{x | (x-c)ᵀ Q⁻¹ (x-c) ≤ 1}` with shape matrix
`Q = B Bᵀ`; see `mem_ellipsoid_iff`) has Lebesgue measure `|det B| · κ`, where `κ` is the
measure of the Euclidean unit ball (`volume_ellipsoid`, `det_shape`).  Hence `log vol E` is
`½·log det Q + log κ`: the determinant potential that `brick-ellipsoid-step` decreases *is* a
log-volume, and a step shrinking `det Q` by `θ` shrinks the volume by `θ`
(`volume_ellipsoid_le_smul`, `volume_ellipsoid_exp_shrink`, `volume_ellipsoid_lt_of_det_lt`).

**Link 2: volume makes the loop terminate.**  If an ellipsoid contains a Euclidean ball of
radius `r > 0`, then `r ^ (2d) ≤ det Q` (`pow_two_mul_le_det_shape`); that is the floor of the
potential, because the containment half of the shallow-cut step keeps the feasible ball inside
every iterate.  A per-step contraction `det Q_{k+1} ≤ (1 - 1/(4d))·det Q_k` therefore cannot be
sustained (`potential_below_floor`, `no_infinite_run`), and since the initial ellipsoid sits
inside a ball of radius `R` (`det_shape_le_of_subset_eucBall`) the count is explicit:
after `(K·2d + 1)·4d` steps the potential is already below its floor whenever `2^K ≥ R/r`, i.e.
**`O(d² log(R/r))` iterations**, with every constant explicit (`explicit_iteration_count`).

The Euclidean ball is written as `{z | z ⬝ᵥ z ≤ r ^ 2}` (`eucBall`) rather than through a norm
instance, so that the statements are unambiguously about the Euclidean ellipsoid; the only
analytic inputs are the Haar-measure Jacobian formula `μ (f '' s) = |det f| · μ s` and
translation invariance, both from Mathlib.  The contraction estimate `(1 - 1/m)^m ≤ 1/2` is
Bernoulli's inequality, so no logarithms or exponentials are needed for the count itself.
-/

open MeasureTheory Matrix
open scoped BigOperators ENNReal

namespace QMCLeafB.EllipsoidVolume

variable {n : ℕ}

/-! ## 1. The Euclidean ball as a dot-product set -/

/-- The closed Euclidean ball of radius `r`, written with the dot product so that no norm
instance is involved: this set *is* the Euclidean ball `{z | ‖z‖₂ ≤ r}`. -/
def eucBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {z | z ⬝ᵥ z ≤ r ^ 2}

/-- A translated Euclidean ball. -/
def eucBallAt (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) := (fun x => c + x) '' eucBall n r

theorem dotProduct_self_eq_sum_sq (z : Fin n → ℝ) : z ⬝ᵥ z = ∑ i, (z i) ^ 2 := by
  simp only [dotProduct, sq]

theorem smul_dot_smul (r : ℝ) (z : Fin n → ℝ) : (r • z) ⬝ᵥ (r • z) = r ^ 2 * (z ⬝ᵥ z) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `κ n`: the Lebesgue measure of the Euclidean unit ball of `Fin n → ℝ`. -/
noncomputable def kappa (n : ℕ) : ℝ≥0∞ := volume (eucBall n 1)

/-- The sup-norm ball of radius `1/(n+1)` sits inside the Euclidean unit ball. -/
theorem closedBall_subset_eucBall (n : ℕ) :
    Metric.closedBall (0 : Fin n → ℝ) (1 / ((n : ℝ) + 1)) ⊆ eucBall n 1 := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have hcoord : ∀ i, |z i| ≤ 1 / ((n : ℝ) + 1) := fun i => by
    have h1 : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at h1
    exact h1.trans hz
  simp only [eucBall, Set.mem_setOf_eq, one_pow]
  rw [dotProduct_self_eq_sum_sq]
  have hterm : ∀ i : Fin n, (z i) ^ 2 ≤ (1 / ((n : ℝ) + 1)) ^ 2 := by
    intro i
    nlinarith [hcoord i, abs_nonneg (z i), sq_abs (z i)]
  calc ∑ i, (z i) ^ 2 ≤ ∑ _i : Fin n, (1 / ((n : ℝ) + 1)) ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 1 := by
        rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
        nlinarith

theorem kappa_ne_zero (n : ℕ) : kappa n ≠ 0 := by
  have hpos : 0 < volume (Metric.ball (0 : Fin n → ℝ) (1 / ((n : ℝ) + 1))) := by
    apply MeasureTheory.Measure.measure_pos_of_nonempty_interior
    exact ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.ball_mem_nhds 0 (by positivity))⟩
  refine ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_))
  exact Metric.ball_subset_closedBall.trans (closedBall_subset_eucBall n)

/-- The Euclidean unit ball sits inside the sup-norm cube of radius `1` (so it is bounded). -/
theorem eucBall_subset_pi_Icc (n : ℕ) :
    eucBall n 1 ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
  intro z hz
  simp only [eucBall, Set.mem_setOf_eq, one_pow] at hz
  rw [dotProduct_self_eq_sum_sq] at hz
  rw [Set.mem_pi]
  intro i _
  have hsingle : (z i) ^ 2 ≤ ∑ j, (z j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (z j) ^ 2) (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have habs : |z i| ≤ 1 := by nlinarith [sq_abs (z i), abs_nonneg (z i), hsingle]
  exact abs_le.mp habs

theorem kappa_ne_top (n : ℕ) : kappa n ≠ ⊤ := by
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine ne_top_of_le_ne_top hcomp.measure_lt_top.ne (measure_mono (eucBall_subset_pi_Icc n))

theorem kappa_pos (n : ℕ) : 0 < kappa n := pos_iff_ne_zero.mpr (kappa_ne_zero n)

/-! ## 2. Linear images, translations and scalings -/

/-- Lebesgue measure of a linear image: the Jacobian is the determinant. -/
theorem volume_image_toLin' (B : Matrix (Fin n) (Fin n) ℝ) (s : Set (Fin n → ℝ)) :
    volume (⇑(Matrix.toLin' B) '' s) = ENNReal.ofReal |B.det| * volume s := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

/-- Lebesgue measure is translation invariant, in image form. -/
theorem volume_translate_image (v : Fin n → ℝ) (s : Set (Fin n → ℝ)) :
    volume ((fun x => v + x) '' s) = volume s := by
  have himg : (fun x => v + x) '' s = (fun y => y - v) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y - v, by simpa using hy, by abel⟩
  rw [himg]
  have := MeasureTheory.measure_preimage_add (volume : Measure (Fin n → ℝ)) (-v) s
  simpa [sub_eq_add_neg] using this

/-- The Euclidean ball of radius `r` is the unit ball scaled by `r`. -/
theorem eucBall_eq_smul (r : ℝ) (hr : 0 < r) :
    eucBall n r = ⇑(Matrix.toLin' (r • (1 : Matrix (Fin n) (Fin n) ℝ))) '' eucBall n 1 := by
  ext z
  simp only [eucBall, Set.mem_setOf_eq, Set.mem_image, Matrix.toLin'_apply, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  constructor
  · intro hz
    refine ⟨r⁻¹ • z, ?_, ?_⟩
    · rw [smul_dot_smul, inv_pow]
      have h2 : (0 : ℝ) < (r ^ 2)⁻¹ := by positivity
      have h3 : (r ^ 2)⁻¹ * r ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
      calc (r ^ 2)⁻¹ * (z ⬝ᵥ z) ≤ (r ^ 2)⁻¹ * r ^ 2 :=
            mul_le_mul_of_nonneg_left hz (le_of_lt h2)
        _ = 1 ^ 2 := by rw [h3]; norm_num
    · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro ⟨w, hw, rfl⟩
    rw [smul_dot_smul]
    calc r ^ 2 * (w ⬝ᵥ w) ≤ r ^ 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa using hw
      _ = r ^ 2 := mul_one _

/-- The determinant of the scaling matrix `r • 1` is `r ^ n`. -/
theorem det_smul_one (r : ℝ) : (r • (1 : Matrix (Fin n) (Fin n) ℝ)).det = r ^ n := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

/-- **The measure of a Euclidean ball.**  `vol B(c,r) = r ^ n · κ n`. -/
theorem volume_eucBallAt (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (eucBallAt c r) = ENNReal.ofReal (r ^ n) * kappa n := by
  rw [eucBallAt, eucBall_eq_smul r hr, volume_translate_image,
    volume_image_toLin' (r • (1 : Matrix (Fin n) (Fin n) ℝ)) _, det_smul_one,
    abs_of_nonneg (pow_nonneg hr.le n), kappa]

/-! ## 3. The ellipsoid of a Gram factor -/

/-- The ellipsoid with Gram factor `B` and centre `c`: the image of the Euclidean unit ball
under `z ↦ c + B z`.  Its shape matrix is `Q = B Bᵀ = shape B` (`mem_ellipsoid_iff`). -/
noncomputable def ellipsoid (B : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun x => c + x) '' (⇑(Matrix.toLin' B) '' eucBall n 1)

/-- The shape matrix of the ellipsoid `E(B,c)`: `Q = B Bᵀ`, so that
`E(B,c) = {x | (x - c) ⬝ᵥ (Q⁻¹ *ᵥ (x - c)) ≤ 1}` (`mem_ellipsoid_iff`). -/
noncomputable def shape (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := B * Bᵀ

theorem det_shape (B : Matrix (Fin n) (Fin n) ℝ) : (shape B).det = B.det * B.det := by
  rw [shape, Matrix.det_mul, Matrix.det_transpose]

theorem det_transpose_mul_eq_det_shape (B : Matrix (Fin n) (Fin n) ℝ) :
    (Bᵀ * B).det = (shape B).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, det_shape]

/-- **The volume of an ellipsoid.**  `vol E(B,c) = |det B| · κ n`. -/
theorem volume_ellipsoid (B : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    volume (ellipsoid B c) = ENNReal.ofReal |B.det| * kappa n := by
  simp only [ellipsoid, volume_translate_image, volume_image_toLin', kappa]

/-- The volume in terms of the shape matrix: `vol E(B,c) = √(det Q) · κ n`. -/
theorem volume_ellipsoid_shape (B : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    volume (ellipsoid B c) = ENNReal.ofReal (Real.sqrt (shape B).det) * kappa n := by
  rw [volume_ellipsoid, det_shape, Real.sqrt_mul_self_eq_abs]

/-! ## 4. This really is the ellipsoid of its shape matrix -/

/-- The quadratic form of the ellipsoid, computed on the Gram factor: for `Q = B Bᵀ`,
`(B z) ⬝ᵥ (Q⁻¹ *ᵥ (B z)) = z ⬝ᵥ z`. -/
theorem dot_quadform_eq (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (z : Fin n → ℝ) :
    (B *ᵥ z) ⬝ᵥ ((shape B)⁻¹ *ᵥ (B *ᵥ z)) = z ⬝ᵥ z := by
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hunitT : IsUnit (Bᵀ).det := by rwa [Matrix.det_transpose]
  have hQ : (shape B)⁻¹ = (Bᵀ)⁻¹ * B⁻¹ := by rw [shape, Matrix.mul_inv_rev]
  have hdot : ∀ (v w : Fin n → ℝ), (B *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Bᵀ *ᵥ w) := by
    intro v w
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]
  have hmat : (shape B)⁻¹ * B = (Bᵀ)⁻¹ := by
    rw [hQ, Matrix.mul_assoc, Matrix.nonsing_inv_mul B hunit, Matrix.mul_one]
  have hmat2 : Bᵀ * (Bᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv (Bᵀ) hunitT
  calc (B *ᵥ z) ⬝ᵥ ((shape B)⁻¹ *ᵥ (B *ᵥ z))
      = (B *ᵥ z) ⬝ᵥ (((shape B)⁻¹ * B) *ᵥ z) := by rw [Matrix.mulVec_mulVec]
    _ = (B *ᵥ z) ⬝ᵥ ((Bᵀ)⁻¹ *ᵥ z) := by rw [hmat]
    _ = z ⬝ᵥ (Bᵀ *ᵥ ((Bᵀ)⁻¹ *ᵥ z)) := hdot z _
    _ = z ⬝ᵥ ((Bᵀ * (Bᵀ)⁻¹) *ᵥ z) := by rw [Matrix.mulVec_mulVec]
    _ = z ⬝ᵥ z := by rw [hmat2, Matrix.one_mulVec]

/-- **The ellipsoid as a quadratic-form level set.**  With `Q = B Bᵀ`, membership in `E(B,c)` is
exactly `(x - c) ⬝ᵥ (Q⁻¹ *ᵥ (x - c)) ≤ 1`: the set is the classical ellipsoid of `Q⁻¹`. -/
theorem mem_ellipsoid_iff (B : Matrix (Fin n) (Fin n) ℝ) (c x : Fin n → ℝ) (hB : B.det ≠ 0) :
    x ∈ ellipsoid B c ↔ (x - c) ⬝ᵥ ((shape B)⁻¹ *ᵥ (x - c)) ≤ 1 := by
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    have hsub : c + ⇑(Matrix.toLin' B) z - c = B *ᵥ z := by
      rw [add_sub_cancel_left, Matrix.toLin'_apply]
    rw [hsub, dot_quadform_eq B hB]
    simpa [eucBall] using hz
  · intro hx
    refine ⟨B *ᵥ ((B⁻¹) *ᵥ (x - c)), ⟨(B⁻¹) *ᵥ (x - c), ?_, ?_⟩, ?_⟩
    · have hstep : B *ᵥ ((B⁻¹) *ᵥ (x - c)) = x - c := by
        calc B *ᵥ ((B⁻¹) *ᵥ (x - c)) = (B * B⁻¹) *ᵥ (x - c) := by rw [Matrix.mulVec_mulVec]
          _ = x - c := by rw [Matrix.mul_nonsing_inv B hunit, Matrix.one_mulVec]
      simp only [eucBall, Set.mem_setOf_eq, one_pow]
      have hzz : B⁻¹ *ᵥ (x - c) ⬝ᵥ (B⁻¹ *ᵥ (x - c))
          = (x - c) ⬝ᵥ ((shape B)⁻¹ *ᵥ (x - c)) := by
        rw [← dot_quadform_eq B hB (B⁻¹ *ᵥ (x - c)), hstep]
      rw [hzz]
      exact hx
    · rw [Matrix.toLin'_apply]
    · calc c + B *ᵥ ((B⁻¹) *ᵥ (x - c)) = c + (x - c) := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hunit, Matrix.one_mulVec]
        _ = x := by abel

/-! ## 5. The determinant floor: a contained ball bounds `det Q` from below -/

/-- **A contained ball is a determinant floor.**  If the ellipsoid `E(B,c')` contains a
Euclidean ball of radius `r > 0`, then `r ^ n ≤ |det B|`, i.e. `r ^ (2n) ≤ det Q` for the shape
matrix `Q = B Bᵀ` (`pow_two_mul_le_det_shape`).  This is the floor of the potential
`log det Q`, and it is what makes the shallow-cut loop stop. -/
theorem le_abs_det_of_eucBall_subset (B : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) (hsub : eucBallAt c r ⊆ ellipsoid B c') :
    r ^ n ≤ |B.det| := by
  have hle : volume (eucBallAt c r) ≤ volume (ellipsoid B c') := measure_mono hsub
  rw [volume_eucBallAt c hr, volume_ellipsoid B c'] at hle
  have hcancel : ENNReal.ofReal (r ^ n) ≤ ENNReal.ofReal |B.det| :=
    (ENNReal.mul_le_mul_iff_left (kappa_ne_zero n) (kappa_ne_top n)).mp hle
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg B.det)).mp hcancel

/-- The shape-matrix form of the floor: `r ^ (2n) ≤ det Q`. -/
theorem pow_two_mul_le_det_shape (B : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) (hsub : eucBallAt c r ⊆ ellipsoid B c') :
    r ^ (2 * n) ≤ (shape B).det := by
  have h := le_abs_det_of_eucBall_subset B c c' hr hsub
  have h2 : (r ^ n) ^ 2 ≤ |B.det| ^ 2 := pow_le_pow_left₀ (pow_nonneg hr.le n) h 2
  rw [det_shape, Nat.mul_comm 2 n, pow_mul]
  simpa [sq_abs, sq] using h2

/-! ## 6. Geometric contraction of a positive potential -/

/-- A geometrically contracting nonnegative potential is bounded by its geometric series. -/
theorem potential_le_pow_mul (Φ : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ k, Φ (k + 1) ≤ c * Φ k) (h0 : 0 ≤ Φ 0) :
    ∀ k, Φ k ≤ c ^ k * Φ 0 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      calc Φ (n + 1) ≤ c * Φ n := hstep n
        _ ≤ c * (c ^ n * Φ 0) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (n + 1) * Φ 0 := by ring

/-- **Bernoulli count for the shallow-cut factor.**  `(1 - 1/(4d))^(4d) ≤ 1/2` for `d ≥ 1`:
the per-step determinant factor of the shallow-cut step halves the potential every `4d` steps. -/
theorem one_sub_inv_pow_le_half (d : ℕ) (hd : 1 ≤ d) :
    (1 - 1 / ((4 * d : ℕ) : ℝ)) ^ (4 * d) ≤ 1 / 2 := by
  have hm1 : (0 : ℝ) < ((4 * d - 1 : ℕ) : ℝ) := by
    have : 0 < 4 * d - 1 := by omega
    exact_mod_cast this
  have hcast : ((4 * d - 1 : ℕ) : ℝ) + 1 = ((4 * d : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 4 * d)]
    ring
  have hbern : 1 + ((4 * d : ℕ) : ℝ) * (1 / ((4 * d - 1 : ℕ) : ℝ)) ≤
      (1 + 1 / ((4 * d - 1 : ℕ) : ℝ)) ^ (4 * d) := by
    have hpos : (0 : ℝ) ≤ 1 / ((4 * d - 1 : ℕ) : ℝ) := by positivity
    simpa using one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / ((4 * d - 1 : ℕ) : ℝ) by linarith)
      (4 * d)
  have hgeom : 1 + 1 / ((4 * d - 1 : ℕ) : ℝ) =
      ((4 * d : ℕ) : ℝ) / ((4 * d - 1 : ℕ) : ℝ) := by
    rw [← hcast]
    field_simp
  rw [hgeom] at hbern
  have hmdiv : (1 : ℝ) ≤ ((4 * d : ℕ) : ℝ) * (1 / ((4 * d - 1 : ℕ) : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hm1, ← hcast]
    linarith
  have hratio : (2 : ℝ) ≤ (((4 * d : ℕ) : ℝ) / ((4 * d - 1 : ℕ) : ℝ)) ^ (4 * d) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt (pow_pos hm1 (4 * d)))
  have hcancel : (((4 * d : ℕ) : ℝ) / ((4 * d - 1 : ℕ) : ℝ)) ^ (4 * d) *
      (((4 * d - 1 : ℕ) : ℝ)) ^ (4 * d) = (((4 * d : ℕ) : ℝ)) ^ (4 * d) := by
    rw [div_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hm1))
  rw [hcancel] at hmul
  have hkey : (1 - 1 / ((4 * d : ℕ) : ℝ)) =
      ((4 * d - 1 : ℕ) : ℝ) / ((4 * d : ℕ) : ℝ) := by
    field_simp
    push_cast [Nat.cast_sub (by omega : 1 ≤ 4 * d)]
    ring
  rw [hkey, div_pow, div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < ((4 * d : ℕ) : ℝ)) (4 * d))]
  linarith

/-- **The potential drops below any prescribed floor.**  A potential that contracts by
`1 - 1/(4d)` per step falls below `r^(2d)` within `K·(4d)` steps, once `2^K` clears the ratio
`Φ 0 / r^(2d)`. -/
theorem potential_below_floor (Φ : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (_hr : 0 < r)
    (hpos : ∀ k, 0 < Φ k)
    (hdec : ∀ k, Φ (k + 1) ≤ (1 - 1 / ((4 * d : ℕ) : ℝ)) * Φ k)
    {K : ℕ} (hK : Φ 0 < r ^ (2 * d) * 2 ^ K) :
    Φ (K * (4 * d)) < r ^ (2 * d) := by
  have hc0 : (0 : ℝ) ≤ 1 - 1 / ((4 * d : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 4 * d := by omega
      exact_mod_cast this
    have h2 : 1 / ((4 * d : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h1
    linarith
  have hle := potential_le_pow_mul Φ _ hc0 hdec (le_of_lt (hpos 0)) (K * (4 * d))
  rw [show (1 - 1 / ((4 * d : ℕ) : ℝ)) ^ (K * (4 * d)) =
      ((1 - 1 / ((4 * d : ℕ) : ℝ)) ^ (4 * d)) ^ K by
    rw [Nat.mul_comm K (4 * d), pow_mul]] at hle
  have hbase : (0 : ℝ) ≤ (1 - 1 / ((4 * d : ℕ) : ℝ)) ^ (4 * d) := pow_nonneg hc0 (4 * d)
  have hhalf : ((1 - 1 / ((4 * d : ℕ) : ℝ)) ^ (4 * d)) ^ K ≤ (1 / 2 : ℝ) ^ K :=
    pow_le_pow_left₀ hbase (one_sub_inv_pow_le_half d hd) K
  have hstep2 : ((1 - 1 / ((4 * d : ℕ) : ℝ)) ^ (4 * d)) ^ K * Φ 0 ≤
      (1 / 2 : ℝ) ^ K * Φ 0 :=
    mul_le_mul_of_nonneg_right hhalf (le_of_lt (hpos 0))
  have hfinal : (1 / 2 : ℝ) ^ K * Φ 0 < r ^ (2 * d) := by
    have h1 : (1 / 2 : ℝ) ^ K * (2 : ℝ) ^ K = 1 := by
      rw [← mul_pow]
      norm_num
    have hlt := mul_lt_mul_of_pos_left hK (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ K)
    calc (1 / 2 : ℝ) ^ K * Φ 0 < (1 / 2 : ℝ) ^ K * (r ^ (2 * d) * 2 ^ K) := hlt
      _ = r ^ (2 * d) * ((1 / 2 : ℝ) ^ K * 2 ^ K) := by ring
      _ = r ^ (2 * d) := by rw [h1, mul_one]
  linarith

/-- **The potential reaches the floor in bounded time.**  No knowledge of `K` is needed: an
integer `K` with `2^K > Φ 0 / r^(2d)` exists (Archimedean), and then `Φ` is already below the
floor at time `K·(4d)`. -/
theorem exists_potential_below_floor (Φ : ℕ → ℝ) (d : ℕ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ k, 0 < Φ k)
    (hdec : ∀ k, Φ (k + 1) ≤ (1 - 1 / ((4 * d : ℕ) : ℝ)) * Φ k) :
    ∃ K : ℕ, Φ (K * (4 * d)) < r ^ (2 * d) := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (Φ 0 / r ^ (2 * d)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, potential_below_floor Φ d hd hr hpos hdec ?_⟩
  rw [div_lt_iff₀ (pow_pos hr (2 * d))] at hK
  linarith

/-! ## 7. The loop terminates -/

/-- **Termination of the shallow-cut loop.**  Let `E_k = E(B_k, c_k)` be the shallow-cut iterates
in dimension `d ≥ 1`, each containing the fixed Euclidean ball of radius `r > 0`
(`no_infinite_run` records that this is the containment half of one step), and let each step
shrink the potential by the standard shallow-cut factor
`det Q_{k+1} ≤ (1 - 1/(4d))·det Q_k`, `Q_k = shape (B k)`.  Then after `K·(4d)` steps — with
`K` any integer such that `2^K` clears `det Q_0 / r^(2d)` — the potential is *below* the floor
that containment forces, so no such run exists. -/
theorem potential_below_floor_of_iterates (d : ℕ) (hd : 1 ≤ d)
    (B : ℕ → Matrix (Fin d) (Fin d) ℝ) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ k, 0 < (shape (B k)).det)
    (hdec : ∀ k, (shape (B (k + 1))).det ≤
      (1 - 1 / ((4 * d : ℕ) : ℝ)) * (shape (B k)).det)
    {K : ℕ} (hK : (shape (B 0)).det < r ^ (2 * d) * 2 ^ K) :
    (shape (B (K * (4 * d)))).det < r ^ (2 * d) :=
  potential_below_floor (fun k => (shape (B k)).det) d hd hr hpos hdec hK

/-- **No run of `K·(4d)` steps keeps the feasible ball inside the ellipsoid.**  A shallow-cut
loop whose iterates all contain the ball of radius `r` around `c₀` must stop before `K·(4d)`
steps, with `2^K` clearing `det Q_0 / r^(2d)`. -/
theorem no_infinite_run (d : ℕ) (hd : 1 ≤ d)
    (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (c c₀ : ℕ → Fin d → ℝ) {r : ℝ} (hr : 0 < r)
    (hsub : ∀ k, eucBallAt (c₀ k) r ⊆ ellipsoid (B k) (c k))
    (hpos : ∀ k, 0 < (shape (B k)).det)
    (hdec : ∀ k, (shape (B (k + 1))).det ≤
      (1 - 1 / ((4 * d : ℕ) : ℝ)) * (shape (B k)).det)
    {K : ℕ} (hK : (shape (B 0)).det < r ^ (2 * d) * 2 ^ K) :
    False := by
  have hfloor : ∀ k, r ^ (2 * d) ≤ (shape (B k)).det := fun k =>
    pow_two_mul_le_det_shape (B k) (c₀ k) (c k) hr (hsub k)
  have hbelow := potential_below_floor_of_iterates d hd B hr hpos hdec hK
  linarith [hfloor (K * (4 * d))]

/-! ## 8. Volume shrink -/

/-- **One step shrinks the volume by the determinant ratio.**  If the Gram factor of the next
iterate is smaller in determinant by a factor `θ ≥ 0`, the ellipsoid's volume is smaller by the
same factor. -/
theorem volume_ellipsoid_le_smul (B B' : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ) {θ : ℝ}
    (_hθ : 0 ≤ θ) (h : |B'.det| ≤ |B.det| * θ) :
    volume (ellipsoid B' c') ≤ ENNReal.ofReal θ * volume (ellipsoid B c) := by
  rw [volume_ellipsoid B' c', volume_ellipsoid B c]
  have h1 : ENNReal.ofReal |B'.det| ≤ ENNReal.ofReal (|B.det| * θ) := ENNReal.ofReal_le_ofReal h
  calc ENNReal.ofReal |B'.det| * kappa n
      ≤ ENNReal.ofReal (|B.det| * θ) * kappa n := by gcongr
    _ = (ENNReal.ofReal |B.det| * ENNReal.ofReal θ) * kappa n := by
        rw [ENNReal.ofReal_mul (abs_nonneg B.det)]
    _ = ENNReal.ofReal θ * (ENNReal.ofReal |B.det| * kappa n) := by ring

/-- **Volume decrease `e^{-1/n}` per step.**  A log-det estimate `log det Q' ≤ log det Q - 1/n`
is exactly `|det B'| ≤ |det B|·e^{-1/n}`, and then the ellipsoid's measure shrinks by the same
factor. -/
theorem volume_ellipsoid_exp_shrink (B B' : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ)
    (h : |B'.det| ≤ |B.det| * Real.exp (-(1 / (n : ℝ)))) :
    volume (ellipsoid B' c') ≤ ENNReal.ofReal (Real.exp (-(1 / (n : ℝ)))) *
      volume (ellipsoid B c) :=
  volume_ellipsoid_le_smul B B' c c' (le_of_lt (Real.exp_pos _)) h

/-- **A strict determinant drop is a strict volume drop.**  The ellipsoid is a faithful model of
the potential. -/
theorem volume_ellipsoid_lt_of_det_lt (B B' : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ)
    (h : |B'.det| < |B.det|) :
    volume (ellipsoid B' c') < volume (ellipsoid B c) := by
  rw [volume_ellipsoid B' c', volume_ellipsoid B c]
  have hpos : (0 : ℝ) < |B.det| := lt_of_le_of_lt (abs_nonneg B'.det) h
  have h1 : ENNReal.ofReal |B'.det| < ENNReal.ofReal |B.det| :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).mpr h
  exact (ENNReal.mul_lt_mul_iff_left (kappa_ne_zero n) (kappa_ne_top n)).mpr h1

/-! ## 9. The covering radius and the explicit `O(d² log(R/r))` count -/

/-- **Contained in a ball: a determinant ceiling.**  If the ellipsoid `E(B,c)` sits inside a
Euclidean ball of radius `R`, then `|det B| ≤ R ^ n`.  This turns the covering radius of the
*initial* ellipsoid into the starting potential. -/
theorem abs_det_le_of_ellipsoid_subset_eucBall (B : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ)
    {R : ℝ} (hR : 0 < R) (hsub : ellipsoid B c ⊆ eucBallAt c' R) : |B.det| ≤ R ^ n := by
  have hle : volume (ellipsoid B c) ≤ volume (eucBallAt c' R) := measure_mono hsub
  rw [volume_ellipsoid B c, volume_eucBallAt c' hR] at hle
  have hcancel : ENNReal.ofReal |B.det| ≤ ENNReal.ofReal (R ^ n) :=
    (ENNReal.mul_le_mul_iff_left (kappa_ne_zero n) (kappa_ne_top n)).mp hle
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR.le n)).mp hcancel

/-- The shape-matrix form of the ceiling: a contained-in-`R` ellipsoid has `det Q ≤ R^(2n)`. -/
theorem det_shape_le_of_subset_eucBall (B : Matrix (Fin n) (Fin n) ℝ) (c c' : Fin n → ℝ)
    {R : ℝ} (hR : 0 < R) (hsub : ellipsoid B c ⊆ eucBallAt c' R) :
    (shape B).det ≤ R ^ (2 * n) := by
  have h := abs_det_le_of_ellipsoid_subset_eucBall B c c' hR hsub
  have h2 : |B.det| ^ 2 ≤ (R ^ n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [det_shape, Nat.mul_comm 2 n, pow_mul]
  simpa [sq_abs, sq] using h2

/-- **The explicit GLS iteration count.**  In dimension `d ≥ 1`, suppose the initial ellipsoid
`E(B₀,c₀)` is contained in a Euclidean ball of radius `R` (the covering radius), the potential
contracts by `1 - 1/(4d)` per step, and `2^K ≥ R/r`.  Then after `(K·2d + 1)·(4d) = O(d²·K)`
steps the potential is below the floor `r^(2d)`; together with `no_infinite_run` this says that
**the shallow-cut loop must stop within `O(d² log(R/r))` iterations**. -/
theorem explicit_iteration_count (d : ℕ) (hd : 1 ≤ d)
    (B : ℕ → Matrix (Fin d) (Fin d) ℝ) (c c₀ : ℕ → Fin d → ℝ) {r R : ℝ} (hr : 0 < r)
    (hR : 0 < R) (hcover : ellipsoid (B 0) (c 0) ⊆ eucBallAt (c₀ 0) R)
    (hpos : ∀ k, 0 < (shape (B k)).det)
    (hdec : ∀ k, (shape (B (k + 1))).det ≤
      (1 - 1 / ((4 * d : ℕ) : ℝ)) * (shape (B k)).det)
    {K : ℕ} (hK : R / r ≤ 2 ^ K) :
    (shape (B ((K * (2 * d) + 1) * (4 * d)))).det < r ^ (2 * d) := by
  have hceil : (shape (B 0)).det ≤ R ^ (2 * d) :=
    det_shape_le_of_subset_eucBall (B 0) (c 0) (c₀ 0) hR hcover
  have hRm : R ^ (2 * d) = r ^ (2 * d) * (R / r) ^ (2 * d) := by
    rw [div_pow]
    field_simp
  have hmono : (R / r) ^ (2 * d) ≤ ((2 : ℝ) ^ K) ^ (2 * d) :=
    pow_le_pow_left₀ (by positivity) hK (2 * d)
  have hpow : ((2 : ℝ) ^ K) ^ (2 * d) = (2 : ℝ) ^ (K * (2 * d)) := by
    rw [← pow_mul]
  have hratio : R ^ (2 * d) ≤ r ^ (2 * d) * (2 : ℝ) ^ (K * (2 * d)) := by
    rw [hRm]
    exact mul_le_mul_of_nonneg_left (hmono.trans_eq hpow) (pow_nonneg hr.le _)
  have hstrict : r ^ (2 * d) * (2 : ℝ) ^ (K * (2 * d)) <
      r ^ (2 * d) * (2 : ℝ) ^ (K * (2 * d) + 1) := by
    refine mul_lt_mul_of_pos_left ?_ (pow_pos hr _)
    rw [pow_succ]
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (K * (2 * d)) := by positivity
    linarith
  exact potential_below_floor_of_iterates d hd B hr hpos hdec
    (lt_of_le_of_lt (hceil.trans hratio) hstrict)


/-! ## 10. Sanity: the unit Gram factor gives the unit ball -/

theorem ellipsoid_one (c : Fin n → ℝ) :
    ellipsoid (1 : Matrix (Fin n) (Fin n) ℝ) c = eucBallAt c 1 := by
  ext x
  simp [ellipsoid, eucBallAt, eucBall, Matrix.toLin'_one]

theorem volume_ellipsoid_one (c : Fin n → ℝ) :
    volume (ellipsoid (1 : Matrix (Fin n) (Fin n) ℝ) c) = kappa n := by
  rw [volume_ellipsoid, Matrix.det_one, abs_one, ENNReal.ofReal_one, one_mul]

/-! ## 11. Axiom audit -/

#print axioms QMCLeafB.EllipsoidVolume.volume_ellipsoid
#print axioms QMCLeafB.EllipsoidVolume.volume_ellipsoid_shape
#print axioms QMCLeafB.EllipsoidVolume.volume_eucBallAt
#print axioms QMCLeafB.EllipsoidVolume.mem_ellipsoid_iff
#print axioms QMCLeafB.EllipsoidVolume.le_abs_det_of_eucBall_subset
#print axioms QMCLeafB.EllipsoidVolume.pow_two_mul_le_det_shape
#print axioms QMCLeafB.EllipsoidVolume.one_sub_inv_pow_le_half
#print axioms QMCLeafB.EllipsoidVolume.potential_below_floor
#print axioms QMCLeafB.EllipsoidVolume.exists_potential_below_floor
#print axioms QMCLeafB.EllipsoidVolume.potential_below_floor_of_iterates
#print axioms QMCLeafB.EllipsoidVolume.no_infinite_run
#print axioms QMCLeafB.EllipsoidVolume.volume_ellipsoid_exp_shrink
#print axioms QMCLeafB.EllipsoidVolume.volume_ellipsoid_lt_of_det_lt
#print axioms QMCLeafB.EllipsoidVolume.abs_det_le_of_ellipsoid_subset_eucBall
#print axioms QMCLeafB.EllipsoidVolume.explicit_iteration_count
#print axioms QMCLeafB.EllipsoidVolume.ellipsoid_one
#print axioms QMCLeafB.EllipsoidVolume.volume_ellipsoid_one

end QMCLeafB.EllipsoidVolume


