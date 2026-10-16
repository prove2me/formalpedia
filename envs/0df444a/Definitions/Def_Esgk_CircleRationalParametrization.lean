-- Prove2me | Definitions.Def_Esgk_CircleRationalParametrization
-- name    : Esgk_CircleRationalParametrization
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:53:09.128316+00:00
-- url     : https://prove2.me/theorems/9bfc0a5f-648f-4f67-9afd-5aee2b37dad1
-- title:
--   Rational parametrization of a Euclidean circle
-- statement:
--   This defines a rational parametrization of a Euclidean circle, with its evaluation identities, coverage away from the base point and injectivity for nonzero radius. It also bounds finite sets covered by polynomial-root images, optionally with one additional base point.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneAffineIsometryDistancePolynomial
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic


def circleParamDenominator (t : ℝ) : ℝ := 1 + t ^ 2

theorem circleParamDenominator_pos (t : ℝ) :
    0 < circleParamDenominator t := by
  unfold circleParamDenominator
  nlinarith [sq_nonneg t]

theorem circleParamDenominator_ne_zero (t : ℝ) :
    circleParamDenominator t ≠ 0 :=
  ne_of_gt (circleParamDenominator_pos t)


def circleRationalParam (c : Point2) (r t : ℝ) : Point2 :=
  WithLp.toLp 2
    ![c 0 + r * (1 - t ^ 2) / circleParamDenominator t,
      c 1 + r * (2 * t) / circleParamDenominator t]


def circleRationalBasePoint (c : Point2) (r : ℝ) : Point2 :=
  WithLp.toLp 2 ![c 0 - r, c 1]

@[simp]
theorem circleRationalParam_apply_zero (c : Point2) (r t : ℝ) :
    circleRationalParam c r t 0 =
      c 0 + r * (1 - t ^ 2) / circleParamDenominator t := by
  simp [circleRationalParam]

@[simp]
theorem circleRationalParam_apply_one (c : Point2) (r t : ℝ) :
    circleRationalParam c r t 1 =
      c 1 + r * (2 * t) / circleParamDenominator t := by
  simp [circleRationalParam]

@[simp]
theorem circleRationalBasePoint_apply_zero (c : Point2) (r : ℝ) :
    circleRationalBasePoint c r 0 = c 0 - r := by
  simp [circleRationalBasePoint]

@[simp]
theorem circleRationalBasePoint_apply_one (c : Point2) (r : ℝ) :
    circleRationalBasePoint c r 1 = c 1 := by
  simp [circleRationalBasePoint]


theorem circleRationalParam_dist_sq (c : Point2) (r t : ℝ) :
    dist (circleRationalParam c r t) c ^ 2 = r ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [circleRationalParam, Fin.sum_univ_two, Real.dist_eq,
    circleParamDenominator]
  field_simp [circleParamDenominator_ne_zero]
  ring


theorem circleRationalParam_mem_sphere (c : Point2) {r : ℝ} (hr : 0 ≤ r)
    (t : ℝ) : circleRationalParam c r t ∈ Metric.sphere c r := by
  change dist (circleRationalParam c r t) c = r
  have hsq := circleRationalParam_dist_sq c r t
  nlinarith [dist_nonneg (x := circleRationalParam c r t) (y := c)]


theorem circleRationalParam_injective (c : Point2) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (circleRationalParam c r) := by
  intro t u htu
  have hzero := congrArg (fun z : Point2 ↦ z 0) htu
  have hone := congrArg (fun z : Point2 ↦ z 1) htu
  simp only [circleRationalParam_apply_zero] at hzero
  simp only [circleRationalParam_apply_one] at hone
  have hzero' :
      (1 - t ^ 2) / circleParamDenominator t =
        (1 - u ^ 2) / circleParamDenominator u := by
    apply mul_left_cancel₀ hr
    simpa [mul_div_assoc] using add_left_cancel hzero
  have hone' :
      (2 * t) / circleParamDenominator t =
        (2 * u) / circleParamDenominator u := by
    apply mul_left_cancel₀ hr
    simpa [mul_div_assoc] using add_left_cancel hone
  have hsquare : t ^ 2 = u ^ 2 := by
    field_simp [circleParamDenominator_ne_zero] at hzero'
    unfold circleParamDenominator at hzero'
    nlinarith
  field_simp [circleParamDenominator_ne_zero] at hone'
  unfold circleParamDenominator at hone'
  rw [hsquare] at hone'
  have hden : 1 + u ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg u]
  apply mul_left_cancel₀ hden
  simpa [mul_comm] using hone'


theorem exists_circleRationalParam_eq_of_mem_sphere_ne_base
    (c : Point2) {r : ℝ} (hr : 0 < r) {z : Point2}
    (hz : z ∈ Metric.sphere c r)
    (hzbase : z ≠ circleRationalBasePoint c r) :
    ∃ t : ℝ, circleRationalParam c r t = z := by
  change dist z c = r at hz
  have hcircle :
      (z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2 = r ^ 2 := by
    have hsquare := congrArg (fun x : ℝ ↦ x ^ 2) hz
    change dist z c ^ 2 = r ^ 2 at hsquare
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hsquare
    simpa [Real.dist_eq, sq_abs] using hsquare
  have hden : r + (z 0 - c 0) ≠ 0 := by
    intro hzero
    have hx : z 0 = c 0 - r := by linarith
    have hy : z 1 = c 1 := by
      have hySq : (z 1 - c 1) ^ 2 = 0 := by
        nlinarith
      nlinarith [sq_nonneg (z 1 - c 1)]
    apply hzbase
    ext i
    fin_cases i
    · simp [circleRationalBasePoint, hx]
    · simp [circleRationalBasePoint, hy]
  have hdenSquare :
      (r + (z 0 - c 0)) ^ 2 + (z 1 - c 1) ^ 2 =
        2 * r * (r + (z 0 - c 0)) := by
    nlinarith
  let t : ℝ := (z 1 - c 1) / (r + (z 0 - c 0))
  refine ⟨t, ?_⟩
  have htden := circleParamDenominator_ne_zero t
  ext i
  fin_cases i
  · change c 0 + r * (1 - t ^ 2) / circleParamDenominator t = z 0
    dsimp [t] at htden ⊢
    unfold circleParamDenominator at htden ⊢
    field_simp [hden, htden]
    nlinarith [hdenSquare]
  · change c 1 + r * (2 * t) / circleParamDenominator t = z 1
    dsimp [t] at htden ⊢
    unfold circleParamDenominator at htden ⊢
    field_simp [hden, htden]
    rw [hdenSquare]
    ring


theorem card_le_natDegree_add_one_of_parametrized_roots
    {β : Type*} [DecidableEq β] (S : Finset β) (p : Polynomial ℝ)
    (param : ℝ → β) (base : β)
    (hcover :
      ∀ z ∈ S, z = base ∨
        ∃ t ∈ p.roots.toFinset, param t = z) :
    S.card ≤ p.natDegree + 1 := by
  let rootImages := p.roots.toFinset.image param
  have hsubset : S ⊆ insert base rootImages := by
    intro z hz
    rcases hcover z hz with hbase | ⟨t, ht, rfl⟩
    · exact Finset.mem_insert.mpr (Or.inl hbase)
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr ⟨t, ht, rfl⟩))
  calc
    S.card ≤ (insert base rootImages).card := Finset.card_le_card hsubset
    _ ≤ rootImages.card + 1 := Finset.card_insert_le base rootImages
    _ ≤ p.roots.toFinset.card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ p.roots.card + 1 :=
      Nat.add_le_add_right p.roots.toFinset_card_le 1
    _ ≤ p.natDegree + 1 :=
      Nat.add_le_add_right p.card_roots' 1


theorem card_le_natDegree_of_parametrized_roots
    {β : Type*} [DecidableEq β] (S : Finset β) (p : Polynomial ℝ)
    (param : ℝ → β)
    (hcover :
      ∀ z ∈ S, ∃ t ∈ p.roots.toFinset, param t = z) :
    S.card ≤ p.natDegree := by
  let rootImages := p.roots.toFinset.image param
  have hsubset : S ⊆ rootImages := by
    intro z hz
    rcases hcover z hz with ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  calc
    S.card ≤ rootImages.card := Finset.card_le_card hsubset
    _ ≤ p.roots.toFinset.card := Finset.card_image_le
    _ ≤ p.roots.card := p.roots.toFinset_card_le
    _ ≤ p.natDegree := p.card_roots'

end Esgk


