-- Prove2me | Definitions.Def_LeanPool_ParallelPostulate
-- name    : LeanPool_ParallelPostulate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:10:53.954788+00:00
-- url     : https://prove2.me/theorems/818ecc5c-2523-459d-bf9a-d051539384db
-- title:
--   Parallel Postulate
-- statement:
--   Definitions and structural lemmas for Parallel Postulate, from Richard Sutton; LeanPool contributors's pinned Independence of the parallel postulate development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_mem
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_ne
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_not_left
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_not_right
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_eq_through
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_subset_plane
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_two_points
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_between_trichotomy
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_crosses
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_exists_beyond
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_exists_three_points
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_line_through
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_ne_of_side_ne_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_pasch
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_convex
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_openAlong
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_open_forward
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_zero
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_sq_add_sq_pos
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_zero_mem_plane
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_mem_points_of_side_eq_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_one_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_one
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_side_eq_zero_of_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_side_through
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_zero_mem
public import Theorems.Thm_ParallelPostulate_Pairs_exists_mul_of_cross_eq_zero

set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace ParallelPostulate
namespace ThreeDimensions
open Pairs
section Plane
variable {K : Type*} [CommRing K]
@[expose] def Meet (L M : Dim K) : Prop := ∃ t u : K, L.pt t = M.pt u
end Plane
@[expose] def wholeFigure : Figure ℤ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (1, 1)⟩
  c := ⟨(1, 0), (0, 1)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl
section Fractions
variable {K : Type*} [Field K]
end Fractions
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
end Ordered
@[expose] def exampleFigure : Figure ℚ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (1, 1)⟩
  c := ⟨(1, 0), (0, 1)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl
section Angles
open Real
@[expose] noncomputable def angleFigure (β γ : ℝ) : Figure ℝ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (cos β, sin β)⟩
  c := ⟨(1, 0), (1 - cos γ, sin γ)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl
end Angles
section MathlibAngles
open Real InnerProductGeometry
@[expose] noncomputable def toE (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[p.1, p.2]
end MathlibAngles
end ThreeDimensions
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section StepsAlgebra
variable {K : Type*} [Field K]
@[expose] def step (κ t u : K) : K := (t + u) / (1 - κ * t * u)
@[expose] def shift (κ a w : K) (p : K × K) : K × K :=
  ((p.1 + a) / (1 - κ * a * p.1), w * p.2 / (1 - κ * a * p.1))
theorem shift_bound {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {p : K × K}
    (hD : 1 - κ * a * p.1 ≠ 0) :
    1 + κ * ((shift κ a w p).1 ^ 2 + (shift κ a w p).2 ^ 2)
      = w ^ 2 * (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) / (1 - κ * a * p.1) ^ 2 := by
  have hX : (p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) = p.1 + a :=
    div_mul_cancel₀ _ hD
  have hY : w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) = w * p.2 :=
    div_mul_cancel₀ _ hD
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  simp only [shift]
  linear_combination
    κ * ((p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) + (p.1 + a)) * hX
    + κ * (w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) + w * p.2) * hY
    - (1 + κ * p.1 ^ 2) * hw
theorem shift_shift_neg {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {p : K × K}
    (hD : 1 - κ * a * p.1 ≠ 0) : shift κ (-a) w (shift κ a w p) = p := by
  have hX : (p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) = p.1 + a :=
    div_mul_cancel₀ _ hD
  have hY : w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) = w * p.2 :=
    div_mul_cancel₀ _ hD
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  have hDD : (1 - κ * -a * ((p.1 + a) / (1 - κ * a * p.1))) * (1 - κ * a * p.1) = w ^ 2 := by
    linear_combination κ * a * hX - hw
  have hD' : 1 - κ * -a * ((p.1 + a) / (1 - κ * a * p.1)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hDD
    exact hw2 hDD.symm
  apply Prod.ext
  · simp only [shift]
    rw [div_eq_iff hD']
    apply mul_right_cancel₀ hD
    linear_combination hX - p.1 * hDD - p.1 * hw
  · simp only [shift]
    rw [div_eq_iff hD']
    apply mul_right_cancel₀ hD
    linear_combination w * hY - p.2 * hDD
@[expose] def apart (κ : K) (P Q : K × K) : K :=
  ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2)
    / ((1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))
theorem apart_zero_bound (P Q : K × K) :
    apart 0 P Q = (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 := by
  simp [apart]
theorem apart_self (κ : K) (P : K × K) : apart κ P P = 0 := by
  have h : (P.1 - P.1) ^ 2 + (P.2 - P.2) ^ 2 + κ * (P.1 * P.2 - P.2 * P.1) ^ 2 = 0 := by ring
  simp only [apart, h, zero_div]
theorem apart_comm (κ : K) (P Q : K × K) : apart κ P Q = apart κ Q P := by
  have h : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2
      = (Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2 + κ * (Q.1 * P.2 - Q.2 * P.1) ^ 2 := by ring
  simp only [apart]
  rw [h, mul_comm (1 + κ * (P.1 ^ 2 + P.2 ^ 2))]
theorem apart_centre (κ t : K) : apart κ (0, 0) (t, 0) = t ^ 2 / (1 + κ * t ^ 2) := by
  simp [apart]
theorem apart_aux (κ a w xP yP xQ yQ XP YP XQ YQ : K) (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXQ : XQ * (1 - κ * a * xQ) = xQ + a) (hYQ : YQ * (1 - κ * a * xQ) = w * yQ) :
    ((XP - XQ) ^ 2 + (YP - YQ) ^ 2 + κ * (XP * YQ - YP * XQ) ^ 2)
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xQ) ^ 2)
      = w ^ 4 * ((xP - xQ) ^ 2 + (yP - yQ) ^ 2 + κ * (xP * yQ - yP * xQ) ^ 2) := by
  have e1 : (XP - XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ)) = w ^ 2 * (xP - xQ) := by
    linear_combination (1 - κ * a * xQ) * hXP - (1 - κ * a * xP) * hXQ - (xP - xQ) * hw
  have e2 : (YP - YQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))
      = w * ((yP - yQ) + κ * a * (xP * yQ - yP * xQ)) := by
    linear_combination (1 - κ * a * xQ) * hYP - (1 - κ * a * xP) * hYQ
  have e3 : (XP * YQ - YP * XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))
      = w * ((xP * yQ - yP * xQ) - a * (yP - yQ)) := by
    linear_combination (YQ * (1 - κ * a * xQ)) * hXP + (xP + a) * hYQ
      - (XQ * (1 - κ * a * xQ)) * hYP - (w * yP) * hXQ
  have e : ((XP - XQ) ^ 2 + (YP - YQ) ^ 2 + κ * (XP * YQ - YP * XQ) ^ 2)
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xQ) ^ 2)
      = ((XP - XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2
        + ((YP - YQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2
        + κ * ((XP * YQ - YP * XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2 := by ring
  rw [e, e1, e2, e3]
  linear_combination (-(w ^ 2 * ((yP - yQ) ^ 2 + κ * (xP * yQ - yP * xQ) ^ 2))) * hw
theorem apart_aux' (N N' BP BQ VP VQ DP DQ w : K) (hw : w ≠ 0) (hDP : DP ≠ 0) (hDQ : DQ ≠ 0)
    (hBP : BP ≠ 0) (hBQ : BQ ≠ 0) (hN : N' * (DP ^ 2 * DQ ^ 2) = w ^ 4 * N)
    (hVP : VP * DP ^ 2 = w ^ 2 * BP) (hVQ : VQ * DQ ^ 2 = w ^ 2 * BQ) :
    N' / (VP * VQ) = N / (BP * BQ) := by
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hVP0 : VP ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVP
    exact mul_ne_zero hw2 hBP hVP.symm
  have hVQ0 : VQ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVQ
    exact mul_ne_zero hw2 hBQ hVQ.symm
  rw [div_eq_div_iff (mul_ne_zero hVP0 hVQ0) (mul_ne_zero hBP hBQ)]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hDP) (pow_ne_zero 2 hDQ))
  linear_combination (BP * BQ) * hN - N * (VQ * DQ ^ 2) * hVP - N * (w ^ 2 * BP) * hVQ
theorem shift_apart {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {P Q : K × K}
    (hDP : 1 - κ * a * P.1 ≠ 0) (hDQ : 1 - κ * a * Q.1 ≠ 0)
    (hP : 1 + κ * (P.1 ^ 2 + P.2 ^ 2) ≠ 0) (hQ : 1 + κ * (Q.1 ^ 2 + Q.2 ^ 2) ≠ 0) :
    apart κ (shift κ a w P) (shift κ a w Q) = apart κ P Q := by
  have hN : (((shift κ a w P).1 - (shift κ a w Q).1) ^ 2
      + ((shift κ a w P).2 - (shift κ a w Q).2) ^ 2
      + κ * ((shift κ a w P).1 * (shift κ a w Q).2
        - (shift κ a w P).2 * (shift κ a w Q).1) ^ 2)
        * ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * Q.1) ^ 2)
      = w ^ 4 * ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2) :=
    apart_aux κ a w P.1 P.2 Q.1 Q.2 _ _ _ _ hw
      (div_mul_cancel₀ (P.1 + a) hDP) (div_mul_cancel₀ (w * P.2) hDP)
      (div_mul_cancel₀ (Q.1 + a) hDQ) (div_mul_cancel₀ (w * Q.2) hDQ)
  unfold apart
  exact apart_aux' _ _ _ _ _ _ _ _ w hw0 hDP hDQ hP hQ hN
    ((eq_div_iff (pow_ne_zero 2 hDP)).mp (shift_bound hw hDP))
    ((eq_div_iff (pow_ne_zero 2 hDQ)).mp (shift_bound hw hDQ))
@[expose] def rot (c s : K) (p : K × K) : K × K := (c * p.1 - s * p.2, s * p.1 + c * p.2)
theorem rot_rot_neg {c s : K} (h : c ^ 2 + s ^ 2 = 1) (p : K × K) :
    rot c (-s) (rot c s p) = p := by
  apply Prod.ext
  · simp only [rot]
    linear_combination p.1 * h
  · simp only [rot]
    linear_combination p.2 * h
theorem rot_bound {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (p : K × K) :
    1 + κ * ((rot c s p).1 ^ 2 + (rot c s p).2 ^ 2) = 1 + κ * (p.1 ^ 2 + p.2 ^ 2) := by
  simp only [rot]
  linear_combination κ * (p.1 ^ 2 + p.2 ^ 2) * h
theorem rot_apart {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P Q : K × K) :
    apart κ (rot c s P) (rot c s Q) = apart κ P Q := by
  have hN : ((rot c s P).1 - (rot c s Q).1) ^ 2 + ((rot c s P).2 - (rot c s Q).2) ^ 2
      + κ * ((rot c s P).1 * (rot c s Q).2 - (rot c s P).2 * (rot c s Q).1) ^ 2
      = (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2 := by
    simp only [rot]
    linear_combination ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2
      + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2 * (c ^ 2 + s ^ 2 + 1)) * h
  simp only [apart]
  rw [hN, rot_bound h, rot_bound h]
end StepsAlgebra
section StepsOrder
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
theorem step_den_pos {κ t u : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) : 0 < 1 - κ * t * u := by
  nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg (t + u))]
theorem apart_pos {κ : K} {P Q : K × K} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) (hPQ : P ≠ Q) :
    0 < apart κ P Q := by
  have hv : (P.1 - Q.1, P.2 - Q.2) ≠ ((0 : K), (0 : K)) := by
    intro h
    apply hPQ
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hd : 0 < (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 := sq_add_sq_pos hv
  apply div_pos _ (mul_pos (mem_plane.mp hP) (mem_plane.mp hQ))
  rcases le_or_gt 0 κ with hκ | hκ
  · have h := mul_nonneg hκ (sq_nonneg (P.1 * Q.2 - P.2 * Q.1))
    linarith
  · have e : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2
        = ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) * (1 + κ * (P.1 ^ 2 + P.2 ^ 2))
          + -κ * (P.1 * (Q.1 - P.1) + P.2 * (Q.2 - P.2)) ^ 2 := by ring
    rw [e]
    have h1 := mul_pos hd (mem_plane.mp hP)
    have h2 := mul_nonneg (neg_nonneg.mpr hκ.le)
      (sq_nonneg (P.1 * (Q.1 - P.1) + P.2 * (Q.2 - P.2)))
    linarith
theorem shift_den_pos {κ a : K} (hκ : κ ≤ 0) (ha : 0 < 1 + κ * a ^ 2) {p : K × K}
    (hp : p ∈ plane κ) : 0 < 1 - κ * a * p.1 := by
  have hx : 0 < 1 + κ * p.1 ^ 2 := by
    have h := mem_plane.mp hp
    nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg p.2)]
  exact step_den_pos hκ ha hx
theorem shift_mem_plane {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {p : K × K} (hp : p ∈ plane κ) : shift κ a w p ∈ plane κ := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have hD := shift_den_pos hκ (hw ▸ hw2) hp
  rw [mem_plane, shift_bound hw hD.ne']
  exact div_pos (mul_pos hw2 (mem_plane.mp hp)) (pow_pos hD 2)
theorem shift_neg_shift {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {p : K × K} (hp : p ∈ plane κ) : shift κ (-a) w (shift κ a w p) = p := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  exact shift_shift_neg hw hw0 (shift_den_pos hκ (hw ▸ hw2) hp).ne'
theorem shift_apart_plane {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P Q : K × K} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    apart κ (shift κ a w P) (shift κ a w Q) = apart κ P Q := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  exact shift_apart hw hw0 (shift_den_pos hκ ha hP).ne' (shift_den_pos hκ ha hQ).ne'
    (mem_plane.mp hP).ne' (mem_plane.mp hQ).ne'
omit [IsStrictOrderedRing K] in
/-- **Turning takes points of the plane to points of the plane**, and no others. -/
theorem rot_mem_plane {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {p : K × K} :
    rot c s p ∈ plane κ ↔ p ∈ plane κ := by
  rw [mem_plane, mem_plane, rot_bound h]
end StepsOrder
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section InnerAlgebra
variable {K : Type*} [Field K]
@[expose] def kleinInner (κ : K) (P A B : K × K) : K :=
  (A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) + κ * cross P A * cross P B
end InnerAlgebra
section InnerOrder
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
theorem kleinInner_self_pos {κ : K} {P A : K × K} (hP : P ∈ plane κ) (hA : A ≠ P) :
    0 < kleinInner κ P A A := by
  have hv : (A.1 - P.1, A.2 - P.2) ≠ ((0 : K), (0 : K)) := by
    intro h
    apply hA
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hd : 0 < (A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 := sq_add_sq_pos hv
  rcases le_or_gt 0 κ with hκ | hκ
  · have e : kleinInner κ P A A = (A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 + κ * cross P A ^ 2 := by
      simp only [kleinInner]
      ring
    rw [e]
    have h := mul_nonneg hκ (sq_nonneg (cross P A))
    linarith
  · have e : kleinInner κ P A A
        = ((A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2) * (1 + κ * (P.1 ^ 2 + P.2 ^ 2))
          + -κ * (P.1 * (A.1 - P.1) + P.2 * (A.2 - P.2)) ^ 2 := by
      simp only [kleinInner, cross]
      ring
    rw [e]
    have h1 := mul_pos hd (mem_plane.mp hP)
    have h2 := mul_nonneg (neg_nonneg.mpr hκ.le)
      (sq_nonneg (P.1 * (A.1 - P.1) + P.2 * (A.2 - P.2)))
    linarith
end InnerOrder
section Angles
open Real
@[expose] noncomputable def kleinAngle (κ : ℝ) (P A B : ℝ × ℝ) : ℝ :=
  arccos (kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B)))
theorem kleinAngle_aux {g g₁ g₂ m u v : ℝ} (hm : 0 < m) (huv : 0 < u * v) :
    arccos (m * u * v * g / (√(m * u ^ 2 * g₁) * √(m * v ^ 2 * g₂)))
      = arccos (g / (√g₁ * √g₂)) := by
  have hsq : √m * √m = m := mul_self_sqrt hm.le
  have habs : |u| * |v| = u * v := by rw [← abs_mul, abs_of_pos huv]
  have h1 : √(m * u ^ 2 * g₁) = √m * |u| * √g₁ := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ m * u ^ 2), sqrt_mul hm.le, sqrt_sq_eq_abs]
  have h2 : √(m * v ^ 2 * g₂) = √m * |v| * √g₂ := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ m * v ^ 2), sqrt_mul hm.le, sqrt_sq_eq_abs]
  have hden : √(m * u ^ 2 * g₁) * √(m * v ^ 2 * g₂) = m * u * v * (√g₁ * √g₂) := by
    rw [h1, h2]
    linear_combination (|u| * |v| * √g₁ * √g₂) * hsq + (m * √g₁ * √g₂) * habs
  have hmuv : m * u * v ≠ 0 := by
    rw [mul_assoc]
    exact (mul_pos hm huv).ne'
  rw [hden, mul_div_mul_left _ _ hmuv]
theorem exists_motion_to_centre {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) :
    ∃ c s a w : ℝ, c ^ 2 + s ^ 2 = 1 ∧ w ^ 2 = 1 + κ * a ^ 2 ∧ 0 < w ∧
      shift κ a w (rot c s P) = (0, 0) := by
  by_cases h0 : P.1 ^ 2 + P.2 ^ 2 = 0
  · have h1 : P.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg P.2])
    have h2 : P.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg P.1])
    refine ⟨1, 0, 0, 1, by norm_num, by ring, one_pos, ?_⟩
    apply Prod.ext <;> simp [shift, rot, h1, h2]
  · have hpos : 0 < P.1 ^ 2 + P.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = P.1 ^ 2 + P.2 ^ 2 :=
      ⟨√(P.1 ^ 2 + P.2 ^ 2), sqrt_pos.mpr hpos, sq_sqrt hpos.le⟩
    have hw : 0 < 1 + κ * r ^ 2 := by
      rw [hr2]
      exact mem_plane.mp hP
    have hrot : rot (P.1 / r) (-P.2 / r) P = (r, 0) := by
      apply Prod.ext
      · simp only [rot]
        field_simp
        linear_combination -hr2
      · simp only [rot]
        ring
    refine ⟨P.1 / r, -P.2 / r, -r, √(1 + κ * r ^ 2), ?_, ?_, sqrt_pos.mpr hw, ?_⟩
    · field_simp
      linear_combination -hr2
    · rw [sq_sqrt hw.le]
      ring
    · rw [hrot]
      apply Prod.ext <;> simp [shift]
end Angles
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section MetricAlgebra
variable {K : Type*} [Field K]
@[expose] def kleinMetric (κ : K) (P u v : K × K) : K :=
  (u.1 * v.1 + u.2 * v.2 + κ * cross P u * cross P v) / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2
@[expose] def shiftDeriv (κ a w : K) (P u : K × K) : K × K :=
  ((1 + κ * a ^ 2) * u.1 / (1 - κ * a * P.1) ^ 2,
    w * (κ * a * P.2 * u.1 + (1 - κ * a * P.1) * u.2) / (1 - κ * a * P.1) ^ 2)
theorem kleinMetric_aux (κ a w x y u1 u2 v1 v2 : K) (hw : w ^ 2 = 1 + κ * a ^ 2) :
    (1 + κ * a ^ 2) ^ 2 * (u1 * v1)
        + w ^ 2 * ((κ * a * y * u1 + (1 - κ * a * x) * u2)
          * (κ * a * y * v1 + (1 - κ * a * x) * v2))
        + κ * w ^ 2 * (((x + a) * u2 - y * u1) * ((x + a) * v2 - y * v1))
      = w ^ 4 * (u1 * v1 + u2 * v2 + κ * (x * u2 - y * u1) * (x * v2 - y * v1)) := by
  rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw]
  ring
theorem shift_kleinMetric {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {P : K × K}
    (hD : 1 - κ * a * P.1 ≠ 0) (hP : 1 + κ * (P.1 ^ 2 + P.2 ^ 2) ≠ 0) (u v : K × K) :
    kleinMetric κ (shift κ a w P) (shiftDeriv κ a w P u) (shiftDeriv κ a w P v)
      = kleinMetric κ P u v := by
  have h1 : ((shiftDeriv κ a w P u).1 * (shiftDeriv κ a w P v).1
        + (shiftDeriv κ a w P u).2 * (shiftDeriv κ a w P v).2
        + κ * cross (shift κ a w P) (shiftDeriv κ a w P u)
          * cross (shift κ a w P) (shiftDeriv κ a w P v)) * (1 - κ * a * P.1) ^ 4
      = (1 + κ * a ^ 2) ^ 2 * (u.1 * v.1)
        + w ^ 2 * ((κ * a * P.2 * u.1 + (1 - κ * a * P.1) * u.2)
          * (κ * a * P.2 * v.1 + (1 - κ * a * P.1) * v.2))
        + κ * w ^ 2 * (((P.1 + a) * u.2 - P.2 * u.1) * ((P.1 + a) * v.2 - P.2 * v.1)) := by
    simp only [shift, shiftDeriv, cross]
    field_simp
    ring
  have h2 : (shiftDeriv κ a w P u).1 * (shiftDeriv κ a w P v).1
        + (shiftDeriv κ a w P u).2 * (shiftDeriv κ a w P v).2
        + κ * cross (shift κ a w P) (shiftDeriv κ a w P u)
          * cross (shift κ a w P) (shiftDeriv κ a w P v)
      = w ^ 4 * (u.1 * v.1 + u.2 * v.2 + κ * cross P u * cross P v) / (1 - κ * a * P.1) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 hD), h1, kleinMetric_aux κ a w P.1 P.2 u.1 u.2 v.1 v.2 hw]
    simp only [cross]
  unfold kleinMetric
  rw [h2, shift_bound hw hD]
  field_simp
theorem rot_kleinMetric {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P u v : K × K) :
    kleinMetric κ (rot c s P) (rot c s u) (rot c s v) = kleinMetric κ P u v := by
  unfold kleinMetric
  rw [rot_bound h]
  congr 1
  simp only [rot, cross]
  linear_combination (u.1 * v.1 + u.2 * v.2
    + κ * (P.1 * u.2 - P.2 * u.1) * (P.1 * v.2 - P.2 * v.1) * (c ^ 2 + s ^ 2 + 1)) * h
end MetricAlgebra
section MetricOrder
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
end MetricOrder
section Metric
open Real
theorem shift_differentiableAt {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) :
    DifferentiableAt ℝ (shift κ a w) P := by
  unfold shift
  simp only [div_eq_mul_inv]
  fun_prop (disch := exact hD)
theorem shift_hasLineDerivAt {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) (u : ℝ × ℝ) :
    HasLineDerivAt ℝ (shift κ a w) (shiftDeriv κ a w P u) P u := by
  have e : (fun t : ℝ => shift κ a w (P + t • u)) = fun t : ℝ =>
      ((P.1 + t * u.1 + a) / (1 - κ * a * (P.1 + t * u.1)),
        w * (P.2 + t * u.2) / (1 - κ * a * (P.1 + t * u.1))) := by
    funext t
    simp [shift]
  have hx : HasDerivAt (fun t : ℝ => P.1 + t * u.1) u.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.1).const_add P.1
  have hy : HasDerivAt (fun t : ℝ => P.2 + t * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.2).const_add P.2
  have hd : HasDerivAt (fun t : ℝ => 1 - κ * a * (P.1 + t * u.1)) (-(κ * a * u.1)) 0 :=
    (hx.const_mul (κ * a)).const_sub 1
  have hD0 : 1 - κ * a * (P.1 + 0 * u.1) ≠ 0 := by simpa using hD
  have h := ((hx.add_const a).div hd hD0).prodMk ((hy.const_mul w).div hd hD0)
  unfold HasLineDerivAt
  rw [e]
  convert! h using 1
  try simp only [shiftDeriv, zero_mul, add_zero]
  apply Prod.ext
  · field_simp
    ring
  · field_simp
    ring
theorem fderiv_shift {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) (u : ℝ × ℝ) :
    fderiv ℝ (shift κ a w) P u = shiftDeriv κ a w P u := by
  rw [← (shift_differentiableAt hD).lineDeriv_eq_fderiv]
  exact (shift_hasLineDerivAt hD u).lineDeriv
theorem fderiv_rot (c s : ℝ) (P u : ℝ × ℝ) : fderiv ℝ (rot c s) P u = rot c s u := by
  have hdiff : DifferentiableAt ℝ (rot c s) P := by
    unfold rot
    fun_prop
  have e : (fun t : ℝ => rot c s (P + t • u)) = fun t : ℝ =>
      (c * (P.1 + t * u.1) - s * (P.2 + t * u.2), s * (P.1 + t * u.1) + c * (P.2 + t * u.2)) := by
    funext t
    simp [rot]
  have hx : HasDerivAt (fun t : ℝ => P.1 + t * u.1) u.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.1).const_add P.1
  have hy : HasDerivAt (fun t : ℝ => P.2 + t * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.2).const_add P.2
  have h : HasLineDerivAt ℝ (rot c s) (rot c s u) P u := by
    unfold HasLineDerivAt
    rw [e]
    exact ((hx.const_mul c).sub (hy.const_mul s)).prodMk ((hx.const_mul s).add (hy.const_mul c))
  rw [← hdiff.lineDeriv_eq_fderiv]
  exact h.lineDeriv
theorem shift_kleinMetric_fderiv {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hw0 : w ≠ 0) {P : ℝ × ℝ} (hP : P ∈ plane κ) (u v : ℝ × ℝ) :
    kleinMetric κ (shift κ a w P) (fderiv ℝ (shift κ a w) P u) (fderiv ℝ (shift κ a w) P v)
      = kleinMetric κ P u v := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have hD := (shift_den_pos hκ (hw ▸ hw2) hP).ne'
  rw [fderiv_shift hD, fderiv_shift hD]
  exact shift_kleinMetric hw hw0 hD (mem_plane.mp hP).ne' u v
theorem rot_kleinMetric_fderiv {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P u v : ℝ × ℝ) :
    kleinMetric κ (rot c s P) (fderiv ℝ (rot c s) P u) (fderiv ℝ (rot c s) P v)
      = kleinMetric κ P u v := by
  rw [fderiv_rot, fderiv_rot]
  exact rot_kleinMetric h κ P u v
end Metric
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section Curvature
open Filter Topology
@[expose] noncomputable def partialX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => f (t, p.2)) p.1
@[expose] noncomputable def partialY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => f (p.1, t)) p.2
@[expose] noncomputable def gaussCurvature (E F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Matrix.det !![-partialY (partialY E) p / 2 + partialX (partialY F) p
          - partialX (partialX G) p / 2, partialX E p / 2, partialX F p - partialY E p / 2;
        partialY F p - partialX G p / 2, E p, F p;
        partialY G p / 2, F p, G p]
    - Matrix.det !![0, partialY E p / 2, partialX G p / 2;
        partialY E p / 2, E p, F p;
        partialX G p / 2, F p, G p]) / (E p * G p - F p ^ 2) ^ 2
@[expose] noncomputable def kleinE (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + κ * p.2 ^ 2) / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
@[expose] noncomputable def kleinF (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  -κ * p.1 * p.2 / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
@[expose] noncomputable def kleinG (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + κ * p.1 ^ 2) / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
end Curvature
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section Distance
open Set Filter Topology Real
@[expose] def IsKleinPath (κ : ℝ) (γ : ℝ → ℝ × ℝ) (P Q : ℝ × ℝ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) (plane κ) ∧ γ 0 = P ∧ γ 1 = Q
@[expose] noncomputable def kleinLength (κ : ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t) (derivWithin γ (Icc 0 1) t))
@[expose] noncomputable def kleinDist (κ : ℝ) (P Q : ℝ × ℝ) : ℝ :=
  sInf (kleinLength κ '' {γ | IsKleinPath κ γ P Q})
theorem kleinLength_nonneg (κ : ℝ) (γ : ℝ → ℝ × ℝ) : 0 ≤ kleinLength κ γ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sqrt_nonneg _)
theorem segment_isKleinPath {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    IsKleinPath κ (Dim.mk P Q).pt P Q := by
  refine ⟨?_, fun t ht => plane_convex κ hP hQ ht.1 ht.2, Dim.pt_zero _, Dim.pt_one _⟩
  have : ContDiff ℝ 1 (Dim.mk P Q).pt := by
    unfold Dim.pt
    fun_prop
  exact this.contDiffOn
theorem kleinDist_nonempty {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    (kleinLength κ '' {γ | IsKleinPath κ γ P Q}).Nonempty :=
  ⟨_, _, segment_isKleinPath hP hQ, rfl⟩
theorem kleinDist_bddBelow (κ : ℝ) (P Q : ℝ × ℝ) :
    BddBelow (kleinLength κ '' {γ | IsKleinPath κ γ P Q}) :=
  ⟨0, by rintro _ ⟨γ, -, rfl⟩; exact kleinLength_nonneg κ γ⟩
theorem kleinLength_integrand_continuousOn {κ : ℝ} {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ}
    (h : IsKleinPath κ γ P Q) :
    ContinuousOn (fun t => √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t)
      (derivWithin γ (Icc 0 1) t))) (Icc 0 1) := by
  have hγ : ContinuousOn γ (Icc 0 1) := h.1.continuousOn
  have hv : ContinuousOn (derivWithin γ (Icc 0 1)) (Icc 0 1) :=
    h.1.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, (1 + κ * ((γ t).1 ^ 2 + (γ t).2 ^ 2)) ^ 2 ≠ 0 :=
    fun t ht => pow_ne_zero 2 (mem_plane.mp (h.2.1 ht)).ne'
  unfold kleinMetric cross
  apply ContinuousOn.sqrt
  apply ContinuousOn.div _ _ hB
  · fun_prop
  · fun_prop
theorem isKleinPath_map {κ : ℝ} {M : ℝ × ℝ → ℝ × ℝ} (hM : ContDiffOn ℝ 1 M (plane κ))
    (hMp : MapsTo M (plane κ) (plane κ)) (hMd : ∀ p ∈ plane κ, DifferentiableAt ℝ M p)
    (hMg : ∀ p ∈ plane κ, ∀ v, kleinMetric κ (M p) (fderiv ℝ M p v) (fderiv ℝ M p v)
      = kleinMetric κ p v v)
    {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ} (h : IsKleinPath κ γ P Q) :
    IsKleinPath κ (M ∘ γ) (M P) (M Q) ∧ kleinLength κ (M ∘ γ) = kleinLength κ γ := by
  obtain ⟨hγ, hmaps, h0, h1⟩ := h
  refine ⟨⟨hM.comp hγ hmaps, hMp.comp hmaps, by simp [h0], by simp [h1]⟩, ?_⟩
  unfold kleinLength
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hd : derivWithin (M ∘ γ) (Icc 0 1) t = fderiv ℝ M (γ t) (derivWithin γ (Icc 0 1) t) :=
    ((hMd _ (hmaps ht)).hasFDerivAt.comp_hasDerivWithinAt t
      ((hγ.differentiableOn one_ne_zero t ht).hasDerivWithinAt)).derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)
  simp only [Function.comp_apply, hd, hMg _ (hmaps ht)]
theorem kleinDist_map_le {κ : ℝ} {M : ℝ × ℝ → ℝ × ℝ} (hM : ContDiffOn ℝ 1 M (plane κ))
    (hMp : MapsTo M (plane κ) (plane κ)) (hMd : ∀ p ∈ plane κ, DifferentiableAt ℝ M p)
    (hMg : ∀ p ∈ plane κ, ∀ v, kleinMetric κ (M p) (fderiv ℝ M p v) (fderiv ℝ M p v)
      = kleinMetric κ p v v)
    {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    kleinDist κ (M P) (M Q) ≤ kleinDist κ P Q := by
  apply csInf_le_csInf (kleinDist_bddBelow κ _ _) (kleinDist_nonempty hP hQ)
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨hpath, hlen⟩ := isKleinPath_map hM hMp hMd hMg hγ
  exact ⟨M ∘ γ, hpath, hlen⟩
theorem shift_contDiffOn {κ a w : ℝ} (hκ : κ ≤ 0) (ha : 0 < 1 + κ * a ^ 2) :
    ContDiffOn ℝ 1 (shift κ a w) (plane κ) := by
  unfold shift
  simp only [div_eq_mul_inv]
  have hD : ∀ p ∈ plane κ, 1 - κ * a * p.1 ≠ 0 := fun p hp => (shift_den_pos hκ ha hp).ne'
  apply ContDiffOn.prodMk
  · exact ContDiffOn.mul (by fun_prop) (ContDiffOn.inv (by fun_prop) hD)
  · exact ContDiffOn.mul (by fun_prop) (ContDiffOn.inv (by fun_prop) hD)
theorem shift_kleinDist {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    kleinDist κ (shift κ a w P) (shift κ a w Q) = kleinDist κ P Q := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by rw [hw]; ring
  have ha' : 0 < 1 + κ * (-a) ^ 2 := hw' ▸ hw2
  have key : ∀ b : ℝ, w ^ 2 = 1 + κ * b ^ 2 → 0 < 1 + κ * b ^ 2 → ∀ X Y : ℝ × ℝ,
      X ∈ plane κ → Y ∈ plane κ → kleinDist κ (shift κ b w X) (shift κ b w Y) ≤ kleinDist κ X Y :=
    fun b hb hb' X Y hX hY => kleinDist_map_le (shift_contDiffOn hκ hb')
      (fun p hp => shift_mem_plane hκ hb hw0 hp)
      (fun p hp => shift_differentiableAt (shift_den_pos hκ hb' hp).ne')
      (fun p hp v => shift_kleinMetric_fderiv hκ hb hw0 hp v v) hX hY
  apply le_antisymm (key a hw ha P Q hP hQ)
  have h := key (-a) hw' ha' _ _ (shift_mem_plane hκ hw hw0 hP) (shift_mem_plane hκ hw hw0 hQ)
  rwa [shift_neg_shift hκ hw hw0 hP, shift_neg_shift hκ hw hw0 hQ] at h
theorem rot_kleinDist {κ c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ (rot c s P) (rot c s Q) = kleinDist κ P Q := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by rw [← h]; ring
  have key : ∀ s' : ℝ, c ^ 2 + s' ^ 2 = 1 → ∀ X Y : ℝ × ℝ,
      X ∈ plane κ → Y ∈ plane κ → kleinDist κ (rot c s' X) (rot c s' Y) ≤ kleinDist κ X Y := by
    intro s' hs' X Y hX hY
    have hrot : ContDiff ℝ 1 (rot c s') := by
      unfold rot
      fun_prop
    exact kleinDist_map_le hrot.contDiffOn (fun p hp => (rot_mem_plane hs').mpr hp)
      (fun p _ => hrot.differentiable one_ne_zero p)
      (fun p _ v => rot_kleinMetric_fderiv hs' κ p v v) hX hY
  apply le_antisymm (key s h P Q hP hQ)
  have hh := key (-s) h' _ _ ((rot_mem_plane h).mpr hP) ((rot_mem_plane h).mpr hQ)
  rwa [rot_rot_neg h, rot_rot_neg h] at hh
@[expose] noncomputable def axisDist (κ x : ℝ) : ℝ := arsinh (√(-κ) * x / √(1 + κ * x ^ 2)) / √(-κ)
theorem axisDist_zero (κ : ℝ) : axisDist κ 0 = 0 := by
  simp [axisDist]
theorem hasDerivAt_axisDist {κ x : ℝ} (hκ : κ < 0) (hx : 0 < 1 + κ * x ^ 2) :
    HasDerivAt (axisDist κ) (1 / (1 + κ * x ^ 2)) x := by
  have hs : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have hs2 : √(-κ) ^ 2 = -κ := sq_sqrt (neg_nonneg.mpr hκ.le)
  have hq : 0 < √(1 + κ * x ^ 2) := sqrt_pos.mpr hx
  have hq2 : √(1 + κ * x ^ 2) ^ 2 = 1 + κ * x ^ 2 := sq_sqrt hx.le
  have hb : HasDerivAt (fun y : ℝ => 1 + κ * y ^ 2) (2 * κ * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul κ).const_add 1
    convert! this using 1
    norm_num
    try ring
  have hu := ((hasDerivAt_id' x).const_mul (√(-κ))).fun_div (hb.sqrt hx.ne') hq.ne'
  have ha := hu.arsinh.div_const (√(-κ))
  have h1u : 1 + (√(-κ) * x / √(1 + κ * x ^ 2)) ^ 2 = (1 / √(1 + κ * x ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, hs2, hq2]
    field_simp
    ring
  have hsq1 : √(1 + (√(-κ) * x / √(1 + κ * x ^ 2)) ^ 2) = 1 / √(1 + κ * x ^ 2) := by
    rw [h1u, sqrt_sq (by positivity)]
  unfold axisDist
  convert! ha using 1
  rw [hsq1, smul_eq_mul]
  field_simp
  rw [hq2]
  ring
theorem axis_le_metric {κ : ℝ} (hκ : κ ≤ 0) {p : ℝ × ℝ} (hp : p ∈ plane κ) (v : ℝ × ℝ) :
    1 / (1 + κ * p.1 ^ 2) * v.1 ≤ √(kleinMetric κ p v v) := by
  have hB := mem_plane.mp hp
  have hBc : 1 + κ * (p.1 ^ 2 + p.2 ^ 2) ≤ 1 + κ * p.1 ^ 2 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ (sq_nonneg p.2)]
  have hc : 0 < 1 + κ * p.1 ^ 2 := lt_of_lt_of_le hB hBc
  have key : (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v)
      - (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) * v.1 ^ 2
      = (κ * p.1 * p.2 * v.1 - (1 + κ * p.1 ^ 2) * v.2) ^ 2 := by
    simp only [cross]
    ring
  have hcN : (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) * v.1 ^ 2
      ≤ (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v) := by
    nlinarith [sq_nonneg (κ * p.1 * p.2 * v.1 - (1 + κ * p.1 ^ 2) * v.2)]
  have hN : 0 ≤ (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v) :=
    le_trans (mul_nonneg hB.le (sq_nonneg _)) hcN
  have hsq : (1 / (1 + κ * p.1 ^ 2) * v.1) ^ 2 ≤ kleinMetric κ p v v := by
    unfold kleinMetric
    rw [show (1 / (1 + κ * p.1 ^ 2) * v.1) ^ 2 = v.1 ^ 2 / (1 + κ * p.1 ^ 2) ^ 2 by
        rw [mul_pow, div_pow, one_pow, one_div, inv_mul_eq_div],
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcN hB.le, mul_le_mul_of_nonneg_right hBc hN]
  exact (le_abs_self _).trans (abs_le_sqrt hsq)
theorem axisDist_sub_le_kleinLength {κ : ℝ} (hκ : κ < 0) {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ}
    (h : IsKleinPath κ γ P Q) : axisDist κ Q.1 - axisDist κ P.1 ≤ kleinLength κ γ := by
  obtain ⟨hγ, hmaps, h0, h1⟩ := h
  have hx : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + κ * (γ t).1 ^ 2 := fun t ht => by
    have := mem_plane.mp (hmaps ht)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ.le (sq_nonneg (γ t).2)]
  have hcont : ContinuousOn (fun t => axisDist κ (γ t).1) (Icc 0 1) := fun t ht =>
    ContinuousAt.comp_continuousWithinAt (f := fun t => (γ t).1)
      (hasDerivAt_axisDist hκ (hx t ht)).continuousAt (hγ.continuousOn t ht).fst
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun t => axisDist κ (γ t).1)
      (1 / (1 + κ * (γ t).1 ^ 2) * (derivWithin γ (Icc 0 1) t).1) (Ioi t) t := by
    intro t ht
    have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd : HasDerivAt γ (derivWithin γ (Icc 0 1) t) t := by
      rw [derivWithin_of_mem_nhds hmem]
      exact ((hγ.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).differentiableAt
        hmem).hasDerivAt
    have hd1 : HasDerivAt (fun t => (γ t).1) (derivWithin γ (Icc 0 1) t).1 t := by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hd
      exact this
    exact ((hasDerivAt_axisDist hκ (hx t (Ioo_subset_Icc_self ht))).comp t hd1).hasDerivWithinAt
  have hint := (kleinLength_integrand_continuousOn ⟨hγ, hmaps, h0, h1⟩).integrableOn_Icc
    (μ := MeasureTheory.volume)
  have hle : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / (1 + κ * (γ t).1 ^ 2) * (derivWithin γ (Icc 0 1) t).1
      ≤ √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t) (derivWithin γ (Icc 0 1) t)) :=
    fun t ht => axis_le_metric hκ.le (hmaps (Ioo_subset_Icc_self ht)) _
  have := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le zero_le_one hcont hderiv hint hle
  simp only [h0, h1] at this
  exact this
theorem axis_isKleinPath {κ r : ℝ} (hκ : κ ≤ 0) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    IsKleinPath κ (fun t => (t * r, 0)) (0, 0) (r, 0) := by
  refine ⟨(by fun_prop : ContDiff ℝ 1 fun t : ℝ => (t * r, (0 : ℝ))).contDiffOn, ?_, by simp,
    by simp⟩
  intro t ht
  have hr' := mem_plane.mp hr
  simp only at hr'
  rw [mem_plane]
  simp only
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg r), mul_nonpos_of_nonpos_of_nonneg hκ
    (sq_nonneg r)]
theorem axis_kleinLength {κ r : ℝ} (hκ : κ < 0) (hr0 : 0 ≤ r) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    kleinLength κ (fun t => (t * r, 0)) = axisDist κ r := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + κ * (t * r) ^ 2 := fun t ht => by
    have := mem_plane.mp ((axis_isKleinPath hκ.le hr).2.1 ht)
    simp only at this
    linarith
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t = (r, 0) := fun t ht =>
    (((hasDerivAt_mul_const r).prodMk (hasDerivAt_const t (0 : ℝ))).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)
  have hint : ∀ t ∈ uIcc (0 : ℝ) 1,
      √(kleinMetric κ (t * r, 0) (derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t)
        (derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t))
      = 1 / (1 + κ * (t * r) ^ 2) * r := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [hderiv t ht]
    have hp := hpos t ht
    have e : kleinMetric κ (t * r, 0) (r, 0) (r, 0) = (1 / (1 + κ * (t * r) ^ 2) * r) ^ 2 := by
      simp only [kleinMetric, cross]
      field_simp
      ring
    rw [e, sqrt_sq (by positivity)]
  unfold kleinLength
  rw [intervalIntegral.integral_congr hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => axisDist κ (t * r))]
  · simp [axisDist_zero]
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hasDerivAt_axisDist hκ (hpos t ht)).comp t (hasDerivAt_mul_const r)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply ContinuousOn.mul _ continuousOn_const
    exact ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => (hpos t ht).ne')
theorem kleinDist_axis {κ r : ℝ} (hκ : κ < 0) (hr0 : 0 ≤ r) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    kleinDist κ (0, 0) (r, 0) = axisDist κ r := by
  apply le_antisymm
  · rw [← axis_kleinLength hκ hr0 hr]
    exact csInf_le (kleinDist_bddBelow κ _ _) ⟨_, axis_isKleinPath hκ.le hr, rfl⟩
  · apply le_csInf (kleinDist_nonempty (zero_mem_plane κ) hr)
    rintro _ ⟨γ, hγ, rfl⟩
    have := axisDist_sub_le_kleinLength hκ hγ
    simpa [axisDist_zero] using this
theorem exists_rot_to_axis (Q : ℝ × ℝ) :
    ∃ c s r : ℝ, c ^ 2 + s ^ 2 = 1 ∧ 0 ≤ r ∧ rot c s Q = (r, 0) := by
  by_cases h0 : Q.1 ^ 2 + Q.2 ^ 2 = 0
  · have h1 : Q.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg Q.2])
    have h2 : Q.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg Q.1])
    exact ⟨1, 0, 0, by norm_num, le_rfl, by simp [rot, h1, h2]⟩
  · have hpos : 0 < Q.1 ^ 2 + Q.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = Q.1 ^ 2 + Q.2 ^ 2 :=
      ⟨√(Q.1 ^ 2 + Q.2 ^ 2), sqrt_pos.mpr hpos, sq_sqrt hpos.le⟩
    refine ⟨Q.1 / r, -Q.2 / r, r, ?_, hr0.le, ?_⟩
    · field_simp
      linear_combination -hr2
    · apply Prod.ext
      · simp only [rot]
        field_simp
        linear_combination -hr2
      · simp only [rot]
        ring
theorem kleinDist_eq_arsinh {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ P Q = arsinh (√(-κ * apart κ P Q)) / √(-κ) := by
  obtain ⟨c, s, a, w, hcs, hw, hw0, hPc⟩ := exists_motion_to_centre hP
  have hrP : rot c s P ∈ plane κ := (rot_mem_plane hcs).mpr hP
  have hrQ : rot c s Q ∈ plane κ := (rot_mem_plane hcs).mpr hQ
  have hQ1 : shift κ a w (rot c s Q) ∈ plane κ := shift_mem_plane hκ.le hw hw0.ne' hrQ
  obtain ⟨c2, s2, r, hcs2, hr0, hQ2⟩ := exists_rot_to_axis (shift κ a w (rot c s Q))
  have hr : (r, (0 : ℝ)) ∈ plane κ := hQ2 ▸ (rot_mem_plane hcs2).mpr hQ1
  have hrot0 : rot c2 s2 ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [rot]
  have hd : kleinDist κ P Q = kleinDist κ (0, 0) (r, 0) :=
    calc kleinDist κ P Q = kleinDist κ (rot c s P) (rot c s Q) := (rot_kleinDist hcs hP hQ).symm
      _ = kleinDist κ (shift κ a w (rot c s P)) (shift κ a w (rot c s Q)) :=
        (shift_kleinDist hκ.le hw hw0.ne' hrP hrQ).symm
      _ = kleinDist κ (rot c2 s2 (0, 0)) (rot c2 s2 (shift κ a w (rot c s Q))) := by
        rw [hPc, rot_kleinDist hcs2 (zero_mem_plane κ) hQ1]
      _ = kleinDist κ (0, 0) (r, 0) := by rw [hrot0, hQ2]
  have ha : apart κ P Q = r ^ 2 / (1 + κ * r ^ 2) :=
    calc apart κ P Q = apart κ (rot c s P) (rot c s Q) := (rot_apart hcs κ P Q).symm
      _ = apart κ (shift κ a w (rot c s P)) (shift κ a w (rot c s Q)) :=
        (shift_apart_plane hκ.le hw hw0.ne' hrP hrQ).symm
      _ = apart κ (rot c2 s2 (0, 0)) (rot c2 s2 (shift κ a w (rot c s Q))) := by
        rw [hPc, rot_apart hcs2]
      _ = r ^ 2 / (1 + κ * r ^ 2) := by rw [hrot0, hQ2, apart_centre]
  have hr1 : 0 < 1 + κ * r ^ 2 := by
    have := mem_plane.mp hr
    simp only at this
    linarith
  rw [hd, kleinDist_axis hκ hr0 hr, ha, axisDist, sqrt_mul (neg_nonneg.mpr hκ.le),
    sqrt_div' _ hr1.le, sqrt_sq hr0, mul_div_assoc]
theorem apart_eq_sinh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : apart κ P Q = sinh (√(-κ) * kleinDist κ P Q) ^ 2 / (-κ) := by
  have hs : √(-κ) ≠ 0 := (sqrt_pos.mpr (neg_pos.mpr hκ)).ne'
  have ha : 0 ≤ apart κ P Q := by
    rcases eq_or_ne P Q with rfl | h
    · rw [apart_self]
    · exact (apart_pos hP hQ h).le
  have e : √(-κ) * (arsinh (√(-κ * apart κ P Q)) / √(-κ)) = arsinh (√(-κ * apart κ P Q)) := by
    field_simp
  rw [kleinDist_eq_arsinh hκ hP hQ, e, sinh_arsinh, sq_sqrt (mul_nonneg (neg_nonneg.mpr hκ.le) ha)]
  field_simp [hκ.ne]
end Distance
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section Congruence
open Set Real
theorem apart_eq_kleinInner (κ : ℝ) (P Q : ℝ × ℝ) :
    apart κ P Q = kleinInner κ P Q Q
      / ((1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  simp only [apart, kleinInner, cross]
  ring
theorem one_add_dot_pos {κ : ℝ} (hκ : κ ≤ 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : 0 < 1 + κ * (P.1 * Q.1 + P.2 * Q.2) := by
  have hP' := mem_plane.mp hP
  have hQ' := mem_plane.mp hQ
  have hcs : (P.1 * Q.1 + P.2 * Q.2) ^ 2 ≤ (P.1 ^ 2 + P.2 ^ 2) * (Q.1 ^ 2 + Q.2 ^ 2) := by
    nlinarith [sq_nonneg (P.1 * Q.2 - P.2 * Q.1)]
  have h1 : 0 ≤ -κ * (P.1 ^ 2 + P.2 ^ 2) := mul_nonneg (neg_nonneg.mpr hκ) (by positivity)
  have h2 : 0 ≤ -κ * (Q.1 ^ 2 + Q.2 ^ 2) := mul_nonneg (neg_nonneg.mpr hκ) (by positivity)
  have hlt : (κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2 < 1 := by
    calc (κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2 = κ ^ 2 * (P.1 * Q.1 + P.2 * Q.2) ^ 2 := by ring
      _ ≤ κ ^ 2 * ((P.1 ^ 2 + P.2 ^ 2) * (Q.1 ^ 2 + Q.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg κ)
      _ = (-κ * (P.1 ^ 2 + P.2 ^ 2)) * (-κ * (Q.1 ^ 2 + Q.2 ^ 2)) := by ring
      _ < 1 * 1 := by
        apply mul_lt_mul'' _ _ h1 h2 <;> linarith
      _ = 1 := one_mul 1
  nlinarith [hlt]
theorem kleinDist_nonneg {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    0 ≤ kleinDist κ P Q :=
  le_csInf (kleinDist_nonempty hP hQ) (by rintro _ ⟨γ, -, rfl⟩; exact kleinLength_nonneg κ γ)
theorem kleinDist_comm {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ P Q = kleinDist κ Q P := by
  rw [kleinDist_eq_arsinh hκ hP hQ, kleinDist_eq_arsinh hκ hQ hP, apart_comm]
theorem kleinDist_pos {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) (hPQ : P ≠ Q) : 0 < kleinDist κ P Q := by
  rw [kleinDist_eq_arsinh hκ hP hQ]
  apply div_pos _ (sqrt_pos.mpr (neg_pos.mpr hκ))
  rw [arsinh_pos_iff, sqrt_pos]
  exact mul_pos (neg_pos.mpr hκ) (apart_pos hP hQ hPQ)
theorem sinh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) :
    sinh (√(-κ) * kleinDist κ P Q) = √(-κ) * √(kleinInner κ P Q Q)
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  have hs : √(-κ) ≠ 0 := (sqrt_pos.mpr (neg_pos.mpr hκ)).ne'
  have e : √(-κ) * (arsinh (√(-κ * apart κ P Q)) / √(-κ)) = arsinh (√(-κ * apart κ P Q)) := by
    field_simp
  rw [kleinDist_eq_arsinh hκ hP hQ, e, sinh_arsinh, apart_eq_kleinInner,
    sqrt_mul (neg_nonneg.mpr hκ.le),
    sqrt_div' _ (mul_nonneg (mem_plane.mp hP).le (mem_plane.mp hQ).le),
    sqrt_mul (mem_plane.mp hP).le, mul_div_assoc]
theorem cosh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) :
    cosh (√(-κ) * kleinDist κ P Q) = (1 + κ * (P.1 * Q.1 + P.2 * Q.2))
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  have hBP := mem_plane.mp hP
  have hBQ := mem_plane.mp hQ
  have hsP : 0 < √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) := sqrt_pos.mpr hBP
  have hsQ : 0 < √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) := sqrt_pos.mpr hBQ
  have hk : √(-κ) ^ 2 = -κ := sq_sqrt (neg_nonneg.mpr hκ.le)
  have hg : √(kleinInner κ P Q Q) ^ 2 = kleinInner κ P Q Q := by
    rcases eq_or_ne Q P with rfl | h
    · have h0 : kleinInner κ Q Q Q = 0 := by
        simp only [kleinInner, cross]
        ring
      rw [h0]
      simp
    · exact sq_sqrt (kleinInner_self_pos hP h).le
  have hP2 : √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 = 1 + κ * (P.1 ^ 2 + P.2 ^ 2) := sq_sqrt hBP.le
  have hQ2 : √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2 = 1 + κ * (Q.1 ^ 2 + Q.2 ^ 2) := sq_sqrt hBQ.le
  have hpos : 0 < (1 + κ * (P.1 * Q.1 + P.2 * Q.2))
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) :=
    div_pos (one_add_dot_pos hκ.le hP hQ) (mul_pos hsP hsQ)
  rw [← pow_left_inj₀ (cosh_pos _).le hpos.le two_ne_zero, cosh_sq, sinh_kleinDist hκ hP hQ]
  have e1 : (√(-κ) * √(kleinInner κ P Q Q)
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))) ^ 2 + 1
      = (√(-κ) ^ 2 * √(kleinInner κ P Q Q) ^ 2
        + √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2)
          / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2) := by
    field_simp
  have e2 : ((1 + κ * (P.1 * Q.1 + P.2 * Q.2))
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))) ^ 2
      = (1 + κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2
          / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2) := by
    rw [div_pow, mul_pow]
  rw [e1, e2, hk, hg, hP2, hQ2]
  congr 1
  simp only [kleinInner, cross]
  ring
theorem kleinInner_gram (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinInner κ P A A * kleinInner κ P B B - kleinInner κ P A B ^ 2
      = (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (Dim.mk P A).side B ^ 2 := by
  simp only [kleinInner, Dim.side, Dim.dir, cross]
  ring
theorem cos_kleinAngle {κ : ℝ} {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ≠ P) (hB : B ≠ P) :
    cos (kleinAngle κ P A B)
      = kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B)) := by
  have hgA := kleinInner_self_pos hP hA
  have hgB := kleinInner_self_pos hP hB
  have hd : 0 < √(kleinInner κ P A A) * √(kleinInner κ P B B) :=
    mul_pos (sqrt_pos.mpr hgA) (sqrt_pos.mpr hgB)
  have habs : |kleinInner κ P A B| ≤ √(kleinInner κ P A A) * √(kleinInner κ P B B) := by
    rw [← sqrt_mul hgA.le]
    apply abs_le_sqrt
    have := kleinInner_gram κ P A B
    nlinarith [mul_nonneg (mem_plane.mp hP).le (sq_nonneg ((Dim.mk P A).side B))]
  have hx : |kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B))| ≤ 1 := by
    rw [abs_div, abs_of_pos hd, div_le_one hd]
    exact habs
  have h1 := abs_le.mp hx
  rw [kleinAngle, cos_arccos h1.1 h1.2]
theorem kleinAngle_eq_arccos_cos (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (cos (kleinAngle κ P A B)) :=
  (arccos_cos (arccos_nonneg _) (arccos_le_pi _)).symm
theorem law_of_cosines {κ : ℝ} (hκ : κ < 0) {P A B : ℝ × ℝ} (hP : P ∈ plane κ)
    (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hAP : A ≠ P) (hBP : B ≠ P) :
    cosh (√(-κ) * kleinDist κ P A) * cosh (√(-κ) * kleinDist κ P B)
        - cosh (√(-κ) * kleinDist κ A B)
      = sinh (√(-κ) * kleinDist κ P A) * sinh (√(-κ) * kleinDist κ P B)
        * cos (kleinAngle κ P A B) := by
  have hsP := sqrt_pos.mpr (mem_plane.mp hP)
  have hsA := sqrt_pos.mpr (mem_plane.mp hA)
  have hsB := sqrt_pos.mpr (mem_plane.mp hB)
  have hgA := sqrt_pos.mpr (kleinInner_self_pos hP hAP)
  have hgB := sqrt_pos.mpr (kleinInner_self_pos hP hBP)
  have hL : cosh (√(-κ) * kleinDist κ P A) * cosh (√(-κ) * kleinDist κ P B)
        - cosh (√(-κ) * kleinDist κ A B)
      = ((1 + κ * (P.1 * A.1 + P.2 * A.2)) * (1 + κ * (P.1 * B.1 + P.2 * B.2))
          - √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * (1 + κ * (A.1 * B.1 + A.2 * B.2)))
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (B.1 ^ 2 + B.2 ^ 2))) := by
    rw [cosh_kleinDist hκ hP hA, cosh_kleinDist hκ hP hB, cosh_kleinDist hκ hA hB]
    field_simp
  have hR : sinh (√(-κ) * kleinDist κ P A) * sinh (√(-κ) * kleinDist κ P B)
        * cos (kleinAngle κ P A B)
      = √(-κ) ^ 2 * kleinInner κ P A B
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (B.1 ^ 2 + B.2 ^ 2))) := by
    rw [sinh_kleinDist hκ hP hA, sinh_kleinDist hκ hP hB, cos_kleinAngle hP hAP hBP]
    field_simp
  rw [hL, hR, sq_sqrt (neg_nonneg.mpr hκ.le), sq_sqrt (mem_plane.mp hP).le]
  congr 1
  simp only [kleinInner, cross]
  ring
@[expose] def OnRay (O A X : ℝ × ℝ) : Prop := ∃ t : ℝ, 0 < t ∧ X = (Dim.mk O A).pt t
@[expose] def SameSide (O A X Y : ℝ × ℝ) : Prop := 0 < (Dim.mk O A).side X * (Dim.mk O A).side Y
theorem kleinAngle_comm (κ : ℝ) (P A B : ℝ × ℝ) : kleinAngle κ P A B = kleinAngle κ P B A := by
  have h : kleinInner κ P A B = kleinInner κ P B A := by
    simp only [kleinInner]
    ring
  rw [kleinAngle, kleinAngle, h, mul_comm (√(kleinInner κ P A A))]
theorem kleinAngle_onRay {κ : ℝ} {P A B A' B' : ℝ × ℝ} (hA : OnRay P A A') (hB : OnRay P B B') :
    kleinAngle κ P A' B' = kleinAngle κ P A B := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  have e1 : kleinInner κ P ((Dim.mk P A).pt s) ((Dim.mk P B).pt t)
      = 1 * s * t * kleinInner κ P A B := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have e2 : kleinInner κ P ((Dim.mk P A).pt s) ((Dim.mk P A).pt s)
      = 1 * s ^ 2 * kleinInner κ P A A := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have e3 : kleinInner κ P ((Dim.mk P B).pt t) ((Dim.mk P B).pt t)
      = 1 * t ^ 2 * kleinInner κ P B B := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  rw [kleinAngle, e1, e2, e3, kleinAngle_aux one_pos (mul_pos hs ht)]
  rfl
theorem side_angle_side {κ : ℝ} (hκ : κ < 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hE : E ∈ plane κ)
    (hF : F ∈ plane κ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hDE : D ≠ E) (hDF : D ≠ F)
    (hEF : E ≠ F) (h1 : kleinDist κ A B = kleinDist κ D E)
    (h2 : kleinDist κ A C = kleinDist κ D F) (h3 : kleinAngle κ A B C = kleinAngle κ D E F) :
    kleinDist κ B C = kleinDist κ E F ∧ kleinAngle κ B A C = kleinAngle κ E D F ∧
      kleinAngle κ C A B = kleinAngle κ F D E := by
  have hk : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have lA := law_of_cosines hκ hA hB hC hAB.symm hAC.symm
  have lD := law_of_cosines hκ hD hE hF hDE.symm hDF.symm
  rw [h1, h2, h3] at lA
  have hcosh : cosh (√(-κ) * kleinDist κ B C) = cosh (√(-κ) * kleinDist κ E F) := by linarith
  have hnn : ∀ {X Y : ℝ × ℝ}, X ∈ plane κ → Y ∈ plane κ → 0 ≤ √(-κ) * kleinDist κ X Y :=
    fun hX hY => mul_nonneg hk.le (kleinDist_nonneg hX hY)
  have hBCEF : kleinDist κ B C = kleinDist κ E F := by
    have h := le_antisymm (cosh_le_cosh.mp hcosh.le) (cosh_le_cosh.mp hcosh.ge)
    rw [abs_of_nonneg (hnn hB hC), abs_of_nonneg (hnn hE hF)] at h
    exact mul_left_cancel₀ hk.ne' h
  have hsinh : ∀ {X Y : ℝ × ℝ}, X ∈ plane κ → Y ∈ plane κ → X ≠ Y →
      0 < sinh (√(-κ) * kleinDist κ X Y) :=
    fun hX hY hXY => sinh_pos_iff.mpr (mul_pos hk (kleinDist_pos hκ hX hY hXY))
  have angle_eq : ∀ {P Q R P' Q' R' : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ →
      P' ∈ plane κ → Q' ∈ plane κ → R' ∈ plane κ → Q ≠ P → R ≠ P → Q' ≠ P' → R' ≠ P' →
      kleinDist κ P Q = kleinDist κ P' Q' → kleinDist κ P R = kleinDist κ P' R' →
      kleinDist κ Q R = kleinDist κ Q' R' → kleinAngle κ P Q R = kleinAngle κ P' Q' R' := by
    intro P Q R P' Q' R' hP hQ hR hP' hQ' hR' hQP hRP hQP' hRP' e1 e2 e3
    have l := law_of_cosines hκ hP hQ hR hQP hRP
    have l' := law_of_cosines hκ hP' hQ' hR' hQP' hRP'
    rw [e1, e2, e3] at l
    have hpos := mul_pos (hsinh hP' hQ' hQP'.symm) (hsinh hP' hR' hRP'.symm)
    have hcos : cos (kleinAngle κ P Q R) = cos (kleinAngle κ P' Q' R') :=
      mul_left_cancel₀ hpos.ne' (by linarith)
    rw [kleinAngle_eq_arccos_cos κ P Q R, kleinAngle_eq_arccos_cos κ P' Q' R', hcos]
  refine ⟨hBCEF, ?_, ?_⟩
  · exact angle_eq hB hA hC hE hD hF hAB hBC.symm hDE hEF.symm
      (by rw [kleinDist_comm hκ hB hA, kleinDist_comm hκ hE hD, h1]) hBCEF h2
  · exact angle_eq hC hA hB hF hD hE hAC hBC hDF hEF
      (by rw [kleinDist_comm hκ hC hA, kleinDist_comm hκ hF hD, h2])
      (by rw [kleinDist_comm hκ hC hB, kleinDist_comm hκ hF hE, hBCEF]) h1
theorem kleinDist_add_of_between {κ : ℝ} (hκ : κ < 0) {A B C : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (h : Between A B C) :
    B ∈ plane κ ∧ kleinDist κ A C = kleinDist κ A B + kleinDist κ B C := by
  obtain ⟨-, u, hu0, hu1, rfl⟩ := h
  have hB : (Dim.mk A C).pt u ∈ plane κ := plane_convex κ hA hC hu0.le hu1.le
  refine ⟨hB, ?_⟩
  have hk : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have hsA := sqrt_pos.mpr (mem_plane.mp hA)
  have hsB := sqrt_pos.mpr (mem_plane.mp hB)
  have hsC := sqrt_pos.mpr (mem_plane.mp hC)
  have hgAB : kleinInner κ A ((Dim.mk A C).pt u) ((Dim.mk A C).pt u)
      = u ^ 2 * kleinInner κ A C C := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have hgBC : kleinInner κ ((Dim.mk A C).pt u) C C = (1 - u) ^ 2 * kleinInner κ A C C := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have hcB : u * (1 + κ * (((Dim.mk A C).pt u).1 * C.1 + ((Dim.mk A C).pt u).2 * C.2))
      + (1 - u) * (1 + κ * (A.1 * ((Dim.mk A C).pt u).1 + A.2 * ((Dim.mk A C).pt u).2))
      = 1 + κ * (((Dim.mk A C).pt u).1 ^ 2 + ((Dim.mk A C).pt u).2 ^ 2) := by
    simp only [Dim.pt]
    ring
  have hL : sinh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u))
        * cosh (√(-κ) * kleinDist κ ((Dim.mk A C).pt u) C)
      + cosh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u))
        * sinh (√(-κ) * kleinDist κ ((Dim.mk A C).pt u) C)
      = √(-κ) * √(kleinInner κ A C C)
        * (u * (1 + κ * (((Dim.mk A C).pt u).1 * C.1 + ((Dim.mk A C).pt u).2 * C.2))
          + (1 - u) * (1 + κ * (A.1 * ((Dim.mk A C).pt u).1 + A.2 * ((Dim.mk A C).pt u).2)))
        / (√(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (((Dim.mk A C).pt u).1 ^ 2 + ((Dim.mk A C).pt u).2 ^ 2)) ^ 2
          * √(1 + κ * (C.1 ^ 2 + C.2 ^ 2))) := by
    rw [sinh_kleinDist hκ hA hB, cosh_kleinDist hκ hB hC, cosh_kleinDist hκ hA hB,
      sinh_kleinDist hκ hB hC, hgAB, hgBC, sqrt_mul (sq_nonneg _), sqrt_mul (sq_nonneg _),
      sqrt_sq hu0.le, sqrt_sq (by linarith)]
    field_simp
  have hsum : sinh (√(-κ) * kleinDist κ A C) = sinh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u)
      + √(-κ) * kleinDist κ ((Dim.mk A C).pt u) C) := by
    have hBB := (mem_plane.mp hB).ne'
    rw [sinh_add, hL, hcB, sq_sqrt (mem_plane.mp hB).le, sinh_kleinDist hκ hA hC]
    field_simp
  have := sinh_injective hsum
  rw [← mul_add] at this
  exact mul_left_cancel₀ hk.ne' this
theorem segment_addition {κ : ℝ} (hκ : κ < 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hF : F ∈ plane κ) (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : kleinDist κ A B = kleinDist κ D E)
    (h2 : kleinDist κ B C = kleinDist κ E F) : kleinDist κ A C = kleinDist κ D F := by
  rw [(kleinDist_add_of_between hκ hA hC hABC).2, (kleinDist_add_of_between hκ hD hF hDEF).2,
    h1, h2]
theorem apart_ray (κ : ℝ) (O D : ℝ × ℝ) (t : ℝ) :
    apart κ O ((Dim.mk O D).pt t) = t ^ 2 * kleinInner κ O D D
      / ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2))) := by
  rw [apart_eq_kleinInner]
  congr 1
  simp only [kleinInner, cross, Dim.pt]
  ring
theorem apart_ray_lt {κ : ℝ} (hκ : κ < 0) {O D : ℝ × ℝ} (hO : O ∈ plane κ) (hOD : O ≠ D)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (hXs : (Dim.mk O D).pt s ∈ plane κ)
    (hXt : (Dim.mk O D).pt t ∈ plane κ) :
    apart κ O ((Dim.mk O D).pt s) < apart κ O ((Dim.mk O D).pt t) := by
  have hG := kleinInner_self_pos hO hOD.symm
  have hBO := mem_plane.mp hO
  have hBs := mem_plane.mp hXs
  have hBt := mem_plane.mp hXt
  have h1 := one_add_dot_pos hκ.le hO hXs
  have h2 := one_add_dot_pos hκ.le hO hXt
  rw [apart_ray, apart_ray, div_lt_div_iff₀ (mul_pos hBO hBs) (mul_pos hBO hBt)]
  have key : t ^ 2 * kleinInner κ O D D * ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt s).1 ^ 2 + ((Dim.mk O D).pt s).2 ^ 2)))
      - s ^ 2 * kleinInner κ O D D * ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2)))
      = kleinInner κ O D D * (1 + κ * (O.1 ^ 2 + O.2 ^ 2)) * ((t - s)
        * (s * (1 + κ * (O.1 * ((Dim.mk O D).pt t).1 + O.2 * ((Dim.mk O D).pt t).2))
          + t * (1 + κ * (O.1 * ((Dim.mk O D).pt s).1 + O.2 * ((Dim.mk O D).pt s).2)))) := by
    simp only [Dim.pt]
    ring
  have hpos := mul_pos (mul_pos hG hBO) (mul_pos (sub_pos.mpr hst)
    (add_pos (mul_pos hs h2) (mul_pos (hs.trans hst) h1)))
  linarith
theorem exists_onRay_apart {κ : ℝ} (hκ : κ < 0) {O D : ℝ × ℝ} (hO : O ∈ plane κ) (hOD : O ≠ D)
    {α : ℝ} (hα : 0 < α) :
    ∃ t : ℝ, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ apart κ O ((Dim.mk O D).pt t) = α := by
  have hG := kleinInner_self_pos hO hOD.symm
  have hBO := mem_plane.mp hO
  have hnk : 0 < -κ := neg_pos.mpr hκ
  have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
    have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hOD
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    exact sq_add_sq_pos hne
  set V := (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 with hVdef
  set W := O.1 * (D.1 - O.1) + O.2 * (D.2 - O.2) with hWdef
  set T := (2 * |W| + 1) / V + 1 / (-κ) with hTdef
  have hT1 : 1 / (-κ) ≤ T := by
    have : 0 ≤ (2 * |W| + 1) / V := div_nonneg (by positivity) hV.le
    linarith
  have hT0 : 0 ≤ T := le_trans (one_div_pos.mpr hnk).le hT1
  have hTV : 2 * |W| + 1 ≤ T * V := by
    rw [hTdef, add_mul, div_mul_cancel₀ _ hV.ne']
    have : 0 ≤ 1 / (-κ) * V := mul_nonneg (one_div_pos.mpr hnk).le hV.le
    linarith
  have hXT : 1 / (-κ) ≤ ((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2 := by
    have e : ((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2
        = (O.1 ^ 2 + O.2 ^ 2) + 2 * (T * W) + T * (T * V) := by
      simp only [Dim.pt, hWdef, hVdef]
      ring
    rw [e]
    have ha : -(T * |W|) ≤ T * W := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le W) hT0
      linarith
    have hb : 0 ≤ T * (T * V - 2 * |W| - 1) := mul_nonneg hT0 (by linarith)
    nlinarith only [ha, hb, hT1, sq_nonneg O.1, sq_nonneg O.2]
  have hBT : 1 + κ * (((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2) ≤ 0 := by
    have h := mul_le_mul_of_nonpos_left hXT hκ.le
    have e : κ * (1 / (-κ)) = -1 := by
      rw [mul_one_div, div_neg, div_self hκ.ne]
    linarith
  set f : ℝ → ℝ := fun t => t ^ 2 * kleinInner κ O D D - α
    * (1 + κ * (O.1 ^ 2 + O.2 ^ 2))
    * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2)) with hf
  have hfc : Continuous f := by
    simp only [hf, Dim.pt]
    fun_prop
  have hf0 : f 0 < 0 := by
    have e : f 0 = -(α * (1 + κ * (O.1 ^ 2 + O.2 ^ 2)) ^ 2) := by
      simp only [hf, Dim.pt]
      ring
    rw [e]
    have := mul_pos hα (pow_pos hBO 2)
    linarith
  have hfT : 0 ≤ f T := by
    simp only [hf]
    have := mul_nonneg (mul_nonneg hα.le hBO.le) (neg_nonneg.mpr hBT)
    nlinarith only [this, mul_nonneg (sq_nonneg T) hG.le]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hT0 hfc.continuousOn ⟨hf0.le, hfT⟩
  have ht0 : 0 < t := by
    rcases ht.1.eq_or_lt with h | h
    · rw [← h] at hft
      linarith
    · exact h
  simp only [hf] at hft
  have hBt : 0 < 1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2) := by
    by_contra h
    have h := not_lt.mp h
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hα hBO).le h
    nlinarith only [hft, this, mul_pos (pow_pos ht0 2) hG]
  have hXt : (Dim.mk O D).pt t ∈ plane κ := mem_plane.mpr hBt
  have hap : apart κ O ((Dim.mk O D).pt t) = α := by
    rw [apart_ray, div_eq_iff (mul_pos hBO hBt).ne']
    linear_combination hft
  exact ⟨t, ht0, hXt, hap⟩
theorem segment_construction {κ : ℝ} (hκ : κ < 0) {A B O D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hO : O ∈ plane κ) (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane κ ∧ OnRay O D X ∧ kleinDist κ A B = kleinDist κ O X := by
  obtain ⟨t, ht0, hXt, hap⟩ := exists_onRay_apart hκ hO hOD (apart_pos hA hB hAB)
  refine ⟨(Dim.mk O D).pt t, ⟨hXt, ⟨t, ht0, rfl⟩, ?_⟩, ?_⟩
  · rw [kleinDist_eq_arsinh hκ hA hB, kleinDist_eq_arsinh hκ hO hXt, hap]
  · rintro Y ⟨hY, ⟨s, hs, rfl⟩, hYd⟩
    have hapY : apart κ O ((Dim.mk O D).pt s) = apart κ A B := by
      rw [apart_eq_sinh_kleinDist hκ hO hY, ← hYd, ← apart_eq_sinh_kleinDist hκ hA hB]
    rcases lt_trichotomy s t with h | rfl | h
    · exact absurd (hapY.trans hap.symm) (apart_ray_lt hκ hO hOD hs h hY hXt).ne
    · rfl
    · exact absurd (hap.trans hapY.symm) (apart_ray_lt hκ hO hOD ht0 h hXt hY).ne
theorem sin_kleinAngle_pos {κ : ℝ} {A B C : ℝ × ℝ} (hA : A ∈ plane κ)
    (hABC : (Dim.mk A B).side C ≠ 0) : 0 < sin (kleinAngle κ A B C) := by
  have hBA : B ≠ A := by
    rintro rfl
    apply hABC
    simp [Dim.side, Dim.dir, cross]
  have hCA : C ≠ A := by
    rintro rfl
    apply hABC
    simp [Dim.side, Dim.dir, cross]
  have hgB := kleinInner_self_pos hA hBA
  have hgC := kleinInner_self_pos hA hCA
  have h0 : 0 ≤ sin (kleinAngle κ A B C) :=
    sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  have hc2 : cos (kleinAngle κ A B C) ^ 2 < 1 := by
    rw [cos_kleinAngle hA hBA hCA, div_pow, mul_pow, sq_sqrt hgB.le, sq_sqrt hgC.le,
      div_lt_one (mul_pos hgB hgC)]
    have := kleinInner_gram κ A B C
    have : 0 < (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) * (Dim.mk A B).side C ^ 2 :=
      mul_pos (mem_plane.mp hA) (by positivity)
    linarith
  have hs := sin_sq_add_cos_sq (kleinAngle κ A B C)
  rcases h0.eq_or_lt with h | h
  · rw [← h] at hs
    linarith
  · exact h
theorem angle_construction {κ : ℝ} {A B C D F G : ℝ × ℝ} (hA : A ∈ plane κ)
    (hD : D ∈ plane κ) (hABC : (Dim.mk A B).side C ≠ 0) (hDF : D ≠ F)
    (hG : (Dim.mk D F).side G ≠ 0) :
    (∃ E, E ∈ plane κ ∧ SameSide D F E G ∧ kleinAngle κ D F E = kleinAngle κ A B C) ∧
    ∀ E E', E ∈ plane κ → SameSide D F E G → kleinAngle κ D F E = kleinAngle κ A B C →
      E' ∈ plane κ → SameSide D F E' G → kleinAngle κ D F E' = kleinAngle κ A B C →
      OnRay D E E' := by
  have hsin := sin_kleinAngle_pos hA hABC
  have hgU := kleinInner_self_pos hD hDF.symm
  have hBD := mem_plane.mp hD
  refine ⟨?_, ?_⟩
  · -- the direction perpendicular to `DF` in Klein's metric, and the side of `G`
    set θ := kleinAngle κ A B C with hθ
    set sG := (Dim.mk D F).side G with hsG
    set σ := sG / |sG| with hσ
    have hσ2 : σ ^ 2 = 1 := by
      rw [hσ, div_pow, sq_abs, div_self (pow_ne_zero 2 hG)]
    have hσG : 0 < σ * sG := by
      rw [hσ, div_mul_eq_mul_div, ← sq, ← sq_abs, sq, mul_self_div_self]
      exact abs_pos.mpr hG
    set sB := √(1 + κ * (D.1 ^ 2 + D.2 ^ 2)) with hsB
    have hsB2 : sB ^ 2 = 1 + κ * (D.1 ^ 2 + D.2 ^ 2) := sq_sqrt hBD.le
    have hsBp : 0 < sB := sqrt_pos.mpr hBD
    set c := D.1 * F.2 - D.2 * F.1 with hc
    set v : ℝ × ℝ := (cos θ * sB * (F.1 - D.1) + σ * sin θ * (-(F.2 - D.2) - κ * c * D.1),
      cos θ * sB * (F.2 - D.2) + σ * sin θ * ((F.1 - D.1) - κ * c * D.2)) with hv
    obtain ⟨ε, hε, hE⟩ := plane_open_forward κ (Dim.mk D (D.1 + v.1, D.2 + v.2)) hD
    set E := (Dim.mk D (D.1 + v.1, D.2 + v.2)).pt ε with hEdef
    have hN : kleinInner κ D F E = ε * cos θ * sB * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, cross, Dim.pt]
      ring
    have hNN : kleinInner κ D E E = ε ^ 2 * (cos θ ^ 2 * sB ^ 2
        + σ ^ 2 * sin θ ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2))) * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, cross, Dim.pt]
      ring
    have hside : (Dim.mk D F).side E = ε * σ * sin θ * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, Dim.side, Dim.dir, cross, Dim.pt]
      ring
    have hNN' : kleinInner κ D E E
        = ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F := by
      rw [hNN, hsB2, hσ2]
      linear_combination (ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F)
        * sin_sq_add_cos_sq θ
    have hsq : √(ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F)
        = ε * sB * √(kleinInner κ D F F) := by
      rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_sq hε.le]
    have hg2 : √(kleinInner κ D F F) * √(kleinInner κ D F F) = kleinInner κ D F F :=
      mul_self_sqrt hgU.le
    have hx : ε * cos θ * sB * kleinInner κ D F F
        / (√(kleinInner κ D F F) * (ε * sB * √(kleinInner κ D F F))) = cos θ := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-(ε * cos θ * sB)) * hg2
    refine ⟨E, hE, ?_, ?_⟩
    · change 0 < (Dim.mk D F).side E * sG
      rw [hside]
      have := mul_pos (mul_pos (mul_pos hε hsin) hgU) hσG
      linarith [this]
    · have hθ0 : 0 ≤ θ := arccos_nonneg _
      have hθπ : θ ≤ π := arccos_le_pi _
      rw [kleinAngle, hN, hNN', hsq, hx, arccos_cos hθ0 hθπ]
  · intro E₁ E₂ hE₁ hs₁ ha₁ hE₂ hs₂ ha₂
    have hs12 : 0 < (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ := by
      have h := mul_pos hs₁ hs₂
      have e : (Dim.mk D F).side E₁ * (Dim.mk D F).side G
          * ((Dim.mk D F).side E₂ * (Dim.mk D F).side G)
          = (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ * (Dim.mk D F).side G ^ 2 := by ring
      rw [e] at h
      exact (mul_pos_iff_of_pos_right (by positivity)).mp h
    have hs1 : (Dim.mk D F).side E₁ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hs12
      exact lt_irrefl 0 hs12
    have hE1D : E₁ ≠ D := by
      rintro rfl
      apply hs1
      simp [Dim.side, Dim.dir, cross]
    have hE2D : E₂ ≠ D := by
      rintro rfl
      apply (lt_irrefl (0 : ℝ))
      convert! hs12 using 1
      try simp [Dim.side, Dim.dir, cross]
    have hg1 := kleinInner_self_pos hD hE1D
    have hg2 := kleinInner_self_pos hD hE2D
    have hx : kleinInner κ D F E₁ / (√(kleinInner κ D F F) * √(kleinInner κ D E₁ E₁))
        = kleinInner κ D F E₂ / (√(kleinInner κ D F F) * √(kleinInner κ D E₂ E₂)) := by
      rw [← cos_kleinAngle hD hDF.symm hE1D, ← cos_kleinAngle hD hDF.symm hE2D, ha₁, ha₂]
    rw [div_eq_div_iff (by positivity) (by positivity)] at hx
    have hN : kleinInner κ D F E₁ * √(kleinInner κ D E₂ E₂)
        = kleinInner κ D F E₂ * √(kleinInner κ D E₁ E₁) := by
      apply mul_left_cancel₀ (sqrt_pos.mpr hgU).ne'
      linear_combination hx
    have hsq : kleinInner κ D F E₁ ^ 2 * kleinInner κ D E₂ E₂
        = kleinInner κ D F E₂ ^ 2 * kleinInner κ D E₁ E₁ := by
      have h := congrArg (· ^ 2) hN
      simp only [mul_pow, sq_sqrt hg1.le, sq_sqrt hg2.le] at h
      exact h
    have hNN : 0 ≤ kleinInner κ D F E₁ * kleinInner κ D F E₂ := by
      have h : kleinInner κ D F E₁ * kleinInner κ D F E₂ * √(kleinInner κ D E₂ E₂)
          = kleinInner κ D F E₂ ^ 2 * √(kleinInner κ D E₁ E₁) := by
        linear_combination (kleinInner κ D F E₂) * hN
      have h' : 0 ≤ kleinInner κ D F E₁ * kleinInner κ D F E₂ * √(kleinInner κ D E₂ E₂) := by
        rw [h]
        positivity
      exact (mul_nonneg_iff_of_pos_right (sqrt_pos.mpr hg2)).mp h'
    have gram1 := kleinInner_gram κ D F E₁
    have gram2 := kleinInner_gram κ D F E₂
    have hmain : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂) ^ 2
        = (kleinInner κ D F E₂ * (Dim.mk D F).side E₁) ^ 2 := by
      apply mul_left_cancel₀ hBD.ne'
      linear_combination kleinInner κ D F F * hsq - kleinInner κ D F E₁ ^ 2 * gram2
        + kleinInner κ D F E₂ ^ 2 * gram1
    have hprod : 0 ≤ (kleinInner κ D F E₁ * (Dim.mk D F).side E₂)
        * (kleinInner κ D F E₂ * (Dim.mk D F).side E₁) := by
      have e : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂)
          * (kleinInner κ D F E₂ * (Dim.mk D F).side E₁)
          = kleinInner κ D F E₁ * kleinInner κ D F E₂
            * ((Dim.mk D F).side E₁ * (Dim.mk D F).side E₂) := by ring
      rw [e]
      exact mul_nonneg hNN hs12.le
    have heq : kleinInner κ D F E₁ * (Dim.mk D F).side E₂
        = kleinInner κ D F E₂ * (Dim.mk D F).side E₁ := by
      have h1 : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂
          - kleinInner κ D F E₂ * (Dim.mk D F).side E₁)
          * (kleinInner κ D F E₁ * (Dim.mk D F).side E₂
            + kleinInner κ D F E₂ * (Dim.mk D F).side E₁) = 0 := by
        linear_combination hmain
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · have ha : kleinInner κ D F E₁ * (Dim.mk D F).side E₂
            = -(kleinInner κ D F E₂ * (Dim.mk D F).side E₁) := by linarith
        rw [ha] at hprod
        have hb : kleinInner κ D F E₂ * (Dim.mk D F).side E₁ = 0 := by
          nlinarith only [hprod, sq_nonneg (kleinInner κ D F E₂ * (Dim.mk D F).side E₁)]
        rw [ha, hb]
        ring
    have hplucker : kleinInner κ D F F * (Dim.mk D E₁).side E₂
        = kleinInner κ D F E₁ * (Dim.mk D F).side E₂
          - kleinInner κ D F E₂ * (Dim.mk D F).side E₁ := by
      simp only [kleinInner, Dim.side, Dim.dir, cross]
      ring
    have hcross : (Dim.mk D E₁).side E₂ = 0 := by
      have h : kleinInner κ D F F * (Dim.mk D E₁).side E₂ = 0 := by
        rw [hplucker, heq, sub_self]
      exact (mul_eq_zero.mp h).resolve_left hgU.ne'
    have hv1 : ((E₁.1 - D.1, E₁.2 - D.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hE1D
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero hv1 hcross
    have h1 := congrArg Prod.fst hl
    have h2 := congrArg Prod.snd hl
    simp only [] at h1 h2
    have hs2l : (Dim.mk D F).side E₂ = l * (Dim.mk D F).side E₁ := by
      simp only [Dim.side, Dim.dir, cross]
      linear_combination (F.1 - D.1) * h2 - (F.2 - D.2) * h1
    have hl0 : 0 < l := by
      have h : 0 < l * (Dim.mk D F).side E₁ ^ 2 := by
        have e : l * (Dim.mk D F).side E₁ ^ 2
            = (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ := by
          rw [hs2l]
          ring
        rw [e]
        exact hs12
      exact (mul_pos_iff_of_pos_right (by positivity)).mp h
    refine ⟨l, hl0, Prod.ext ?_ ?_⟩
    · simp only [Dim.pt]
      linarith
    · simp only [Dim.pt]
      linarith
end Congruence
section Apart
open Real
theorem onRay_of_between {O A X : ℝ × ℝ} (h : X = A ∨ Between O X A ∨ Between O A X) :
    OnRay O A X := by
  rcases h with rfl | ⟨-, u, hu0, -, hu⟩ | ⟨-, u, hu0, -, hu⟩
  · exact ⟨1, one_pos, (Dim.pt_one (Dim.mk O X)).symm⟩
  · exact ⟨u, hu0, hu.symm⟩
  · refine ⟨1 / u, by positivity, ?_⟩
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.snd hu
    simp only [Dim.pt] at h1 h2
    apply Prod.ext
    · simp only [Dim.pt]
      rw [← h1]
      field_simp
      ring
    · simp only [Dim.pt]
      rw [← h2]
      field_simp
      ring
theorem between_of_onRay {O A X : ℝ × ℝ} (hOA : O ≠ A) (h : OnRay O A X) :
    X = A ∨ Between O X A ∨ Between O A X := by
  obtain ⟨t, ht, rfl⟩ := h
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  · exact Or.inr (Or.inl ⟨hOA, t, ht, h1, rfl⟩)
  · exact Or.inl (Dim.pt_one (Dim.mk O A))
  · refine Or.inr (Or.inr ⟨?_, 1 / t, by positivity, (div_lt_one ht).mpr h1, ?_⟩)
    · intro h
      apply hOA
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only [Dim.pt] at e1 e2
      have k1 : t * (A.1 - O.1) = 0 := by linarith
      have k2 : t * (A.2 - O.2) = 0 := by linarith
      apply Prod.ext
      · linarith [(mul_eq_zero.mp k1).resolve_left ht.ne']
      · linarith [(mul_eq_zero.mp k2).resolve_left ht.ne']
    · apply Prod.ext
      · simp only [Dim.pt]
        field_simp
        ring
      · simp only [Dim.pt]
        field_simp
        ring
theorem mem_plane_zero (p : ℝ × ℝ) : p ∈ plane (0 : ℝ) := by
  rw [plane_zero]
  trivial
theorem apart_zero_nonneg (P Q : ℝ × ℝ) : 0 ≤ apart 0 P Q := by
  rw [apart_zero_bound]
  positivity
theorem apart_zero_eq_kleinInner (P Q : ℝ × ℝ) : apart 0 P Q = kleinInner 0 P Q Q := by
  rw [apart_zero_bound]
  simp only [kleinInner, zero_mul, add_zero]
  ring
theorem euclid_segment_construction {A B O D : ℝ × ℝ} (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane (0 : ℝ) ∧ OnRay O D X ∧ apart 0 A B = apart 0 O X := by
  have hα : 0 < apart 0 A B := apart_pos (mem_plane_zero A) (mem_plane_zero B) hAB
  have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
    have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hOD
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    exact sq_add_sq_pos hne
  have hray : ∀ t : ℝ, apart 0 O ((Dim.mk O D).pt t)
      = t ^ 2 * ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := by
    intro t
    rw [apart_zero_bound]
    simp only [Dim.pt]
    ring
  have ht0 : 0 < √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) :=
    sqrt_pos.mpr (div_pos hα hV)
  have ht2 : √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2
      = apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := sq_sqrt (div_pos hα hV).le
  refine ⟨(Dim.mk O D).pt (√(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2))),
    ⟨mem_plane_zero _, ⟨_, ht0, rfl⟩, ?_⟩, ?_⟩
  · rw [hray, ht2, div_mul_cancel₀ _ hV.ne']
  · rintro Y ⟨-, ⟨s, hs, rfl⟩, hY⟩
    rw [hray] at hY
    have hs2 : s ^ 2 = √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2 := by
      rw [ht2, eq_div_iff hV.ne']
      linarith
    rw [(pow_left_inj₀ hs.le ht0.le two_ne_zero).mp hs2]
theorem euclid_sqrt_apart_add {A B C : ℝ × ℝ} (h : Between A B C) :
    √(apart 0 A C) = √(apart 0 A B) + √(apart 0 B C) := by
  obtain ⟨-, u, hu0, hu1, rfl⟩ := h
  have e1 : apart 0 A ((Dim.mk A C).pt u) = u ^ 2 * apart 0 A C := by
    rw [apart_zero_bound, apart_zero_bound]
    simp only [Dim.pt]
    ring
  have e2 : apart 0 ((Dim.mk A C).pt u) C = (1 - u) ^ 2 * apart 0 A C := by
    rw [apart_zero_bound, apart_zero_bound]
    simp only [Dim.pt]
    ring
  rw [e1, e2, sqrt_mul (sq_nonneg _), sqrt_mul (sq_nonneg _), sqrt_sq hu0.le,
    sqrt_sq (by linarith)]
  ring
theorem euclid_segment_addition {A B C D E F : ℝ × ℝ} (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : apart 0 A B = apart 0 D E) (h2 : apart 0 B C = apart 0 E F) :
    apart 0 A C = apart 0 D F := by
  have h := euclid_sqrt_apart_add hABC
  rw [h1, h2, ← euclid_sqrt_apart_add hDEF] at h
  exact (sqrt_inj (apart_zero_nonneg _ _) (apart_zero_nonneg _ _)).mp h
theorem euclid_law_of_cosines {A B C : ℝ × ℝ} (hB : B ≠ A) (hC : C ≠ A) :
    apart 0 B C = apart 0 A B + apart 0 A C
      - 2 * (√(apart 0 A B) * √(apart 0 A C)) * cos (kleinAngle 0 A B C) := by
  have hgB := sqrt_pos.mpr (kleinInner_self_pos (mem_plane_zero A) hB)
  have hgC := sqrt_pos.mpr (kleinInner_self_pos (mem_plane_zero A) hC)
  have e : apart 0 B C = kleinInner 0 A B B + kleinInner 0 A C C - 2 * kleinInner 0 A B C := by
    rw [apart_zero_bound]
    simp only [kleinInner, zero_mul, add_zero]
    ring
  rw [e, apart_zero_eq_kleinInner A B, apart_zero_eq_kleinInner A C,
    cos_kleinAngle (mem_plane_zero A) hB hC]
  field_simp
theorem euclid_sas {A B C D E F : ℝ × ℝ} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hDE : D ≠ E) (hDF : D ≠ F) (hEF : E ≠ F) (h1 : apart 0 A B = apart 0 D E)
    (h2 : apart 0 A C = apart 0 D F) (h3 : kleinAngle 0 A B C = kleinAngle 0 D E F) :
    apart 0 B C = apart 0 E F ∧ kleinAngle 0 B A C = kleinAngle 0 E D F ∧
      kleinAngle 0 C A B = kleinAngle 0 F D E := by
  have hBCEF : apart 0 B C = apart 0 E F := by
    rw [euclid_law_of_cosines hAB.symm hAC.symm, euclid_law_of_cosines hDE.symm hDF.symm, h1, h2,
      h3]
  have angle_eq : ∀ {P Q R P' Q' R' : ℝ × ℝ}, Q ≠ P → R ≠ P → Q' ≠ P' → R' ≠ P' →
      apart 0 P Q = apart 0 P' Q' → apart 0 P R = apart 0 P' R' →
      apart 0 Q R = apart 0 Q' R' → kleinAngle 0 P Q R = kleinAngle 0 P' Q' R' := by
    intro P Q R P' Q' R' hQ hR hQ' hR' e1 e2 e3
    have l := euclid_law_of_cosines hQ hR
    have l' := euclid_law_of_cosines hQ' hR'
    rw [e1, e2, e3] at l
    have hpos : 0 < 2 * (√(apart 0 P' Q') * √(apart 0 P' R')) := by
      have := sqrt_pos.mpr (apart_pos (mem_plane_zero P') (mem_plane_zero Q') hQ'.symm)
      have := sqrt_pos.mpr (apart_pos (mem_plane_zero P') (mem_plane_zero R') hR'.symm)
      positivity
    have hcos : cos (kleinAngle 0 P Q R) = cos (kleinAngle 0 P' Q' R') :=
      mul_left_cancel₀ hpos.ne' (by linarith)
    rw [kleinAngle_eq_arccos_cos 0 P Q R, kleinAngle_eq_arccos_cos 0 P' Q' R', hcos]
  refine ⟨hBCEF, ?_, ?_⟩
  · exact angle_eq hAB hBC.symm hDE hEF.symm (by rw [apart_comm, h1, apart_comm]) hBCEF h2
  · exact angle_eq hAC hBC hDF hEF (by rw [apart_comm, h2, apart_comm])
      (by rw [apart_comm, hBCEF, apart_comm]) h1
theorem apart_eq_iff_kleinDist_eq {κ : ℝ} (hκ : κ < 0) {A B C D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) :
    apart κ A B = apart κ C D ↔ kleinDist κ A B = kleinDist κ C D := by
  constructor
  · intro h
    rw [kleinDist_eq_arsinh hκ hA hB, kleinDist_eq_arsinh hκ hC hD, h]
  · intro h
    rw [apart_eq_sinh_kleinDist hκ hA hB, apart_eq_sinh_kleinDist hκ hC hD, h]
theorem segment_construction_apart {κ : ℝ} (hκ : κ ≤ 0) {A B O D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hO : O ∈ plane κ) (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane κ ∧ OnRay O D X ∧ apart κ A B = apart κ O X := by
  rcases hκ.lt_or_eq with h | rfl
  · obtain ⟨X, ⟨hX, hray, hd⟩, huniq⟩ := segment_construction h hA hB hO hAB hOD
    exact ⟨X, ⟨hX, hray, (apart_eq_iff_kleinDist_eq h hA hB hO hX).mpr hd⟩,
      fun Y ⟨hY, hrY, haY⟩ => huniq Y ⟨hY, hrY, (apart_eq_iff_kleinDist_eq h hA hB hO hY).mp haY⟩⟩
  · exact euclid_segment_construction hAB hOD
theorem segment_addition_apart {κ : ℝ} (hκ : κ ≤ 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hF : F ∈ plane κ) (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : apart κ A B = apart κ D E) (h2 : apart κ B C = apart κ E F) :
    apart κ A C = apart κ D F := by
  rcases hκ.lt_or_eq with h | rfl
  · have hB := (kleinDist_add_of_between h hA hC hABC).1
    have hE := (kleinDist_add_of_between h hD hF hDEF).1
    rw [apart_eq_iff_kleinDist_eq h hA hC hD hF]
    exact segment_addition h hA hC hD hF hABC hDEF
      ((apart_eq_iff_kleinDist_eq h hA hB hD hE).mp h1)
      ((apart_eq_iff_kleinDist_eq h hB hC hE hF).mp h2)
  · exact euclid_segment_addition hABC hDEF h1 h2
theorem sas_apart {κ : ℝ} (hκ : κ ≤ 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hE : E ∈ plane κ)
    (hF : F ∈ plane κ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hDE : D ≠ E) (hDF : D ≠ F)
    (hEF : E ≠ F) (h1 : apart κ A B = apart κ D E) (h2 : apart κ A C = apart κ D F)
    (h3 : kleinAngle κ A B C = kleinAngle κ D E F) :
    apart κ B C = apart κ E F ∧ kleinAngle κ B A C = kleinAngle κ E D F ∧
      kleinAngle κ C A B = kleinAngle κ F D E := by
  rcases hκ.lt_or_eq with h | rfl
  · obtain ⟨e1, e2, e3⟩ := side_angle_side h hA hB hC hD hE hF hAB hAC hBC hDE hDF hEF
      ((apart_eq_iff_kleinDist_eq h hA hB hD hE).mp h1)
      ((apart_eq_iff_kleinDist_eq h hA hC hD hF).mp h2) h3
    exact ⟨(apart_eq_iff_kleinDist_eq h hB hC hE hF).mpr e1, e2, e3⟩
  · exact euclid_sas hAB hAC hBC hDE hDF hEF h1 h2 h3
end Apart
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
@[expose] def leaningFigure : Figure ℚ where
  a := ⟨(0, 0), (3 / 5, 0)⟩
  b := ⟨(0, 0), (0, 1 / 2)⟩
  c := ⟨(3 / 5, 0), (27 / 50, 1 / 2)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl
section KleinFifth
open Real
@[expose] def EuclidFifth (κ : ℝ) : Prop :=
  ∀ F : Figure ℝ, F.a.zero ∈ plane κ → F.a.one ∈ plane κ → F.b.one ∈ plane κ →
    F.c.one ∈ plane κ → 0 < F.a.side F.b.one → 0 < F.a.side F.c.one →
    kleinAngle κ F.a.zero F.a.one F.b.one + kleinAngle κ F.a.one F.a.zero F.c.one < π →
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.b.pt t ∈ plane κ ∧
      0 < F.a.side (F.b.pt t)
@[expose] noncomputable def realLeaningFigure : Figure ℝ where
  a := ⟨(0, 0), (3 / 5, 0)⟩
  b := ⟨(0, 0), (0, 1 / 2)⟩
  c := ⟨(3 / 5, 0), (27 / 50, 1 / 2)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl
end KleinFifth
end HyperbolicPlane
end ParallelPostulate
namespace ParallelPostulate
namespace Hilbert
open Pairs HyperbolicPlane
open Real
abbrev Pt (κ : ℝ) := {p : ℝ × ℝ // p ∈ plane κ}
abbrev Ln (κ : ℝ) := {S : Set (ℝ × ℝ) // IsLine (plane κ) S}
@[expose] def mlies (κ : ℝ) (p : Pt κ) (l : Ln κ) : Prop := p.1 ∈ l.1
@[expose] def mbtw (κ : ℝ) (A B C : Pt κ) : Prop := Between A.1 B.1 C.1
@[expose] def msegCong (κ : ℝ) (A B C D : Pt κ) : Prop := apart κ A.1 B.1 = apart κ C.1 D.1
@[expose] def mangCong (κ : ℝ) (A B C D E F : Pt κ) : Prop :=
  kleinAngle κ B.1 A.1 C.1 = kleinAngle κ E.1 D.1 F.1
@[expose] def lineThrough {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) : Ln κ :=
  ⟨(Dim.mk A.1 B.1).points ∩ plane κ, ⟨Dim.mk A.1 B.1, h, rfl, A.1, (Dim.mk _ _).zero_mem, A.2⟩⟩
theorem lies_lineThrough_left {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) :
    mlies κ A (lineThrough A B h) := ⟨(Dim.mk _ _).zero_mem, A.2⟩
theorem lies_lineThrough_right {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) :
    mlies κ B (lineThrough A B h) := ⟨(Dim.mk _ _).one_mem, B.2⟩
theorem model_I1 (κ : ℝ) : ∀ A B : Pt κ, A ≠ B → ∃! l, mlies κ A l ∧ mlies κ B l := by
  intro A B hAB
  obtain ⟨S, ⟨hS, hA, hB⟩, huniq⟩ :=
    line_through (plane κ) A.2 B.2 (fun h => hAB (Subtype.ext h))
  exact ⟨⟨S, hS⟩, ⟨hA, hB⟩, fun l hl => Subtype.ext (huniq l.1 ⟨l.2, hl.1, hl.2⟩)⟩
theorem model_I2 (κ : ℝ) : ∀ l : Ln κ, ∃ A B : Pt κ, A ≠ B ∧ mlies κ A l ∧ mlies κ B l := by
  intro l
  obtain ⟨A, B, hAB, hA, hB⟩ := l.2.two_points (plane_openAlong κ)
  exact ⟨⟨A, l.2.subset_plane hA⟩, ⟨B, l.2.subset_plane hB⟩,
    fun h => hAB (congrArg Subtype.val h), hA, hB⟩
theorem model_I3 (κ : ℝ) : ∃ A B C : Pt κ, ¬ Collinear (mlies κ) A B C := by
  obtain ⟨A, B, C, hA, hB, hC, h⟩ := exists_three_points κ
  exact ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, fun ⟨l, h1, h2, h3⟩ => h l.1 l.2 ⟨h1, h2, h3⟩⟩
theorem model_B1 (κ : ℝ) : ∀ A B C : Pt κ, mbtw κ A B C →
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear (mlies κ) A B C ∧ mbtw κ C B A := by
  intro A B C h
  obtain ⟨h1, h2, h3⟩ := Between.ne h
  exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e),
    fun e => h3 (congrArg Subtype.val e),
    ⟨lineThrough A C h3, lies_lineThrough_left A C h3, ⟨Between.mem h, B.2⟩,
      lies_lineThrough_right A C h3⟩, Between.symm h⟩
theorem model_B2 (κ : ℝ) : ∀ A B : Pt κ, A ≠ B → ∃ C, mbtw κ A B C := by
  intro A B hAB
  obtain ⟨C, hC, h⟩ := exists_beyond κ (fun e => hAB (Subtype.ext e)) B.2
  exact ⟨⟨C, hC⟩, h⟩
theorem model_B3 (κ : ℝ) : ∀ A B C : Pt κ, A ≠ B → B ≠ C → A ≠ C → Collinear (mlies κ) A B C →
    (mbtw κ A B C ∨ mbtw κ B A C ∨ mbtw κ A C B) ∧ ¬ (mbtw κ A B C ∧ mbtw κ B A C) ∧
      ¬ (mbtw κ A B C ∧ mbtw κ A C B) ∧ ¬ (mbtw κ B A C ∧ mbtw κ A C B) := by
  intro A B C hAB hBC hAC ⟨l, hA, hB, hC⟩
  have hAC' : A.1 ≠ C.1 := fun e => hAC (Subtype.ext e)
  have hBm : B.1 ∈ (Dim.mk A.1 C.1).points := by
    have h : B.1 ∈ l.1 := hB
    rw [IsLine.eq_through l.2 hA hC hAC'] at h
    exact h.1
  exact ⟨between_trichotomy (fun e => hAB (Subtype.ext e)) (fun e => hBC (Subtype.ext e)) hAC'
      hBm, fun ⟨h1, h2⟩ => Between.not_left h1 h2, fun ⟨h1, h2⟩ => Between.not_right h1 h2,
    fun ⟨h1, h2⟩ => Between.not_right h1 (Between.symm h2)⟩
theorem model_B4 (κ : ℝ) : ∀ (A B C : Pt κ) (l : Ln κ), ¬ Collinear (mlies κ) A B C →
    ¬ mlies κ A l → ¬ mlies κ B l → ¬ mlies κ C l →
    (∃ D, mlies κ D l ∧ mbtw κ A D B) → ∃ E, mlies κ E l ∧ (mbtw κ A E C ∨ mbtw κ B E C) := by
  intro A B C l _ hA hB hC ⟨D, hD, hAD⟩
  obtain ⟨M, hM, hl, -⟩ := l.2
  have hnot : ∀ X : Pt κ, ¬ mlies κ X l → X.1 ∉ M.points := fun X hX hm =>
    hX (by change X.1 ∈ l.1; rw [hl]; exact ⟨hm, X.2⟩)
  have hDm : D.1 ∈ M.points := by
    have h : D.1 ∈ l.1 := hD
    rw [hl] at h
    exact h.1
  obtain ⟨Y, hYM, hY, hYb⟩ :=
    pasch κ A.2 B.2 C.2 M hM (hnot A hA) (hnot B hB) (hnot C hC) hDm hAD
  exact ⟨⟨Y, hY⟩, by change Y ∈ l.1; rw [hl]; exact ⟨hYM, hY⟩, hYb⟩
theorem model_onRay {κ : ℝ} {O A X : Pt κ} (h : Hilbert.OnRay (mbtw κ) O A X) :
    HyperbolicPlane.OnRay O.1 A.1 X.1 :=
  onRay_of_between (h.imp (congrArg Subtype.val) id)
theorem model_onRay_of {κ : ℝ} {O A X : Pt κ} (hOA : O.1 ≠ A.1)
    (h : HyperbolicPlane.OnRay O.1 A.1 X.1) : Hilbert.OnRay (mbtw κ) O A X :=
  (between_of_onRay hOA h).imp Subtype.ext id
theorem model_C1 (κ : ℝ) (hκ : κ ≤ 0) : ∀ A B C R : Pt κ, A ≠ B → C ≠ R →
    ∃! D, Hilbert.OnRay (mbtw κ) C R D ∧ msegCong κ A B C D := by
  intro A B C R hAB hCR
  have hCR' : C.1 ≠ R.1 := fun e => hCR (Subtype.ext e)
  obtain ⟨X, ⟨hX, hray, hap⟩, huniq⟩ :=
    segment_construction_apart hκ A.2 B.2 C.2 (fun e => hAB (Subtype.ext e)) hCR'
  refine ⟨⟨X, hX⟩, ⟨model_onRay_of hCR' hray, hap⟩, ?_⟩
  rintro D ⟨hD, hapD⟩
  exact Subtype.ext (huniq D.1 ⟨D.2, model_onRay hD, hapD⟩)
theorem model_side_ne_zero {κ : ℝ} {A B C : Pt κ} (h : ¬ Collinear (mlies κ) A B C) :
    (Dim.mk B.1 A.1).side C.1 ≠ 0 := by
  intro hs
  apply h
  by_cases hBA : B.1 = A.1
  · by_cases hAC : A.1 = C.1
    · have hne : A.1 ≠ (A.1.1 + 1, A.1.2) := by
        intro e
        have := congrArg Prod.fst e
        simp at this
      refine ⟨⟨(Dim.mk A.1 (A.1.1 + 1, A.1.2)).points ∩ plane κ,
        ⟨_, hne, rfl, A.1, (Dim.mk _ _).zero_mem, A.2⟩⟩, ⟨(Dim.mk _ _).zero_mem, A.2⟩, ?_, ?_⟩
      · change B.1 ∈ _
        rw [hBA]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
      · change C.1 ∈ _
        rw [← hAC]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
    · refine ⟨lineThrough A C hAC, lies_lineThrough_left A C hAC, ?_,
        lies_lineThrough_right A C hAC⟩
      change B.1 ∈ _
      rw [hBA]
      exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
  · exact ⟨lineThrough B A hBA, lies_lineThrough_right B A hBA, lies_lineThrough_left B A hBA,
      ⟨Dim.mem_points_of_side_eq_zero _ hBA C.1 hs, C.2⟩⟩
theorem model_sameSide_iff {κ : ℝ} {D F : Pt κ} {l : Ln κ} (hD : mlies κ D l) (hF : mlies κ F l)
    (hDF : D.1 ≠ F.1) (E G : Pt κ) :
    Hilbert.SameSide (mlies κ) (mbtw κ) l E G ↔ HyperbolicPlane.SameSide D.1 F.1 E.1 G.1 := by
  have hl := IsLine.eq_through l.2 hD hF hDF
  have hmem : ∀ X : Pt κ, mlies κ X l ↔ (Dim.mk D.1 F.1).side X.1 = 0 := by
    intro X
    change X.1 ∈ l.1 ↔ _
    rw [hl]
    constructor
    · rintro ⟨h, -⟩
      exact Dim.side_eq_zero_of_mem _ h
    · intro h
      exact ⟨Dim.mem_points_of_side_eq_zero _ hDF X.1 h, X.2⟩
  constructor
  · rintro ⟨hE, hG, hno⟩
    have hE' : (Dim.mk D.1 F.1).side E.1 ≠ 0 := fun h => hE ((hmem E).mpr h)
    have hG' : (Dim.mk D.1 F.1).side G.1 ≠ 0 := fun h => hG ((hmem G).mpr h)
    change 0 < _ * _
    rcases lt_trichotomy ((Dim.mk D.1 F.1).side E.1 * (Dim.mk D.1 F.1).side G.1) 0 with h | h | h
    · obtain ⟨Y, hYM, hY, hYb⟩ := crosses κ (Dim.mk D.1 F.1) hDF E.2 G.2 h
      exact absurd ⟨⟨Y, hY⟩, (hmem ⟨Y, hY⟩).mpr (Dim.side_eq_zero_of_mem _ hYM), hYb⟩ hno
    · exact absurd h (mul_ne_zero hE' hG')
    · exact h
  · intro h
    have h' : 0 < (Dim.mk D.1 F.1).side E.1 * (Dim.mk D.1 F.1).side G.1 := h
    have hE' : (Dim.mk D.1 F.1).side E.1 ≠ 0 := by
      intro e
      rw [e, zero_mul] at h'
      exact lt_irrefl 0 h'
    have hG' : (Dim.mk D.1 F.1).side G.1 ≠ 0 := by
      intro e
      rw [e, mul_zero] at h'
      exact lt_irrefl 0 h'
    refine ⟨fun hm => hE' ((hmem E).mp hm), fun hm => hG' ((hmem G).mp hm), ?_⟩
    rintro ⟨C, hCl, ⟨-, u, hu0, hu1, hC⟩⟩
    have h0 := (hmem C).mp hCl
    rw [← hC, Dim.side_through] at h0
    have h1 := congrArg (· * (Dim.mk D.1 F.1).side E.1) h0
    simp only [zero_mul] at h1
    have h2 : 0 < (1 - u) * (Dim.mk D.1 F.1).side E.1 ^ 2 :=
      mul_pos (sub_pos.mpr hu1) (by positivity)
    have h3 := mul_pos hu0 h'
    nlinarith
theorem model_C4 (κ : ℝ) : ∀ (A B C D F G : Pt κ) (l : Ln κ), ¬ Collinear (mlies κ) A B C →
    D ≠ F → mlies κ D l → mlies κ F l → ¬ mlies κ G l →
    (∃ E, Hilbert.SameSide (mlies κ) (mbtw κ) l E G ∧ mangCong κ A B C E D F) ∧
    ∀ E E', Hilbert.SameSide (mlies κ) (mbtw κ) l E G → mangCong κ A B C E D F →
      Hilbert.SameSide (mlies κ) (mbtw κ) l E' G → mangCong κ A B C E' D F →
      Hilbert.OnRay (mbtw κ) D E E' := by
  intro A B C D F G l hABC hDF hD hF hG
  have hDF' : D.1 ≠ F.1 := fun e => hDF (Subtype.ext e)
  have hl := IsLine.eq_through l.2 hD hF hDF'
  have hGs : (Dim.mk D.1 F.1).side G.1 ≠ 0 := by
    intro h
    apply hG
    change G.1 ∈ l.1
    rw [hl]
    exact ⟨Dim.mem_points_of_side_eq_zero _ hDF' G.1 h, G.2⟩
  obtain ⟨hex, huniq⟩ := angle_construction B.2 D.2 (model_side_ne_zero hABC) hDF' hGs
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE, hs, ha⟩ := hex
    refine ⟨⟨E, hE⟩, (model_sameSide_iff hD hF hDF' ⟨E, hE⟩ G).mpr hs, ?_⟩
    change kleinAngle κ B.1 A.1 C.1 = kleinAngle κ D.1 E F.1
    rw [kleinAngle_comm κ D.1 E F.1, ha]
  · intro E E' hs ha hs' ha'
    have hDE : D.1 ≠ E.1 := by
      intro e
      apply hs.1
      rw [show E = D from (Subtype.ext e).symm]
      exact hD
    unfold mangCong at ha ha'
    have hr := huniq E.1 E'.1 E.2 ((model_sameSide_iff hD hF hDF' E G).mp hs)
      (by rw [kleinAngle_comm]; exact ha.symm) E'.2 ((model_sameSide_iff hD hF hDF' E' G).mp hs')
      (by rw [kleinAngle_comm]; exact ha'.symm)
    exact model_onRay_of hDE hr
theorem model_C6 (κ : ℝ) (hκ : κ ≤ 0) : ∀ A B C D E F : Pt κ, ¬ Collinear (mlies κ) A B C →
    ¬ Collinear (mlies κ) D E F → msegCong κ A B D E → msegCong κ A C D F →
    mangCong κ B A C E D F →
    msegCong κ B C E F ∧ mangCong κ A B C D E F ∧ mangCong κ A C B D F E := by
  intro A B C D E F h1 h2 e1 e2 e3
  obtain ⟨hBA, hCB, hCA⟩ := ne_of_side_ne_zero (model_side_ne_zero h1)
  obtain ⟨hED, hFE, hFD⟩ := ne_of_side_ne_zero (model_side_ne_zero h2)
  exact sas_apart hκ A.2 B.2 C.2 D.2 E.2 F.2 hBA.symm hCA.symm hCB.symm hED.symm hFD.symm
    hFE.symm e1 e2 e3
@[expose] noncomputable def model (κ : ℝ) (hκ : κ ≤ 0) : HilbertPlane (Pt κ) (Ln κ) where
  lies := mlies κ
  btw := mbtw κ
  segCong := msegCong κ
  angCong := mangCong κ
  I1 := model_I1 κ
  I2 := model_I2 κ
  I3 := model_I3 κ
  B1 := model_B1 κ
  B2 := model_B2 κ
  B3 := model_B3 κ
  B4 := model_B4 κ
  seg_swap := fun A B => apart_comm κ A.1 B.1
  ang_swap := fun A B C => kleinAngle_comm κ B.1 A.1 C.1
  ang_rays := fun _ _ _ _ _ hA hC => (kleinAngle_onRay (model_onRay hA) (model_onRay hC)).symm
  C1 := model_C1 κ hκ
  C2 := fun _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
  C2_refl := fun _ _ => rfl
  C3 := fun A _ C D _ F h1 h2 h3 h4 => segment_addition_apart hκ A.2 C.2 D.2 F.2 h1 h2 h3 h4
  C4 := model_C4 κ
  C5 := fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
  C5_refl := fun _ _ _ => rfl
  C6 := model_C6 κ hκ
end Hilbert
end ParallelPostulate
namespace ParallelPostulate
namespace Hilbert
open Pairs HyperbolicPlane
end Hilbert
end ParallelPostulate
namespace ParallelPostulate
namespace Hilbert
open Pairs HyperbolicPlane
noncomputable abbrev euclidPlane : HilbertPlane (Pt 0) (Ln 0) := model 0 le_rfl
noncomputable abbrev kleinPlane : HilbertPlane (Pt (-1)) (Ln (-1)) :=
  model (-1) (by norm_num)
end Hilbert
end ParallelPostulate


