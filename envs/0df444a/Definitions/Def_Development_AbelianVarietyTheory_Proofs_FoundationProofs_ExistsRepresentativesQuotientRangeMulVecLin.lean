-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:34.500324+00:00
-- url     : https://prove2.me/theorems/a1e76b58-195f-4902-967c-62a7de131083
-- title:
--   Exists Representatives Quotient Range Mul Vec Lin
-- statement:
--   Definitions and structural lemmas for Exists Representatives Quotient Range Mul Vec Lin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
namespace GlobalTheory
section Trace
variable {A : Type*} [Fintype A] [DecidableEq A]
end Trace
section Bicharacter
variable {A : Type*} [AddCommGroup A] [Fintype A]
end Bicharacter
section Quadratic
variable {A : Type*} [AddCommGroup A] [Fintype A]
open Complex in
theorem periodic_exp_two_pi_rat :
    Function.Periodic (fun r : ℚ => exp (2 * Real.pi * I * r)) 1 := fun r => by
  simp only [Rat.cast_add, Rat.cast_one, mul_add, mul_one, exp_add, exp_two_pi_mul_I]
noncomputable def ratCircleChar : AddChar (AddCircle (1 : ℚ)) ℂ where
  toFun := periodic_exp_two_pi_rat.lift
  map_zero_eq_one' := by
    change Complex.exp _ = 1
    simp
  map_add_eq_mul' x y := by
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    change Complex.exp _ = Complex.exp _ * Complex.exp _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
@[simp]
theorem ratCircleChar_coe (r : ℚ) :
    ratCircleChar (r : AddCircle (1 : ℚ)) = Complex.exp (2 * Real.pi * Complex.I * r) := rfl
end Quadratic
section Matrices
variable {n : Type*} [Fintype n]
noncomputable def halfQuadraticModOne (M : Matrix n n ℚ) :
    QuadraticMap ℤ (n → ℤ) (AddCircle (1 : ℚ)) :=
  LinearMap.BilinMap.toQuadraticMap <| LinearMap.mk₂ ℤ
    (fun x y : n → ℤ =>
      ((((fun i => (x i : ℚ)) ⬝ᵥ M *ᵥ fun i => (y i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)))
    (fun x x' y => by
      rw [← AddCircle.coe_add, ← add_div, ← add_dotProduct]
      congr 3; ext; simp)
    (fun c x y => by
      rw [← AddCircle.coe_zsmul, ← smul_div_assoc, ← smul_dotProduct]
      congr 3; ext; simp)
    (fun x y y' => by
      rw [← AddCircle.coe_add, ← add_div, ← dotProduct_add, ← mulVec_add]
      congr 4; ext; simp)
    (fun c x y => by
      rw [← AddCircle.coe_zsmul, ← smul_div_assoc, ← dotProduct_smul, ← mulVec_smul]
      congr 4; ext; simp)
theorem halfQuadraticModOne_apply (M : Matrix n n ℚ) (x : n → ℤ) :
    halfQuadraticModOne M x =
      ((((fun i => (x i : ℚ)) ⬝ᵥ M *ᵥ fun i => (x i : ℚ)) / 2 : ℚ) : AddCircle (1 : ℚ)) := rfl
theorem polar_halfQuadraticModOne {M : Matrix n n ℚ} (hM : M.IsSymm) (x y : n → ℤ) :
    QuadraticMap.polar (halfQuadraticModOne M) x y =
      (((fun i => (y i : ℚ)) ⬝ᵥ M *ᵥ (fun i => (x i : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [halfQuadraticModOne, LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.mk₂_apply,
    LinearMap.mk₂_apply, ← AddCircle.coe_add, dotProduct_mulVec, ← mulVec_transpose, hM.eq,
    dotProduct_comm, add_halves]
variable [DecidableEq n] {b d : Matrix n n ℤ}
theorem isUnit_det_map_ratCast (hd : d.det ≠ 0) : IsUnit (d.map ((↑) : ℤ → ℚ)).det := by
  rw [← Int.cast_det]; simpa using hd
theorem isSymm_mul_inv_of_isSymm (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm) :
    (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹).IsSymm := by
  have hu := isUnit_det_map_ratCast hd
  have hs' := (hs.map (Int.castRingHom ℚ)).eq
  rw [Matrix.map_mul, transpose_map, transpose_mul, transpose_transpose] at hs'
  simp only [Int.coe_castRingHom] at hs'
  rw [Matrix.IsSymm, transpose_mul, transpose_nonsing_inv]
  set B := b.map ((↑) : ℤ → ℚ)
  set D := d.map ((↑) : ℤ → ℚ)
  calc Dᵀ⁻¹ * Bᵀ = Dᵀ⁻¹ * (Bᵀ * D) * D⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = B * D⁻¹ := by
        rw [hs', ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_transpose _ hu), Matrix.one_mul]
omit [DecidableEq n] in
theorem intCast_mulVec (d : Matrix n n ℤ) (x : n → ℤ) :
    (fun i => ((d *ᵥ x) i : ℚ)) = d.map ((↑) : ℤ → ℚ) *ᵥ fun i => (x i : ℚ) := by
  ext i; simp [mulVec, dotProduct]
omit [DecidableEq n] in
theorem intCast_dotProduct (x y : n → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℚ) = (fun i => (x i : ℚ)) ⬝ᵥ fun i => (y i : ℚ) := by
  simp [dotProduct]
theorem range_le_radical_halfQuadraticModOne (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) :
    LinearMap.range d.mulVecLin ≤
      (halfQuadraticModOne (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹)).radical := by
  rintro _ ⟨μ, rfl⟩
  have hu := isUnit_det_map_ratCast hd
  have key : (b.map ((↑) : ℤ → ℚ) * (d.map ((↑) : ℤ → ℚ))⁻¹) *ᵥ (fun i => ((d *ᵥ μ) i : ℚ)) =
      fun i => ((b *ᵥ μ) i : ℚ) := by
    rw [intCast_mulVec, intCast_mulVec, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu,
      Matrix.mul_one]
  refine ⟨?_, LinearMap.ext fun y => ?_⟩
  · obtain ⟨k, hk⟩ := he μ
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at hk
    rw [mulVecLin_apply, halfQuadraticModOne_apply, key, ← intCast_dotProduct, hk]
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨k, by simp⟩
  · rw [QuadraticMap.polarBilin_apply_apply,
      polar_halfQuadraticModOne (isSymm_mul_inv_of_isSymm hd hs), mulVecLin_apply, key,
      ← intCast_dotProduct]
    exact (AddCircle.coe_eq_zero_iff _).2 ⟨_, by rw [zsmul_eq_mul, mul_one]⟩
noncomputable def pairQuadraticForm (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) :
    QuadraticMap ℤ ((n → ℤ) ⧸ LinearMap.range d.mulVecLin) (AddCircle (1 : ℚ)) :=
  QuadraticMap.lift _ _ (range_le_radical_halfQuadraticModOne hd hs he)
end Matrices
end GlobalTheory


