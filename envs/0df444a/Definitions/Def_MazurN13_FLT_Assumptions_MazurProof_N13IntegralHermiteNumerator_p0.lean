-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralHermiteNumerator_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralHermiteNumerator_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T01:56:05.733289+00:00
-- url     : https://prove2.me/theorems/f53abbec-3866-4665-ba1d-1b4162f7a9a1
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralHermiteNumerator source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralHermiteNumerator

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralHermiteNumerator
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CenteredHermiteFirstOrder_p0
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Construct the monic Hermite numerator directly over Z2. Its four linear
equations have an invertible residue matrix for every actual disk pair;
the tangent slopes need only be integral. This discharges existence of the
four equations used in CenteredHermiteFirstOrder. Identification with the
principal comparison and its residual divisor is a separate obligation.
-/

namespace MazurProof.N13IntegralHermiteNumerator

noncomputable section
open N13CenteredHermiteFirstOrder
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def matrix (P : DiskPair) (s : Fin 2 → R₂) : Matrix (Fin 4) (Fin 4) R₂ :=
  let x₀ := P.x₀
  let x₁ := P.x₁
  let u₀ := x₀ ^ 2 + x₀
  let u₁ := x₁ ^ 2 + x₁
  let d₀ := 2 * x₀ + 1
  let d₁ := 2 * x₁ + 1
  let y₀ := oppositeY P 0
  let y₁ := oppositeY P 1
  !![u₀, u₀ * x₀, y₀, y₀ * x₀;
     u₁, u₁ * x₁, y₁, y₁ * x₁;
     d₀, d₀ * x₀ + u₀, s 0, y₀ + x₀ * s 0;
     d₁, d₁ * x₁ + u₁, s 1, y₁ + x₁ * s 1]

def rightSide (P : DiskPair) : Fin 4 → R₂ :=
  ![-(P.x₀ ^ 2 + P.x₀) * P.x₀ ^ 2,
    -(P.x₁ ^ 2 + P.x₁) * P.x₁ ^ 2,
    -(2 * P.x₀ + 1) * P.x₀ ^ 2 - (P.x₀ ^ 2 + P.x₀) * (2 * P.x₀),
    -(2 * P.x₁ + 1) * P.x₁ ^ 2 - (P.x₁ ^ 2 + P.x₁) * (2 * P.x₁)]

private def residueMatrix (s₀ s₁ : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 1, 1;
     1, 0, s₀, 1; 1, 1, s₁, 1 + s₁]

private def residueInverse (s₀ s₁ : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1 - s₀, -1, 1, 0; s₀, -s₁, -1, 1;
     1, 0, 0, 0; -1, 1, 0, 0]

private theorem residueMatrix_mul_inverse (s₀ s₁ : ZMod 2) :
    residueMatrix s₀ s₁ * residueInverse s₀ s₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residueMatrix, residueInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 from rfl]

private theorem reduce_matrix (P : DiskPair) (s : Fin 2 → R₂) :
    (matrix P s).map N13GeneralizedMumfordReduction.reduceBase =
      residueMatrix (N13GeneralizedMumfordReduction.reduceBase (s 0))
        (N13GeneralizedMumfordReduction.reduceBase (s 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, residueMatrix, Matrix.map, oppositeY,
      N13GoodModelTwo.h, map_add, map_sub, map_neg, map_mul, map_pow] <;>
    first | rfl | decide | (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])

theorem matrix_det_unit (P : DiskPair) (s : Fin 2 → R₂) :
    IsUnit (matrix P s).det := by
  let r := N13GeneralizedMumfordReduction.reduceBase
  have hunit : IsUnit (r (matrix P s).det) := by
    rw [r.map_det]
    change IsUnit ((matrix P s).map r).det
    rw [reduce_matrix]
    exact Matrix.isUnit_det_of_right_inverse
      (residueMatrix_mul_inverse (r (s 0)) (r (s 1)))
  have hres : r (matrix P s).det = 1 := by
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one (r (matrix P s).det)
      (ZMod.pow_card _) with hz | ho
    · exact (hunit.ne_zero hz).elim
    · exact ho
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  have hker : (matrix P s).det - 1 ∈ RingHom.ker r := by
    change r ((matrix P s).det - 1) = 0
    rw [map_sub, hres, map_one, sub_self]
  simpa only [r, N13GeneralizedMumfordReduction.reduceBase, PadicInt.ker_toZMod] using hker

theorem exists_coefficients (P : DiskPair) (s : Fin 2 → R₂) :
    ∃ a₀ a₁ b₀ b₁ : R₂,
      (∀ j, (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (b₀ + b₁ * x P j) * oppositeY P j = 0) ∧
      (∀ j, (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
        b₁ * oppositeY P j + (b₀ + b₁ * x P j) * s j = 0) := by
  have hsurj : Function.Surjective (matrix P s).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (matrix_det_unit P s))
  obtain ⟨c, hc⟩ := hsurj (rightSide P)
  refine ⟨c 0, c 1, c 2, c 3, ?_, ?_⟩
  · intro j
    fin_cases j
    · have h := congrFun hc (0 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
    · have h := congrFun hc (1 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
  · intro j
    fin_cases j
    · have h := congrFun hc (2 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
    · have h := congrFun hc (3 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h

/-- Actual integral coefficients satisfying all four Hermite equations and
the required first-order normalization, without any existence assumption. -/
theorem exists_normalized_coefficients (P : DiskPair) (s : Fin 2 → R₂) :
    ∃ a₀ a₁ b₀ b₁ : R₂,
      (∀ j, (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (b₀ + b₁ * x P j) * oppositeY P j = 0) ∧
      (∀ j, (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
        b₁ * oppositeY P j + (b₀ + b₁ * x P j) * s j = 0) ∧
      b₀ ∈ I P * I P ∧ b₁ ∈ I P * I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P := by
  obtain ⟨a₀, a₁, b₀, b₁, hv, hd⟩ := exists_coefficients P s
  exact ⟨a₀, a₁, b₀, b₁, hv, hd, hermite_coefficients_mod_square P _ _ _ _ s hv hd⟩

end
end MazurProof.N13IntegralHermiteNumerator


