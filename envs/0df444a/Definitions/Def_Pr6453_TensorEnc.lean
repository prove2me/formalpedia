-- Prove2me | Definitions.Def_Pr6453_TensorEnc
-- name    : Pr6453_TensorEnc
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-09T08:53:10.747058+00:00
-- url     : https://prove2.me/theorems/c51c849b-9805-4009-9b38-8e75aa52a4a3
-- title:
--   PR #6453: the tensor encoding and the basis checker
-- statement:
--   The tensor encoding of the two multiplicands, and the basis checker.
--
--   A word is a linear map on its rows, so the two coefficient vectors cannot be packed side by side: the rows are indexed by the tensor product of the two coefficient spaces. `enc row` is the linearisation of $a\otimes b \mapsto \sum_{i,j} a_i b_j \cdot \mathrm{row}_{ij}$, and the basis tensor $e_i\otimes e_j$ is sent to the row $\mathrm{row}_{ij}$ — the row vector carrying the coefficient $A_i$ in one set of columns and $B_j$ in the complement. `checkBasis` tests the composite $\mathrm{read}\circ M\circ\mathrm{enc}$ on every basis tensor against the required value.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (module block, 1152 polynomial coefficients).

/-
PR #6453: the tensor encoding of the two coefficient vectors and the basis checker.
-/
import Mathlib

set_option autoImplicit false

namespace Pr6453Tensor

open TensorProduct

variable {m n c : ℕ}

/-- `b ↦ Σ_{i,j} a_i b_j • row i j`, for a fixed coefficient vector `a`. -/
def rowLin (row : Fin m → Fin n → (Fin c → ℚ)) (a : Fin m → ℚ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin c → ℚ) where
  toFun b := ∑ i : Fin m, ∑ j : Fin n, (a i * b j) • row i j
  map_add' b b' := by
    have h : ∀ i : Fin m, (∑ j : Fin n, (a i * (b + b') j) • row i j)
        = (∑ j : Fin n, (a i * b j) • row i j)
          + (∑ j : Fin n, (a i * b' j) • row i j) := by
      intro i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Pi.add_apply, mul_add, add_smul]
    simp only [h, Finset.sum_add_distrib]
  map_smul' q b := by
    have h : ∀ i : Fin m, (∑ j : Fin n, (a i * (q • b) j) • row i j)
        = q • (∑ j : Fin n, (a i * b j) • row i j) := by
      intro i
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        have hv : a i * (q • b) j = q * (a i * b j) := by
          rw [Pi.smul_apply, smul_eq_mul]
          ring
        rw [hv, smul_smul]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => h i

/-- The bilinear form `(a,b) ↦ Σ_{i,j} a_i b_j • row i j`. -/
def bilin (row : Fin m → Fin n → (Fin c → ℚ)) :
    (Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ) →ₗ[ℚ] (Fin c → ℚ) where
  toFun := rowLin row
  map_add' a a' := by
    refine LinearMap.ext fun b => ?_
    have h : ∀ i : Fin m, (∑ j : Fin n, ((a + a') i * b j) • row i j)
        = (∑ j : Fin n, (a i * b j) • row i j)
          + (∑ j : Fin n, (a' i * b j) • row i j) := by
      intro i
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Pi.add_apply, add_mul, add_smul]
    change (rowLin row (a + a')) b = (rowLin row a) b + (rowLin row a') b
    simp only [rowLin, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [h, Finset.sum_add_distrib]
  map_smul' q a := by
    refine LinearMap.ext fun b => ?_
    have h : ∀ i : Fin m, (∑ j : Fin n, ((q • a) i * b j) • row i j)
        = q • (∑ j : Fin n, (a i * b j) • row i j) := by
      intro i
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        have hv : (q • a) i * b j = q * (a i * b j) := by
          rw [Pi.smul_apply, smul_eq_mul]
          ring
        rw [hv, smul_smul]
    change (rowLin row (q • a)) b = (q • rowLin row a) b
    simp only [rowLin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => h i

/-- **`enc`**: the linear map on the tensor product of the two coefficient spaces. -/
def enc (row : Fin m → Fin n → (Fin c → ℚ)) : ((Fin m → ℚ) ⊗[ℚ] (Fin n → ℚ)) →ₗ[ℚ] (Fin c → ℚ) :=
  TensorProduct.lift (bilin row)

/-- On the basis tensor `e_i ⊗ e_j`, `enc` is the row `row i j`. -/
theorem enc_basis (row : Fin m → Fin n → (Fin c → ℚ)) (i : Fin m) (j : Fin n) :
    enc row (Pi.single i 1 ⊗ₜ[ℚ] Pi.single j 1) = row i j := by
  simp only [enc, TensorProduct.lift.tmul, bilin, rowLin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [Pi.single_eq_of_ne hj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi
    simp only [Pi.single_eq_of_ne hi, zero_mul, zero_smul, Finset.sum_const_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- **The checker**: test the word on every basis tensor. -/
def checkBasis (row : Fin m → Fin n → (Fin c → ℚ)) (M : (Fin c → ℚ) →ₗ[ℚ] (Fin c → ℚ))
    (read : (Fin c → ℚ) →ₗ[ℚ] (Fin c → ℚ)) (P : Fin m → Fin n → (Fin c → ℚ)) : Bool :=
  (List.finRange m).all fun i =>
    (List.finRange n).all fun j =>
      decide (read (M (enc row (Pi.single i 1 ⊗ₜ[ℚ] Pi.single j 1))) = P i j)

end Pr6453Tensor


