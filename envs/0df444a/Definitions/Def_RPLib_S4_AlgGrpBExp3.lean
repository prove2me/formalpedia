-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBExp3
-- name    : RPLib_S4_AlgGrpBExp3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:51:44.949201+00:00
-- url     : https://prove2.me/theorems/36df5e10-2357-4c19-aa94-789e49a07160
-- title:
--   Larsen's alternative library: `exp(tN) = 1 + tN + (t²/2)N²` for `N³ = 0`
-- statement:
--   Char 0. The argument of `Exp` works for any polynomial curve `c` with `c' = c · N` (in coordinates,
--   `derivative (c v) = aeval c (dN N v)`) and `c(0) = 1`: every `f ∈ vanI H` vanishes along `c` when
--   `N ∈ Lie H` (`aeval_gen_eq_zero`). For `N³ = 0` the curve `t ↦ exp3 N t` gives `exp3_mem` (closed `H`).
--   `exp3_mem_isoSub`: `exp3 N t` preserves `B` when `Nᵀ B + B N = 0`; `det_exp3`: its determinant is `1`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSpGen

/-!
# S4-AlgGrpB, file Exp3: `exp(tN) = 1 + tN + (t²/2)N²` for `N³ = 0` (O5b-SO, first part)

Char 0. The argument of `Exp` works for any polynomial curve `c` with `c' = c · N` (in coordinates,
`derivative (c v) = aeval c (dN N v)`) and `c(0) = 1`: every `f ∈ vanI H` vanishes along `c` when
`N ∈ Lie H` (`aeval_gen_eq_zero`). For `N³ = 0` the curve `t ↦ exp3 N t` gives `exp3_mem` (closed `H`).
`exp3_mem_isoSub`: `exp3 N t` preserves `B` when `Nᵀ B + B N = 0`; `det_exp3`: its determinant is `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial
open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem derivative_aeval_gen (N : Matrix n n K) (c : Var n → Polynomial K)
    (hc : ∀ v, Polynomial.derivative (c v) = aeval c (dN N v)) (f : MvPolynomial (Var n) K) :
    Polynomial.derivative (aeval c f) = aeval c (derN N f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [derN_C]
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, hp, hq, derN_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, derN_mul_X, map_add, map_mul, map_mul, aeval_X, hc v]

theorem iterate_derivative_aeval_gen (N : Matrix n n K) (c : Var n → Polynomial K)
    (hc : ∀ v, Polynomial.derivative (c v) = aeval c (dN N v)) (f : MvPolynomial (Var n) K)
    (k : ℕ) : Polynomial.derivative^[k] (aeval c f) = aeval c ((derN N)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_aeval_gen N c hc,
      ← Function.iterate_succ_apply' (derN N)]

theorem eval_aeval_gen (c : Var n → Polynomial K) (t : K) (f : MvPolynomial (Var n) K) :
    Polynomial.eval t (aeval c f) = eval (fun v => Polynomial.eval t (c v)) f := by
  rw [← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
  have : (fun v => Polynomial.aeval t (c v)) = fun v => Polynomial.eval t (c v) :=
    funext fun v => by rw [Polynomial.coe_aeval_eq_eval]
  rw [this]
  rfl

/-- Generic unipotent step (char 0): `f ∈ vanI H` vanishes along a curve `c` with `c' = c N`, `c(0) = 1`. -/
theorem aeval_gen_eq_zero [CharZero K] {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    {N : Matrix n n K} (hN : N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (c : Var n → Polynomial K) (hc : ∀ v, Polynomial.derivative (c v) = aeval c (dN N v))
    (h0 : ∀ v, Polynomial.eval 0 (c v) = crd 1 v) {f : MvPolynomial (Var n) K}
    (hf : f ∈ vanI (H : Set (Matrix.GeneralLinearGroup n K))) : aeval c f = 0 := by
  ext k
  have h1 := congrArg (fun p => Polynomial.coeff p 0) (iterate_derivative_aeval_gen N c hc f k)
  have h0' : (fun v => Polynomial.eval 0 (c v)) = crd 1 := funext h0
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_zero_eq_eval_zero, eval_aeval_gen, h0',
    mem_vanI.1 (derN_iterate_mem_vanI hN hf k) 1 H.one_mem, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul, mul_eq_zero] at h1
  rw [Polynomial.coeff_zero]
  rcases h1 with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))
  · exact h1

/-- `C a + X C b + X² C d` has derivative `C b + X C (2 d)`. -/
theorem derivative_quad (a b d : K) :
    Polynomial.derivative (Polynomial.C a + Polynomial.X * Polynomial.C b +
      Polynomial.X ^ 2 * Polynomial.C d) = Polynomial.C b + Polynomial.X * Polynomial.C (2 * d) := by
  simp only [Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
    Polynomial.derivative_X, Polynomial.derivative_X_pow, Polynomial.C_mul, zero_add, one_mul,
    mul_zero, add_zero]
  simp only [Nat.cast_ofNat, Polynomial.C_ofNat]
  ring

section CharZ

variable [CharZero K]

theorem mul_quad (N : Matrix n n K) (hN : N * N * N = 0) (a b a' b' : K) :
    (1 + a • N + b • (N * N)) * (1 + a' • N + b' • (N * N)) =
      1 + (a + a') • N + (b + a * a' + b') • (N * N) := by
  have h3 : N * (N * N) = 0 := by rw [← Matrix.mul_assoc, hN]
  have h4 : N * N * (N * N) = 0 := by rw [← Matrix.mul_assoc, hN, Matrix.zero_mul]
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h3, h4, hN, smul_zero, add_zero]
  module

theorem half_sum (t : K) : t ^ 2 * (2 : K)⁻¹ + t * -t + t ^ 2 * (2 : K)⁻¹ = 0 := by
  have h2 : (2 : K)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ two_ne_zero]
  linear_combination t ^ 2 * h2

/-- `exp(t N) = 1 + t N + (t²/2) N²` when `N³ = 0`. -/
def exp3 (N : Matrix n n K) (hN : N * N * N = 0) (t : K) : Matrix.GeneralLinearGroup n K where
  val := 1 + t • N + (t ^ 2 * (2 : K)⁻¹) • (N * N)
  inv := 1 + (-t) • N + (t ^ 2 * (2 : K)⁻¹) • (N * N)
  val_inv := by
    rw [mul_quad N hN, add_neg_cancel, half_sum, zero_smul, zero_smul, add_zero, add_zero]
  inv_val := by
    have h : t ^ 2 * (2 : K)⁻¹ + -t * t + t ^ 2 * (2 : K)⁻¹ = 0 := by
      have := half_sum t
      linear_combination this
    rw [mul_quad N hN, neg_add_cancel, h, zero_smul, zero_smul, add_zero, add_zero]

theorem val_exp3 (N : Matrix n n K) (hN : N * N * N = 0) (t : K) :
    ((exp3 N hN t : Matrix.GeneralLinearGroup n K) : Matrix n n K) =
      1 + t • N + (t ^ 2 * (2 : K)⁻¹) • (N * N) := rfl

theorem val_exp3_inv (N : Matrix n n K) (hN : N * N * N = 0) (t : K) :
    (((exp3 N hN t)⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) =
      1 + (-t) • N + (t ^ 2 * (2 : K)⁻¹) • (N * N) := rfl

/-- The curve `t ↦ exp3 N t` in coordinates. -/
def curve3 (N : Matrix n n K) : Var n → Polynomial K :=
  Sum.elim
    (fun ij => Polynomial.C ((1 : Matrix n n K) ij.1 ij.2) + Polynomial.X * Polynomial.C (N ij.1 ij.2) +
      Polynomial.X ^ 2 * Polynomial.C (((2 : K)⁻¹ • (N * N)) ij.1 ij.2))
    (fun ij => Polynomial.C ((1 : Matrix n n K) ij.1 ij.2) +
      Polynomial.X * Polynomial.C ((-N) ij.1 ij.2) +
      Polynomial.X ^ 2 * Polynomial.C (((2 : K)⁻¹ • (N * N)) ij.1 ij.2))

theorem crd_exp3 (N : Matrix n n K) (hN : N * N * N = 0) (t : K) :
    crd (exp3 N hN t) = fun v => Polynomial.eval t (curve3 N v) := by
  funext v
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp [exp3, curve3]
    ring
  · change (1 + (-t) • N + (t ^ 2 * (2 : K)⁻¹) • (N * N)) i j = _
    simp [curve3]
    ring

theorem curve3_zero (N : Matrix n n K) (v : Var n) :
    Polynomial.eval 0 (curve3 N v) = crd 1 v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩ <;> simp [curve3]

theorem two_mul_half (N : Matrix n n K) (i j : n) :
    (2 : K) * ((2 : K)⁻¹ • (N * N)) i j = (N * N) i j := by
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]

theorem curve3_deriv (N : Matrix n n K) (hN : N * N * N = 0) (v : Var n) :
    Polynomial.derivative (curve3 N v) = aeval (curve3 N) (dN N v) := by
  have hN2 : (2 : K)⁻¹ • (N * N) * N = 0 := by rw [Matrix.smul_mul, hN, smul_zero]
  have hN3 : (-N) * ((2 : K)⁻¹ • (N * N)) = 0 := by
    rw [Matrix.mul_smul, Matrix.neg_mul, ← Matrix.mul_assoc, hN, neg_zero, smul_zero]
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · have e : ∑ k, (Polynomial.C ((1 : Matrix n n K) i k) + Polynomial.X * Polynomial.C (N i k) +
        Polynomial.X ^ 2 * Polynomial.C (((2 : K)⁻¹ • (N * N)) i k)) * Polynomial.C (N k j) =
        Polynomial.C (((1 : Matrix n n K) * N) i j) + Polynomial.X * Polynomial.C ((N * N) i j) +
          Polynomial.X ^ 2 * Polynomial.C (((2 : K)⁻¹ • (N * N) * N) i j) := by
      simp only [Matrix.mul_apply, map_sum, Polynomial.C_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [curve3, Sum.elim_inl, dN, map_sum, map_mul, aeval_X, aeval_C,
      Polynomial.algebraMap_eq]
    rw [e, hN2, Matrix.one_mul, Matrix.zero_apply, map_zero, mul_zero, add_zero, derivative_quad,
      two_mul_half]
  · have e : ∑ k, Polynomial.C ((-N) i k) * (Polynomial.C ((1 : Matrix n n K) k j) +
        Polynomial.X * Polynomial.C ((-N) k j) +
        Polynomial.X ^ 2 * Polynomial.C (((2 : K)⁻¹ • (N * N)) k j)) =
        Polynomial.C ((-N * (1 : Matrix n n K)) i j) + Polynomial.X * Polynomial.C ((-N * -N) i j) +
          Polynomial.X ^ 2 * Polynomial.C ((-N * ((2 : K)⁻¹ • (N * N))) i j) := by
      simp only [Matrix.mul_apply, map_sum, Polynomial.C_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [curve3, Sum.elim_inr, dN, map_sum, map_mul, aeval_X, aeval_C,
      Polynomial.algebraMap_eq]
    rw [e, hN3, neg_mul_neg, Matrix.mul_one, Matrix.zero_apply, map_zero, mul_zero, add_zero,
      derivative_quad, two_mul_half]

attribute [local instance] zarTop in
/-- `(A4)`, unipotent step for `N³ = 0` (char 0, `H` closed, `N ∈ Lie H`): `exp3 N t ∈ H`. -/
theorem exp3_mem {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K))) {N : Matrix n n K}
    (hN3 : N * N * N = 0) (hN : N ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) (t : K) :
    exp3 N hN3 t ∈ H := by
  have hc : exp3 N hN3 t ∈ closure (H : Set (Matrix.GeneralLinearGroup n K)) := by
    rw [closure_eq_zeroS_vanI]
    refine mem_zeroS.2 fun f hf => ?_
    rw [crd_exp3, ← eval_aeval_gen,
      aeval_gen_eq_zero hN (curve3 N) (curve3_deriv N hN3) (curve3_zero N) hf, Polynomial.eval_zero]
  rwa [hH.closure_eq] at hc

/-- `exp3 N t` preserves `B` when `Nᵀ B + B N = 0`. -/
theorem exp3_mem_isoSub {B N : Matrix n n K} (hN3 : N * N * N = 0) (hN : Nᵀ * B + B * N = 0)
    (t : K) : exp3 N hN3 t ∈ isoSub B := by
  have h1 : Nᵀ * B = -(B * N) := eq_neg_of_add_eq_zero_left hN
  have h2 : (N * N)ᵀ * B = B * (N * N) := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, h1,
      Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have key : (1 + t • N + (t ^ 2 * (2 : K)⁻¹) • (N * N))ᵀ * B =
      B * (1 + (-t) • N + (t ^ 2 * (2 : K)⁻¹) • (N * N)) := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, add_mul,
      Matrix.one_mul, Matrix.smul_mul, h1, h2, mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_neg, smul_neg, neg_smul]
  rw [mem_isoSub, val_exp3, key, Matrix.mul_assoc, ← val_exp3_inv N hN3, ← val_exp3 N hN3,
    Units.inv_mul, Matrix.mul_one]

/-- `det (1 - M) = 1` for nilpotent `M`. -/
theorem det_one_sub_of_nil {M : Matrix n n K} (hM : IsNilpotent M) : (1 - M).det = 1 := by
  have hu := Matrix.isUnit_charpolyRev_of_isNilpotent hM
  have hp := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)
  have h0 : Polynomial.eval 0 M.charpolyRev = 1 := Matrix.eval_charpolyRev
  have h1 : Polynomial.eval 1 M.charpolyRev = (1 - M).det := by
    rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  rw [← h1, hp, Polynomial.eval_C]
  rw [hp, Polynomial.eval_C] at h0
  exact h0

theorem det_exp3 (N : Matrix n n K) (hN : N * N * N = 0) (t : K) :
    ((exp3 N hN t : Matrix.GeneralLinearGroup n K) : Matrix n n K).det = 1 := by
  have hP : ((exp3 N hN t : Matrix.GeneralLinearGroup n K) : Matrix n n K) =
      1 - (-(t • (1 : Matrix n n K) + (t ^ 2 * (2 : K)⁻¹) • N)) * N := by
    rw [val_exp3]
    simp only [Matrix.neg_mul, add_mul, Matrix.smul_mul, Matrix.one_mul, sub_neg_eq_add, smul_smul]
    module
  rw [hP]
  refine det_one_sub_of_nil (Commute.isNilpotent_mul_left ?_ ⟨3, ?_⟩)
  · exact (((Commute.one_left N).smul_left t).add_left ((Commute.refl N).smul_left _)).neg_left
  · rw [pow_three, ← Matrix.mul_assoc, hN]

end CharZ

end RamanujanPetersson.AlgGrpB

end


