-- Prove2me | Definitions.Def_RPLib_S4_CP4aNewton
-- name    : RPLib_S4_CP4aNewton
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:33.019729+00:00
-- url     : https://prove2.me/theorems/62dab4ec-6371-4009-9067-47f983585c15
-- title:
--   Weight-two Ramanujan-Petersson library: Newton's identity for matrices over any commutative ring
-- statement:
--   Newton's identity for matrices over any commutative ring.
--
--   For a square matrix `A` over a commutative ring `R`, with `C = charpolyRev A = det (1 - X A)`:
--   * `coe_derivative_charpolyRev`: `C' = - C · Σ_k tr(A^(k+1)) X^k` in `R⟦X⟧` (log-derivative / Jacobi at all points;
--     proof: `det (1 - (t + X) A) = det (1 - t A) det (1 + X M')` over `R⟦t⟧[X]`, `M' = -(1 - t A)⁻¹ A`).
--   * `coe_derivative_prod_one_sub`: the same for `Π_i (1 - c_i X)` and the power sums `Σ_i c_i^(k+1)`.
--   * `trace_pow_eq_of_charpolyRev_eq`: equal `charpolyRev` gives equal traces of all positive powers.
--   * `exists_trace_pow_eq_sum_pow`: if `charpolyRev A = L` and `Π (1 - c_i X) = L` for one integer polynomial `L`,
--     then `tr(A^(k+1))` and `Σ c_i^(k+1)` are the images of one integer `s k`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   D. Kalman, A matrix proof of Newton's identities, Math. Mag. 73 (2000), 313-315

import Mathlib

/-!
# S4-CP4a, part b: Newton's identity for matrices over any commutative ring

For a square matrix `A` over a commutative ring `R`, with `C = charpolyRev A = det (1 - X A)`:
* `coe_derivative_charpolyRev`: `C' = - C · Σ_k tr(A^(k+1)) X^k` in `R⟦X⟧` (log-derivative / Jacobi at all points;
  proof: `det (1 - (t + X) A) = det (1 - t A) det (1 + X M')` over `R⟦t⟧[X]`, `M' = -(1 - t A)⁻¹ A`).
* `coe_derivative_prod_one_sub`: the same for `Π_i (1 - c_i X)` and the power sums `Σ_i c_i^(k+1)`.
* `trace_pow_eq_of_charpolyRev_eq`: equal `charpolyRev` gives equal traces of all positive powers.
* `exists_trace_pow_eq_sum_pow`: if `charpolyRev A = L` and `Π (1 - c_i X) = L` for one integer polynomial `L`,
  then `tr(A^(k+1))` and `Σ c_i^(k+1)` are the images of one integer `s k`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The geometric series `Σ_k X^k A^k` as a matrix of power series. -/
noncomputable def geomMat (A : Matrix n n R) : Matrix n n (PowerSeries R) :=
  fun i j => PowerSeries.mk fun k => (A ^ k) i j

theorem mapC_mul_geomMat (A : Matrix n n R) :
    A.map PowerSeries.C * geomMat A = fun i j => PowerSeries.mk fun k => (A ^ (k + 1)) i j := by
  ext i j k
  simp [Matrix.mul_apply, geomMat, map_sum, PowerSeries.coeff_C_mul, pow_succ', Matrix.mul_apply]

theorem geomMat_mul_mapC (A : Matrix n n R) :
    geomMat A * A.map PowerSeries.C = fun i j => PowerSeries.mk fun k => (A ^ (k + 1)) i j := by
  ext i j k
  simp [Matrix.mul_apply, geomMat, map_sum, PowerSeries.coeff_mul_C, pow_succ, Matrix.mul_apply]

theorem one_sub_X_smul_mul_geomMat (A : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • A.map PowerSeries.C) * geomMat A = 1 := by
  have hW : ∀ i j, (A.map PowerSeries.C * geomMat A) i j = PowerSeries.mk fun k => (A ^ (k + 1)) i j :=
    fun i j => by rw [mapC_mul_geomMat]
  rw [sub_mul, one_mul, smul_mul_assoc]
  ext i j k
  rw [Matrix.sub_apply, Matrix.smul_apply, hW, smul_eq_mul]
  rcases k with _ | k
  · by_cases h : i = j <;> simp [geomMat, Matrix.one_apply, h]
  · by_cases h : i = j <;> simp [geomMat, Matrix.one_apply, h, PowerSeries.coeff_succ_X_mul]

theorem coe_charpolyRev (A : Matrix n n R) :
    ((A.charpolyRev : R[X]) : PowerSeries R) =
      det (1 - (PowerSeries.X : PowerSeries R) • A.map PowerSeries.C) := by
  rw [charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h] <;> ring

theorem trace_geomMat_mul (A : Matrix n n R) :
    trace (geomMat A * A.map PowerSeries.C) = PowerSeries.mk fun k => trace (A ^ (k + 1)) := by
  rw [geomMat_mul_mapC]
  refine PowerSeries.ext fun k => ?_
  simp [Matrix.trace, Matrix.diag, map_sum]

/-- **Matrix Newton identity** (log-derivative form): `C' = -C · Σ_k tr(A^(k+1)) X^k`, `C = charpolyRev A`. -/
theorem coe_derivative_charpolyRev (A : Matrix n n R) :
    ((derivative A.charpolyRev : R[X]) : PowerSeries R) =
      -(A.charpolyRev : PowerSeries R) * PowerSeries.mk fun k => trace (A ^ (k + 1)) := by
  set t : PowerSeries R := PowerSeries.X
  set AS : Matrix n n (PowerSeries R) := A.map PowerSeries.C
  set U : Matrix n n (PowerSeries R) := 1 - t • AS with hU
  set V : Matrix n n (PowerSeries R) := geomMat A
  have hUV : U * V = 1 := one_sub_X_smul_mul_geomMat A
  set M' : Matrix n n (PowerSeries R) := -(V * AS)
  have hUM : U * M' = -AS := by
    simp only [M', Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
  let φ : R[X] →+* (PowerSeries R)[X] :=
    Polynomial.eval₂RingHom (Polynomial.C.comp PowerSeries.C) (X + Polynomial.C t)
  have hφ : ∀ p : R[X], φ p = taylor t (p.map PowerSeries.C) := by
    intro p
    simp [φ, taylor_apply, Polynomial.comp, Polynomial.eval₂_map]
  have h1 : φ A.charpolyRev =
      det (1 - (X + Polynomial.C t) • AS.map Polynomial.C) := by
    rw [charpolyRev, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [φ, AS, h] <;> ring
  have h2 : (1 : Matrix n n (PowerSeries R)[X]) - (X + Polynomial.C t) • AS.map Polynomial.C =
      U.map Polynomial.C * (1 + (X : (PowerSeries R)[X]) • M'.map Polynomial.C) := by
    have e1 : U.map Polynomial.C * M'.map Polynomial.C = -AS.map Polynomial.C := by
      rw [← Matrix.map_mul, hUM]
      ext i j
      simp
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, e1]
    ext i j
    by_cases h : i = j <;> simp [U, AS, h] <;> ring
  have h3 : (φ A.charpolyRev).coeff 1 = det U * trace M' := by
    rw [h1, h2, det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.coeff_C_mul,
      coeff_det_one_add_X_smul_one]
  have h4 : (φ A.charpolyRev).coeff 1 = ((derivative A.charpolyRev : R[X]) : PowerSeries R) := by
    rw [hφ, taylor_coeff_one, Polynomial.derivative_map, Polynomial.eval_map,
      Polynomial.eval₂_C_X_eq_coe]
  rw [← h4, h3, coe_charpolyRev, Matrix.trace_neg, trace_geomMat_mul]
  ring

/-- The same for a product `Π_i (1 - c_i X)`: `P' = -P · Σ_k (Σ_i c_i^(k+1)) X^k`. -/
theorem coe_derivative_prod_one_sub (c : Multiset R) :
    ((derivative (c.map fun r => 1 - Polynomial.C r * X).prod : R[X]) : PowerSeries R) =
      -(((c.map fun r => 1 - Polynomial.C r * X).prod : R[X]) : PowerSeries R) *
        PowerSeries.mk fun k => (c.map (· ^ (k + 1))).sum := by
  induction c using Multiset.induction_on with
  | empty =>
    have : (PowerSeries.mk fun _ => (0 : R)) = 0 := by ext; simp
    simp [this]
  | cons a c ih =>
    have key : (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ (k + 1)) =
        PowerSeries.C a := by
      refine PowerSeries.ext fun k => ?_
      rcases k with _ | k
      · simp
      · rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
        simp [pow_succ]
        ring
    have hmk : (PowerSeries.mk fun k => ((a ::ₘ c).map (· ^ (k + 1))).sum) =
        PowerSeries.mk (fun k => a ^ (k + 1)) + PowerSeries.mk fun k => (c.map (· ^ (k + 1))).sum := by
      ext k; simp
    rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_mul, ih, hmk]
    simp only [derivative_sub, derivative_one, derivative_C_mul_X, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, zero_sub, Polynomial.coe_neg] at *
    linear_combination (((c.map fun r => 1 - Polynomial.C r * X).prod : R[X]) : PowerSeries R) * key

/-- Log-derivative cancellation: if `P(0) = 1`, the series `S` with `P' = -P S` is unique. -/
theorem logDeriv_unique {P : R[X]} (hP : P.coeff 0 = 1) {S₁ S₂ : PowerSeries R}
    (h₁ : ((derivative P : R[X]) : PowerSeries R) = -(P : PowerSeries R) * S₁)
    (h₂ : ((derivative P : R[X]) : PowerSeries R) = -(P : PowerSeries R) * S₂) : S₁ = S₂ := by
  have hu : IsUnit (P : PowerSeries R) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe, hP]
    exact isUnit_one
  have h := h₁.symm.trans h₂
  rw [neg_mul, neg_mul, neg_inj] at h
  exact hu.mul_left_cancel h

/-- **Traces of powers are determined by `charpolyRev`.** -/
theorem trace_pow_eq_of_charpolyRev_eq {n' : Type*} [Fintype n'] [DecidableEq n'] (A : Matrix n n R)
    (B : Matrix n' n' R) (h : A.charpolyRev = B.charpolyRev) (k : ℕ) :
    trace (A ^ (k + 1)) = trace (B ^ (k + 1)) := by
  have hS := logDeriv_unique (P := A.charpolyRev) (by rw [Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev])
    (coe_derivative_charpolyRev A) (by rw [h]; exact coe_derivative_charpolyRev B)
  simpa using congrArg (PowerSeries.coeff k) hS

end Mat

section Transfer

/-- An integer polynomial with constant term `1` has integer "power sums" `s` with `L' = -L · Σ s_k X^k`. -/
theorem exists_powerSums (L : ℤ[X]) (hL : L.coeff 0 = 1) :
    ∃ s : ℕ → ℤ, ((derivative L : ℤ[X]) : PowerSeries ℤ) = -(L : PowerSeries ℤ) * PowerSeries.mk s := by
  have hu : IsUnit (L : PowerSeries ℤ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe, hL]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun k => PowerSeries.coeff k (-((↑(u⁻¹) : PowerSeries ℤ) * ((derivative L : ℤ[X]) : PowerSeries ℤ))), ?_⟩
  have : (PowerSeries.mk fun k => PowerSeries.coeff k (-((↑(u⁻¹) : PowerSeries ℤ) * ((derivative L : ℤ[X]) : PowerSeries ℤ)))) =
      -((↑(u⁻¹) : PowerSeries ℤ) * ((derivative L : ℤ[X]) : PowerSeries ℤ)) := by ext; simp
  rw [this, ← hu, mul_neg, neg_mul, neg_neg, ← mul_assoc, Units.mul_inv, one_mul]

theorem map_powerSums {R : Type*} [CommRing R] (L : ℤ[X]) (s : ℕ → ℤ)
    (hs : ((derivative L : ℤ[X]) : PowerSeries ℤ) = -(L : PowerSeries ℤ) * PowerSeries.mk s) :
    ((derivative (L.map (Int.castRingHom R)) : R[X]) : PowerSeries R) =
      -((L.map (Int.castRingHom R) : R[X]) : PowerSeries R) * PowerSeries.mk fun k => (s k : R) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom R)) hs
  rw [map_mul, map_neg, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe,
    ← Polynomial.derivative_map] at h
  rw [h]
  congr 2

/-- **Newton transfer.** If `charpolyRev A` and `Π (1 - c_i X)` are images of one integer polynomial `L`, then for
every `k` there is one integer `s k` with `tr(A^(k+1)) = s k` and `Σ_i c_i^(k+1) = s k`. -/
theorem exists_trace_pow_eq_sum_pow {R K : Type*} [CommRing R] [CommRing K] {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) (L : ℤ[X]) (c : Multiset K)
    (hL : L.coeff 0 = 1) (hA : A.charpolyRev = L.map (Int.castRingHom R))
    (hc : L.map (Int.castRingHom K) = (c.map fun r => 1 - Polynomial.C r * X).prod) :
    ∃ s : ℕ → ℤ, ∀ k : ℕ, trace (A ^ (k + 1)) = (s k : R) ∧ (c.map (· ^ (k + 1))).sum = (s k : K) := by
  have hL0 : (L.map (Int.castRingHom R)).coeff 0 = 1 := by
    rw [← hA, Polynomial.coeff_zero_eq_eval_zero, eval_charpolyRev]
  have hLK0 : (L.map (Int.castRingHom K)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hL, map_one]
  obtain ⟨s, hs⟩ := exists_powerSums L hL
  refine ⟨s, fun k => ⟨?_, ?_⟩⟩
  · have h1 := logDeriv_unique (S₁ := PowerSeries.mk fun k => trace (A ^ (k + 1))) hL0
      (by rw [← hA]; exact coe_derivative_charpolyRev A) (map_powerSums L s hs)
    simpa using congrArg (PowerSeries.coeff k) h1
  · have h2 := logDeriv_unique (S₁ := PowerSeries.mk fun k => (c.map (· ^ (k + 1))).sum) hLK0
      (by rw [hc]; exact coe_derivative_prod_one_sub c) (map_powerSums L s hs)
    simpa using congrArg (PowerSeries.coeff k) h2

end Transfer

end RamanujanPetersson.CP4a


