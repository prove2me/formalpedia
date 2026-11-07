-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
-- name    : QEC_Coding_ExpanderCodes_JacobiTripleProductCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:07:06.268392+00:00
-- url     : https://prove2.me/theorems/2684609c-2d04-440c-aa49-128ce7bc6d7d
-- title:
--   Jacobi Triple Product Core
-- statement:
--   Definitions and structural lemmas for Jacobi Triple Product Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean

import Mathlib
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
noncomputable def qPochhammerInf {R : Type*} [TopologicalSpace R] [CommRing R] (a q : R) : R :=
  ∏'[SummationFilter.conditional ℕ] i, (1 - a * q ^ i)
abbrev R := PowerSeries (LaurentPolynomial ℤ)
noncomputable abbrev a : R := .C (.T 1)
noncomputable abbrev aI : R := .C (.T (-1))
noncomputable abbrev q : R := .X
local instance _p2m_local_instance_23589ab013_50 : UniformSpace (LaurentPolynomial ℤ) := ⊥
open scoped PowerSeries.WithPiTopology in
noncomputable def lhs : R :=
  qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) *
    qPochhammerInf (-q * aI) (q ^ 2)
open scoped PowerSeries.WithPiTopology in
noncomputable def rhs : R :=
  ∑' m : ℤ, .C (.T m) * q ^ m.natAbs ^ 2
noncomputable abbrev ι : R →+* HahnSeries ℤ (LaurentPolynomial ℤ) :=
  HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℤ)
noncomputable def qPoch {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) : R' :=
  ∏ i ∈ Finset.range n, (1 - A * Q ^ i)
noncomputable abbrev piTop : TopologicalSpace R :=
  PowerSeries.WithPiTopology.instTopologicalSpace (LaurentPolynomial ℤ)
open PowerSeries
noncomputable def qBinom (Q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)
lemma qBinom_eq_zero_of_lt (Q : R) : ∀ {n k : ℕ}, n < k → qBinom Q n k = 0
  | 0, _ + 1, _ => by simp [qBinom]
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    rw [qBinom, qBinom_eq_zero_of_lt Q (by omega : n < k),
        qBinom_eq_zero_of_lt Q (by omega : n < k + 1)]
    simp
@[simp] lemma qBinom_self (Q : R) : ∀ n, qBinom Q n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinom, qBinom_self Q n, qBinom_eq_zero_of_lt Q (by omega)]
    simp
abbrev S := PowerSeries R
noncomputable abbrev t : S := PowerSeries.X
noncomputable abbrev CS : R →+* S := PowerSeries.C (R := R)
noncomputable abbrev P (m : ℕ) : R := qPoch (q ^ 2) (q ^ 2) m
noncomputable def aCoeff (ℓ : ℕ) : R :=
  (-1) ^ ℓ * PowerSeries.invOfUnit (P ℓ) 1
noncomputable def bCoeff (k : ℕ) : R :=
  (q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1
noncomputable abbrev piTopS : TopologicalSpace S :=
  @PowerSeries.WithPiTopology.instTopologicalSpace R piTop
noncomputable def A_S : S := letI := piTopS; ∑' ℓ, CS (aCoeff ℓ) * t ^ ℓ
noncomputable def B_S : S := letI := piTopS; ∑' k, CS (bCoeff k) * t ^ k
noncomputable def eval_x_fun (x : R) : S → R :=
  fun p => letI := piTop; ∑' n, p.coeff n * x ^ n
noncomputable abbrev piUnif : UniformSpace R :=
  PowerSeries.WithPiTopology.instUniformSpace (LaurentPolynomial ℤ)
noncomputable def F (p : ℤ × ℕ) : R :=
  PowerSeries.C (LaurentPolynomial.T p.1) *
  ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
  PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1
noncomputable def G (p : ℕ × ℕ) : R :=
  PowerSeries.C (LaurentPolynomial.T (↑p.1)) *
  ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
  PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1
abbrev N_exp (j ℓ : ℕ) : ℕ := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ
noncomputable abbrev S_hahn := HahnSeries ℤ (LaurentPolynomial ℤ)
noncomputable def ι_hahn : R →+* S_hahn := HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℤ)
noncomputable def Q₀ : S_hahn := HahnSeries.single (2 : ℤ) (1 : LaurentPolynomial ℤ)
noncomputable def A_hahn (j : ℕ) : S_hahn :=
  HahnSeries.single ((-2 * ↑j : ℤ)) (1 : LaurentPolynomial ℤ)
noncomputable def V (ℓ : ℕ) : S_hahn :=
  ι_hahn (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)
noncomputable def E_coeff (A : S_hahn) (b : ℤ) : LaurentPolynomial ℤ :=
  ∑ᶠ ℓ : ℕ, ((-A) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b
noncomputable def negReindex : ℕ × ℕ ≃ {p : ℤ × ℕ // ¬(0 ≤ p.1)} where
  toFun p := ⟨(-(↑p.1 + 1), p.2), by omega⟩
  invFun p := ((-(p.1.1 : ℤ) - 1).toNat, p.1.2)
  left_inv := by
    intro ⟨j, ℓ⟩
    simp [Int.toNat_natCast]
  right_inv := by
    intro ⟨⟨z, ℓ⟩, hz⟩
    push_neg at hz
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨by omega, trivial⟩
noncomputable def reindexEquiv : ℤ × ℕ ≃ ℤ × ℕ where
  toFun p := (p.1 - ↑p.2, p.2)
  invFun p := (p.1 + ↑p.2, p.2)
  left_inv p := by simp [sub_add_cancel]
  right_inv p := by simp [add_sub_cancel_right]
noncomputable def g : letI := piTop; ℤ × ℕ → R := fun p =>
  PowerSeries.C (LaurentPolynomial.T p.1) *
    ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore


