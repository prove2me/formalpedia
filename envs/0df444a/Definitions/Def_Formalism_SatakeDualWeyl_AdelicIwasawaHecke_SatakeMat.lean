-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:45.06673+00:00
-- url     : https://prove2.me/theorems/d4f5f16c-886b-4469-b1f3-01ea281a67ab
-- title:
--   Satake Mat
-- statement:
--   Definitions and structural lemmas for Satake Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SatakeMat.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
abbrev satakePairs (S : Finset (Fin n)) : Type := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2}
def satakeN (S : Finset (Fin n)) (c : satakePairs S → O) : Matrix (Fin n) (Fin n) L :=
  fun a l => if h : a ∈ S ∧ l ∉ S ∧ a < l then ((c ⟨(a, l), h⟩ : O) : L) else 0
def satakeD (π : L) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) L :=
  Matrix.diagonal (fun a => if a ∈ S then π else 1)
lemma satakeN_apply (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n) :
    satakeN O S c a l = if h : a ∈ S ∧ l ∉ S ∧ a < l then ((c ⟨(a, l), h⟩ : O) : L) else 0 := rfl
theorem satakeN_mul_self (S : Finset (Fin n)) (c c' : satakePairs S → O) :
    satakeN O S c * satakeN O S c' = 0 := by
  ext a l
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : b ∈ S
  · rw [satakeN_apply O S c a b, dif_neg (fun h => h.2.1 hb), zero_mul]
  · rw [satakeN_apply O S c' b l, dif_neg (fun h => hb h.1), mul_zero]
variable {O}
theorem satakeD_mul_inv {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) :
    satakeD π S * satakeD π⁻¹ S = 1 := by
  simp only [satakeD, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp [hπ]
theorem satakeD_inv_mul {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) :
    satakeD π⁻¹ S * satakeD π S = 1 := by
  simp only [satakeD, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp [hπ]
variable (O)
def satakeGL {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) : GL (Fin n) L where
  val := (1 + satakeN O S c) * satakeD π S
  inv := satakeD π⁻¹ S * (1 - satakeN O S c)
  val_inv := by
    have h : (1 + satakeN O S c) * (1 - satakeN O S c) = 1 := by
      rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, satakeN_mul_self, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]; abel
    rw [show (1 + satakeN O S c) * satakeD π S * (satakeD π⁻¹ S * (1 - satakeN O S c)) =
      (1 + satakeN O S c) * (satakeD π S * satakeD π⁻¹ S) * (1 - satakeN O S c) by
        simp only [Matrix.mul_assoc], satakeD_mul_inv hπ, Matrix.mul_one, h]
  inv_val := by
    have h : (1 - satakeN O S c) * (1 + satakeN O S c) = 1 := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, satakeN_mul_self, Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul]; abel
    rw [show satakeD π⁻¹ S * (1 - satakeN O S c) * ((1 + satakeN O S c) * satakeD π S) =
      satakeD π⁻¹ S * ((1 - satakeN O S c) * (1 + satakeN O S c)) * satakeD π S by
        simp only [Matrix.mul_assoc], h, Matrix.mul_one, satakeD_inv_mul hπ]
def satakeU (S : Finset (Fin n)) (c : satakePairs S → O) : GL (Fin n) L where
  val := 1 + satakeN O S c
  inv := 1 - satakeN O S c
  val_inv := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, satakeN_mul_self, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]; abel
  inv_val := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, satakeN_mul_self, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]; abel
def satakeP (σ : Equiv.Perm (Fin n)) : GL (Fin n) L where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
abbrev satakeRes (π : O) : Type := O ⧸ Ideal.span {π}
def satakeSec (π : O) (r : satakeRes O π) : O :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {π})) r
def satakeRep (π : O) (hπ : (π : L) ≠ 0) (j : ℕ)
    (i : Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes O π) : GL (Fin n) L :=
  satakeGL O hπ i.1.1 (fun p => satakeSec O π (i.2 p))
end Formalism.UG.P


