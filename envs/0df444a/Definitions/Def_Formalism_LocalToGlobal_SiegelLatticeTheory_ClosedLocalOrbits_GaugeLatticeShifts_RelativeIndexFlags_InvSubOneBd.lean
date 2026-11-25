-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:17.991832+00:00
-- url     : https://prove2.me/theorems/dfaa233a-4182-4a56-98e7-b62b37d6e205
-- title:
--   Inv Sub One Bd
-- statement:
--   Definitions and structural lemmas for Inv Sub One Bd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/InvSubOneBd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K]
def Bd (m : ℕ) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < j + m → A i j = 0
theorem Bd.mono {m m' : ℕ} {A : Matrix (Fin n) (Fin n) K} (h : m' ≤ m) (hA : Bd m A) : Bd m' A :=
  fun i j hij => hA i j (by omega)
theorem Bd.mul {m m' m'' : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m' B)
    (h : m'' ≤ m + m') : Bd m'' (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (i : ℕ) < l + m
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]
theorem Bd.add {m : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Bd m A) (hB : Bd m B) : Bd m (A + B) :=
  fun i j h => by rw [Matrix.add_apply, hA i j h, hB i j h, add_zero]
theorem Bd.neg {m : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Bd m A) : Bd m (-A) :=
  fun i j h => by rw [Matrix.neg_apply, hA i j h, neg_zero]
theorem Bd_zero (m : ℕ) : Bd m (0 : Matrix (Fin n) (Fin n) K) :=
  fun i j _ => by rw [Matrix.zero_apply]
theorem Bd_one : Bd 0 (1 : Matrix (Fin n) (Fin n) K) := by
  intro i j h
  rw [Matrix.one_apply_ne]
  intro e
  rw [e] at h
  omega
theorem Bd.pow {A : Matrix (Fin n) (Fin n) K} (hA : Bd 1 A) (k : ℕ) : Bd k (A ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact Bd_one
  | succ k ih => rw [pow_succ]; exact ih.mul hA le_rfl
theorem Bd.sum {ι : Type*} {m : ℕ} {s : Finset ι} {f : ι → Matrix (Fin n) (Fin n) K}
    (h : ∀ i ∈ s, Bd m (f i)) : Bd m (∑ i ∈ s, f i) :=
  fun i j hij => by
    rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun l hl => h l hl i j hij
theorem Bd.eq_zero {A : Matrix (Fin n) (Fin n) K} (h : Bd n A) : A = 0 := by
  ext i j
  have := i.2
  exact h i j (by omega)
theorem inv_sub_one_bd (a : Matrix.GeneralLinearGroup (Fin n) K) (k : ℕ)
    (h : Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1)) :
    Bd (k + 1) (((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) := by
  have hN1 : Bd 1 (-((a : Matrix (Fin n) (Fin n) K) - 1)) := (h.mono (by omega)).neg
  have hpow : (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ n = 0 := (hN1.pow n).eq_zero
  have hba : (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
      (a : Matrix (Fin n) (Fin n) K) = 1 := by
    have e := geom_sum_mul_neg (-((a : Matrix (Fin n) (Fin n) K) - 1)) n
    rw [hpow, sub_zero, sub_neg_eq_add, add_sub_cancel] at e
    exact e
  have hinv : ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i := by
    calc ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
            (a : Matrix (Fin n) (Fin n) K) *
            ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hba, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hb0 : Bd 0 (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) :=
    Bd.sum fun i _ => (hN1.pow i).mono (Nat.zero_le _)
  have e2 : (∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) - 1 =
      -((∑ i ∈ Finset.range n, (-((a : Matrix (Fin n) (Fin n) K) - 1)) ^ i) *
        ((a : Matrix (Fin n) (Fin n) K) - 1)) := by
    rw [mul_sub, hba, mul_one]; abel
  rw [hinv, e2]
  exact (hb0.mul h (by omega)).neg
def FG (n : ℕ) (K : Type*) [Field K] (k : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {a | Bd (k + 1) ((a : Matrix (Fin n) (Fin n) K) - 1)}
  one_mem' := by
    show Bd _ (((1 : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)
    rw [Units.val_one, sub_self]; exact Bd_zero _
  mul_mem' := by
    intro a b ha hb
    show Bd _ (((a * b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)
    have e : ((a * b : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        ((a : Matrix (Fin n) (Fin n) K) - 1) * ((b : Matrix (Fin n) (Fin n) K) - 1) +
          ((a : Matrix (Fin n) (Fin n) K) - 1) + ((b : Matrix (Fin n) (Fin n) K) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e]; exact ((Bd.mul ha hb (by omega)).add ha).add hb
  inv_mem' := fun {a} ha => inv_sub_one_bd a k ha
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt


