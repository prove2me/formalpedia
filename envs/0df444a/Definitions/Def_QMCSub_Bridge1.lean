-- Prove2me | Definitions.Def_QMCSub_Bridge1
-- name    : QMCSub_Bridge1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:19:14.096004+00:00
-- url     : https://prove2.me/theorems/95783fc1-449a-4925-a971-9524dfdc1de5
-- title:
--   The guarded matrix-power loop computes honest matrix powers
-- statement:
--   Integer vectors and matrices are represented as lists of rationals. On such inputs one guarded multiplication equals the matrix product whenever the product's entries fit the bit-size guard, so the inner loop returns $M^{\ell}$ after $\ell$ steps. Entries of $M^m$ are bounded by $(n\mu)^m$ when $|M_{ij}|\le\mu$, which gives an explicit guard length under which the loop is exact. The file also identifies the program's rounding with the integer floor.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_Iter

/-!
List representations of integer vectors and matrices, and the inner (matrix power) loop of the
program in terms of honest matrix powers.
-/

namespace QMCSub
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- An integer vector as a list of rationals. -/
def toV (u : Fin n → ℤ) : Vec := List.ofFn (fun i => (u i : ℚ))

/-- An integer matrix as a list of rows of rationals. -/
def toM (A : Matrix (Fin n) (Fin n) ℤ) : Mat :=
  List.ofFn (fun i => List.ofFn (fun j => (A i j : ℚ)))

theorem gv_toV (u : Fin n → ℤ) (i : Fin n) : gv (toV u) i.val = (u i : ℚ) := by
  simp [gv, toV]

theorem gm_toM (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    gm (toM A) i.val j.val = (A i j : ℚ) := by
  simp [gm, toM]

theorem map_range_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem map_range_congr {α : Type*} (n : ℕ) (f : ℕ → α) (g : Fin n → α)
    (h : ∀ i : Fin n, f i.val = g i) : (List.range n).map f = List.ofFn g := by
  rw [map_range_ofFn]
  congr 1
  funext i
  exact h i

theorem sum_range_congr (n : ℕ) (f : ℕ → ℚ) (g : Fin n → ℚ)
    (h : ∀ i : Fin n, f i.val = g i) : ((List.range n).map f).sum = ∑ i, g i := by
  rw [map_range_congr n f g h, List.sum_ofFn]

/-- The size guard is inactive on small integers. -/
theorem capQ_int (pad : List Unit) (z : ℤ) (h1 : 1 ≤ pad.length)
    (hz : z.natAbs < 2 ^ pad.length) : capQ pad (z : ℚ) = (z : ℚ) := by
  unfold capQ fitsQ
  have hs : z.natAbs.size ≤ pad.length := Nat.size_le.mpr hz
  rw [Rat.num_intCast, Rat.den_intCast]
  simp [hs, h1]

theorem qfloor_eq_floor (q : ℚ) (hq : 0 ≤ q) : qfloor q = ((⌊q⌋ : ℤ) : ℚ) := by
  unfold qfloor
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have h : ((q.num.natAbs / q.den : ℕ) : ℤ) = ⌊q⌋ := by
    rw [Rat.floor_def', Int.natCast_div, Int.natAbs_of_nonneg hnum]
  rw [← h, Int.cast_natCast]

theorem qfloor_div (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    qfloor ((a : ℚ) / (b : ℚ)) = ((a / b : ℤ) : ℚ) := by
  rw [qfloor_eq_floor _ (div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb))]
  congr 1
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  simpa using Rat.floor_intCast_div_natCast a m

/-- One guarded multiplication is an honest multiplication when the result fits. -/
theorem innerStep_toM (M Pm : Matrix (Fin n) (Fin n) ℤ) (pad : List Unit)
    (h1 : 1 ≤ pad.length) (hfit : ∀ a b, ((Pm * M) a b).natAbs < 2 ^ pad.length) :
    innerStep (List.range n, toM M, pad) (toM Pm) = toM (Pm * M) := by
  show (List.range n).map (fun i => (List.range n).map (fun j =>
      capQ pad (((List.range n).map (fun k => gm (toM Pm) i k * gm (toM M) k j)).sum))) =
    List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => (((Pm * M) i j : ℤ) : ℚ)))
  apply map_range_congr
  intro i
  apply map_range_congr
  intro j
  rw [sum_range_congr n _ (fun k : Fin n => ((Pm i k : ℤ) : ℚ) * ((M k j : ℤ) : ℚ))
    (fun k => by rw [gm_toM, gm_toM])]
  have h : (∑ k : Fin n, ((Pm i k : ℤ) : ℚ) * ((M k j : ℤ) : ℚ)) = (((Pm * M) i j : ℤ) : ℚ) := by
    rw [Matrix.mul_apply]
    push_cast
    rfl
  rw [h, capQ_int pad _ h1 (hfit i j)]

theorem idMat_range : idMat (List.range n) = toM (1 : Matrix (Fin n) (Fin n) ℤ) := by
  show (List.range n).map (fun i => (List.range n).map (fun j => if i = j then (1 : ℚ) else 0)) =
    List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n =>
      (((1 : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ℚ)))
  apply map_range_congr
  intro i
  apply map_range_congr
  intro j
  rw [Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h']

/-- The inner loop computes the honest matrix power when all intermediate powers fit. -/
theorem matPow_toM (M : Matrix (Fin n) (Fin n) ℤ) (pad fuel : List Unit) (h1 : 1 ≤ pad.length)
    (hfit : ∀ m, m ≤ fuel.length → ∀ a b, ((M ^ m) a b).natAbs < 2 ^ pad.length) :
    matPow (List.range n) (toM M) pad fuel = toM (M ^ fuel.length) := by
  unfold matPow
  rw [gfold_snd, idMat_range]
  have key : ∀ m, m ≤ fuel.length →
      (innerStep (List.range n, toM M, pad))^[m] (toM (1 : Matrix (Fin n) (Fin n) ℤ)) =
        toM (M ^ m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
    | succ m ih =>
        intro hm
        rw [Function.iterate_succ_apply', ih (Nat.le_of_succ_le hm),
          innerStep_toM M (M ^ m) pad h1 (by rw [← pow_succ]; exact hfit (m + 1) hm), ← pow_succ]
  exact key _ le_rfl

/-- Entries of matrix powers grow at most geometrically. -/
theorem pow_entry_le (M : Matrix (Fin n) (Fin n) ℤ) (μ : ℕ) (hμ : ∀ a b, (M a b).natAbs ≤ μ)
    (m : ℕ) : ∀ a b, ((M ^ m) a b).natAbs ≤ (n * μ) ^ m := by
  induction m with
  | zero =>
      intro a b
      rw [pow_zero, pow_zero, Matrix.one_apply]
      split_ifs <;> simp
  | succ m ih =>
      intro a b
      rw [pow_succ, Matrix.mul_apply]
      calc (∑ k, (M ^ m) a k * M k b).natAbs
          ≤ ∑ k, ((M ^ m) a k * M k b).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ _k : Fin n, (n * μ) ^ m * μ := by
            apply Finset.sum_le_sum
            intro k _
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul (ih a k) (hμ k b)
        _ = (n * μ) ^ (m + 1) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            ring

/-- A convenient sufficient condition for all powers up to `len` to fit the pad. -/
theorem pow_fits (M : Matrix (Fin n) (Fin n) ℤ) (μ b len : ℕ)
    (hμ : ∀ a b, (M a b).natAbs ≤ μ) (hb : n * μ ≤ 2 ^ b) (m : ℕ) (hm : m ≤ len) (a c : Fin n) :
    ((M ^ m) a c).natAbs < 2 ^ (1 + len * b) := by
  have h1 := pow_entry_le M μ hμ m a c
  have h2 : (n * μ) ^ m ≤ (2 ^ b) ^ m := Nat.pow_le_pow_left hb m
  have h3 : (2 ^ b) ^ m = 2 ^ (b * m) := by rw [← pow_mul]
  have h4 : 2 ^ (b * m) ≤ 2 ^ (len * b) :=
    Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact Nat.mul_le_mul_right b hm)
  have h5 : 2 ^ (len * b) < 2 ^ (1 + len * b) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end QMCSub


