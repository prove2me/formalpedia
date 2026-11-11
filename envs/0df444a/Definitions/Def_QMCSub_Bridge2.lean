-- Prove2me | Definitions.Def_QMCSub_Bridge2
-- name    : QMCSub_Bridge2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:20:24.270201+00:00
-- url     : https://prove2.me/theorems/0964759d-defe-4990-99e9-0a9087fe4028
-- title:
--   The outer loop of the program is the integer subgradient iteration
-- statement:
--   On list representations of an integer Laplacian $L$ and an iterate $u$, one guarded outer step of the program equals one step of the integer subgradient iteration whenever the size guards are inactive. Consequently the whole outer loop returns the final iterate $u^{(T)}$ and the accumulated value $P$ of the integer iteration. The file also bounds $P$ and the entries of the shifted matrix.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter
import Definitions.Def_QMCSub_Step
import Definitions.Def_QMCSub_Bridge1

/-!
The outer loop of the program in terms of the integer subgradient iteration.
-/

namespace QMCSub
open Matrix
open scoped BigOperators

variable {n : ℕ}

theorem shiftMat_toM (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (u : Fin n → ℤ) :
    shiftMat (List.range n) (toM L) (σ : ℚ) (toV u) = toM (Mz L σ u) := by
  show (List.range n).map (fun i => (List.range n).map (fun j =>
      gm (toM L) i j + (if i = j then (σ : ℚ) + gv (toV u) i else 0))) =
    List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => ((Mz L σ u i j : ℤ) : ℚ)))
  apply map_range_congr
  intro i
  apply map_range_congr
  intro j
  rw [gm_toM, gv_toV]
  unfold Mz
  rw [Matrix.add_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem diagSum_toM (A : Matrix (Fin n) (Fin n) ℤ) :
    diagSum (List.range n) (toM A) = ((A.trace : ℤ) : ℚ) := by
  unfold diagSum
  rw [sum_range_congr n (fun i => gm (toM A) i i) (fun i : Fin n => ((A i i : ℤ) : ℚ))
    (fun i => gm_toM A i i)]
  simp [Matrix.trace]

theorem lapDot_toM (A B : Matrix (Fin n) (Fin n) ℤ) :
    lapDot (List.range n) (toM A) (toM B) = ((∑ i, ∑ j, A i j * B i j : ℤ) : ℚ) := by
  unfold lapDot
  rw [sum_range_congr n
    (fun i => ((List.range n).map (fun j => gm (toM A) i j * gm (toM B) i j)).sum)
    (fun i : Fin n => ∑ j : Fin n, ((A i j : ℤ) : ℚ) * ((B i j : ℤ) : ℚ))
    (fun i => sum_range_congr n (fun j => gm (toM A) i j * gm (toM B) i j) _
      (fun j => by rw [gm_toM, gm_toM]))]
  push_cast
  rfl

theorem lapQ_nonneg {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) : 0 ≤ ∑ i, ∑ j, L i j * Qz L σ K u i j := by
  have h := psd_trace_mul_nonneg hLap.psd (castM_Qz_psd hLap.symm σ K u)
  have hsum : (castM L * castM (Qz L σ K u)).trace =
      ((∑ i, ∑ j, L i j * Qz L σ K u i j : ℤ) : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, castM_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Qz_symm hLap.symm σ K u j i]
  rw [hsum] at h
  exact_mod_cast h

theorem pz_nonneg {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) : 0 ≤ pz L σ K u := by
  unfold pz
  exact Int.ediv_nonneg (mul_nonneg (Int.natCast_nonneg n) (lapQ_nonneg hLap σ K u))
    (tauz_nonneg hLap.symm σ K u)

theorem pz_le_int {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (σ : ℤ) (K : ℕ)
    (u : Fin n → ℤ) : pz L σ K u ≤ n * L.trace := by
  have h1 := pz_le_pt hLap.symm σ K u
  have h2 := pt_le hLap σ K u
  have h3 : (pz L σ K u : ℝ) ≤ ((n * L.trace : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

theorem Pz_bounds {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (η σ : ℤ)
    (K : ℕ) (k : ℕ) : 0 ≤ Pz L η σ K k ∧ Pz L η σ K k ≤ k * (n * L.trace) := by
  unfold Pz
  constructor
  · exact Finset.sum_nonneg (fun j _ => pz_nonneg hLap σ K _)
  · calc ∑ j ∈ Finset.range k, pz L σ K (useq L η σ K j)
        ≤ ∑ _j ∈ Finset.range k, ((n : ℤ) * L.trace) :=
          Finset.sum_le_sum (fun j _ => pz_le_int hLap σ K _)
      _ = k * (n * L.trace) := by simp

theorem Mz_entry_le (L : Matrix (Fin n) (Fin n) ℤ) (σ : ℤ) (u : Fin n → ℤ) (lam s2 : ℕ)
    (hL : ∀ a b, (L a b).natAbs ≤ lam) (hu : ∀ a, (σ + u a).natAbs ≤ s2) (a b : Fin n) :
    (Mz L σ u a b).natAbs ≤ lam + s2 := by
  unfold Mz
  rw [Matrix.add_apply, Matrix.diagonal_apply]
  split_ifs with h
  · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add (hL a b) (hu a))
  · rw [add_zero]
    exact (hL a b).trans (Nat.le_add_right _ _)

/-- One guarded outer step is an honest step of the integer iteration when everything fits. -/
theorem outerStep_toV {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (η σ : ℤ)
    (K : ℕ) (hη : 0 ≤ η) (fK pI pO : List Unit) (hfuel : fK.length = 2 * K)
    (hpI : 1 ≤ pI.length) (hpO : 1 ≤ pO.length) (u : Fin n → ℤ) (P : ℤ)
    (hI : ∀ m, m ≤ fK.length → ∀ a b, ((Mz L σ u ^ m) a b).natAbs < 2 ^ pI.length)
    (hU : ∀ i, (stepU L η σ K u i).natAbs < 2 ^ pO.length)
    (hP : (P + pz L σ K u).natAbs < 2 ^ pO.length) :
    outerStep (List.range n, toM L, fK, pI, pO, (η : ℚ), (σ : ℚ)) (toV u, (P : ℚ)) =
      (toV (stepU L η σ K u), ((P + pz L σ K u : ℤ) : ℚ)) := by
  have hpow : powQ (List.range n, toM L, fK, pI, pO, (η : ℚ), (σ : ℚ)) (toV u) =
      toM (Qz L σ K u) := by
    show matPow (List.range n) (shiftMat (List.range n) (toM L) (σ : ℚ) (toV u)) pI fK = _
    rw [shiftMat_toM, matPow_toM _ pI fK hpI hI, hfuel]
    rfl
  have hτ0 := tauz_nonneg hLap.symm σ K u
  unfold outerStep
  simp only [hpow, diagSum_toM, lapDot_toM, List.length_range]
  apply Prod.ext
  · show (List.range n).map (fun i => capQ pO (gv (toV u) i + (η : ℚ) -
        qfloor ((η : ℚ) * (n : ℚ) * gm (toM (Qz L σ K u)) i i /
          (((Qz L σ K u).trace : ℤ) : ℚ)))) =
      List.ofFn (fun i : Fin n => ((stepU L η σ K u i : ℤ) : ℚ))
    apply map_range_congr
    intro i
    rw [gv_toV, gm_toM]
    have hq : (η : ℚ) * (n : ℚ) * ((Qz L σ K u i i : ℤ) : ℚ) / (((Qz L σ K u).trace : ℤ) : ℚ) =
        ((η * n * Qz L σ K u i i : ℤ) : ℚ) / ((tauz L σ K u : ℤ) : ℚ) := by
      push_cast
      rfl
    rw [hq, qfloor_div _ _
      (mul_nonneg (mul_nonneg hη (Int.natCast_nonneg n)) (Qz_diag_nonneg hLap.symm σ K u i)) hτ0]
    have hval : (u i : ℚ) + (η : ℚ) - (((η * n * Qz L σ K u i i) / tauz L σ K u : ℤ) : ℚ) =
        ((stepU L η σ K u i : ℤ) : ℚ) := by
      unfold stepU dz
      push_cast
      rfl
    rw [hval, capQ_int pO _ hpO (hU i)]
  · show capQ pO ((P : ℚ) + qfloor ((n : ℚ) *
        (((∑ i, ∑ j, L i j * Qz L σ K u i j : ℤ) : ℚ)) / (((Qz L σ K u).trace : ℤ) : ℚ))) = _
    have hq : (n : ℚ) * (((∑ i, ∑ j, L i j * Qz L σ K u i j : ℤ) : ℚ)) /
        (((Qz L σ K u).trace : ℤ) : ℚ) =
        ((n * ∑ i, ∑ j, L i j * Qz L σ K u i j : ℤ) : ℚ) / ((tauz L σ K u : ℤ) : ℚ) := by
      push_cast
      rfl
    rw [hq, qfloor_div _ _ (mul_nonneg (Int.natCast_nonneg n) (lapQ_nonneg hLap σ K u)) hτ0]
    have hval : (P : ℚ) + (((n * ∑ i, ∑ j, L i j * Qz L σ K u i j) / tauz L σ K u : ℤ) : ℚ) =
        ((P + pz L σ K u : ℤ) : ℚ) := by
      unfold pz
      push_cast
      rfl
    rw [hval, capQ_int pO _ hpO hP]

/-- The whole outer loop is the integer iteration when all guards are inactive. -/
theorem run_eq {L : Matrix (Fin n) (Fin n) ℤ} {w : ℤ} (hLap : LapHyp L w) (η σ : ℤ) (K : ℕ)
    (hη : 0 ≤ η) (fK pI pO fT : List Unit) (hfuel : fK.length = 2 * K)
    (hpI : 1 ≤ pI.length) (hpO : 1 ≤ pO.length)
    (hI : ∀ k, k < fT.length → ∀ m, m ≤ fK.length → ∀ a b,
      ((Mz L σ (useq L η σ K k) ^ m) a b).natAbs < 2 ^ pI.length)
    (hU : ∀ k, k ≤ fT.length → ∀ i, (useq L η σ K k i).natAbs < 2 ^ pO.length)
    (hP : ∀ k, k ≤ fT.length → (Pz L η σ K k).natAbs < 2 ^ pO.length) :
    (gfold outerStep fT ((List.range n, toM L, fK, pI, pO, (η : ℚ), (σ : ℚ)),
        ((List.range n).map (fun _ => (0 : ℚ)), (0 : ℚ)))).2 =
      (toV (useq L η σ K fT.length), ((Pz L η σ K fT.length : ℤ) : ℚ)) := by
  rw [gfold_snd]
  have hinit : ((List.range n).map (fun _ => (0 : ℚ)), (0 : ℚ)) =
      (toV (useq L η σ K 0), ((Pz L η σ K 0 : ℤ) : ℚ)) := by
    apply Prod.ext
    · show (List.range n).map (fun _ => (0 : ℚ)) =
        List.ofFn (fun i : Fin n => ((useq L η σ K 0 i : ℤ) : ℚ))
      apply map_range_congr
      intro i
      rw [useq_zero]
      simp
    · simp [Pz]
  rw [hinit]
  have key : ∀ k, k ≤ fT.length →
      (outerStep (List.range n, toM L, fK, pI, pO, (η : ℚ), (σ : ℚ)))^[k]
        (toV (useq L η σ K 0), ((Pz L η σ K 0 : ℤ) : ℚ)) =
      (toV (useq L η σ K k), ((Pz L η σ K k : ℤ) : ℚ)) := by
    intro k
    induction k with
    | zero =>
        intro _
        rfl
    | succ k ih =>
        intro hk
        have hk' : k < fT.length := hk
        have hPsucc : Pz L η σ K (k + 1) = Pz L η σ K k + pz L σ K (useq L η σ K k) := by
          unfold Pz
          rw [Finset.sum_range_succ]
        rw [Function.iterate_succ_apply', ih hk'.le,
          outerStep_toV hLap η σ K hη fK pI pO hfuel hpI hpO (useq L η σ K k) (Pz L η σ K k)
            (hI k hk') (fun i => by rw [← useq_succ]; exact hU (k + 1) hk i)
            (by rw [← hPsucc]; exact hP (k + 1) hk),
          ← useq_succ, ← hPsucc]
  exact key _ le_rfl

end QMCSub


