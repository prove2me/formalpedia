-- Prove2me | Definitions.Def_QMCLeafB_htop_ledgerW_m7
-- name    : QMCLeafB_htop_ledgerW_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:16:14.634521+00:00
-- url     : https://prove2.me/theorems/0489d95d-0e4e-4605-993e-2adc1580be99
-- title:
--   QMCLeafB htop_ledgerW_m7
-- statement:
--   # leaf B phase 16 — the size ledger at the lower-body round `roundW` (m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_ledgerG_m3
import Definitions.Def_QMCLeafB_unionShallow
/-
# leaf B phase 16 — the size ledger at the lower-body round `roundW` (m7)

`Check_htop_oklower_m7` supplies the round whose `ok` branch is the *lower* body (so `RunParts.hcert`
and m5's `hmem` are free: `relaxMem_of_oracleV_ok`).  Its size ledger is the one thing m3's `MszG`
work does not cover, because `roundV`'s cut branch uses `oracleV`'s normal rather than `oracleR`'s.

Everything transfers, because `MszG`'s cap `capRecG` does not look at the recorded normal at all —
only `aRec` does, and `oracleV`'s answer set is the same four values as `oracleR`'s
(`vecMulVecF (pivAns s).2`, `[]`, `stA s`, `diagSignF (stN s, stX s)`), so m6's
`oracleR_length_le` proof applies verbatim with the branch test changed.

`roundW` is `roundOk` above the campaign slack and `roundV` below it, and it is `HtopFinish.roundU`
with the lower-body engine instead of the shelf one; its ledger is the two branch facts plus the cap.

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.LedgerW

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram
open QMCLeafB.RoundSizeM6
open QMCLeafB.CapGuard
open QMCLeafB.OkLower

theorem MszG_roundOk_le (s : RSt) : MszG (roundOk s) ≤ MszG s + 6 :=
  le_of_eq (QMCLeafB.CapGuard.MszG_roundOk s)

theorem enc_roundOk_le (s : RSt) :
    (enc (roundOk s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  rw [QMCLeafB.CapGuard.enc_roundOk]
  exact le_max_left _ _

/-! ## 1.  m6's `oracleR_length_le` at the lower-body oracle -/

theorem oracleV_length_le (s : RSt) :
    (encodeList (enc : ℚ → List Bool) (oracleV s).2).length
      ≤ capRec s (max (aX s) (capX s)) := by
  set H := max (aX s) (capX s) with hHdef
  have hXd : aX s ≤ H := le_max_left _ _
  have hXh : ∀ q ∈ stX s, HasHeight q H := by
    intro q hq
    have h1 : HasHeight q (aX s) := by
      have h0 := Ratio.height_length q
      exact h0.mono (entries_le_aX hq)
    exact h1.mono hXd
  have hK0 : Lmu s + Ld s ≤ H + Lmu s + Ld s := by omega
  have hAns := runPivL_ans_height (mu := stMu s) (d := stD s) (L := Lmu s) (D := Ld s)
    (N := stN s) (K0 := H + Lmu s + Ld s) (Ratio.height_length (stMu s)) (d_le_two_pow_Ld s)
    hK0 (toRows_rowsHeight (fun q hq => (hXh q hq).mono (by omega)))
    (fun z hz => absurd hz (List.not_mem_nil))
    (toRows_rowsWidth (stN s, stX s))
    (fun z hz => absurd hz (List.not_mem_nil))
    (toRows_length_le (stN s, stX s))
  have hNcap : (stN s * stN s) * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21)
      ≤ capRec s H := by
    simp only [capRec]
    omega
  have hAterm : (encodeList (enc : ℚ → List Bool) (stA s)).length ≤ capRec s H := by
    simp only [capRec]
    omega
  have hDterm : (stN s * stN s) * 33 ≤ capRec s H := by
    simp only [capRec]
    omega
  have hV : (encodeList (enc : ℚ → List Bool) (vecMulVecF (stN s, (pivAns s).2))).length
      ≤ (stN s * stN s) * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21) := by
    have h1 : (encodeList (enc : ℚ → List Bool) (vecMulVecF (stN s, (pivAns s).2))).length
        ≤ (vecMulVecF (stN s, (pivAns s).2)).length
            * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21) := by
      refine encodeList_length_le _ _ ?_
      exact vecMulVecF_height hAns
    have h2 := vecMulVecF_length_le (stN s, (pivAns s).2)
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)
  have hD : (encodeList (enc : ℚ → List Bool) (diagSignF (stN s, stX s))).length
      ≤ (stN s * stN s) * 33 := by
    have h1 : (encodeList (enc : ℚ → List Bool) (diagSignF (stN s, stX s))).length
        ≤ (diagSignF (stN s, stX s)).length * (6 * 1 + 21) :=
      encodeList_length_le _ 1 (diagSignF_height _)
    have h2 := diagSignF_length_le (stN s, stX s)
    calc (encodeList (enc : ℚ → List Bool) (diagSignF (stN s, stX s))).length
        ≤ (diagSignF (stN s, stX s)).length * (6 * 1 + 21) := h1
      _ ≤ (diagSignF (stN s, stX s)).length * 33 :=
          Nat.mul_le_mul_left _ (by norm_num)
      _ ≤ (stN s * stN s) * 33 := Nat.mul_le_mul_right _ h2
  by_cases hdv : dvR s = 0
  · have h1 : (oracleV s).2 = (threshV s).2 := by simp only [oracleV, if_pos hdv]
    rw [h1]
    by_cases hth : fvR s ≤ levelOf s
    · have h2 : (threshV s).2 = (pivCut s).2 := by simp only [threshV, if_pos hth]
      rw [h2]
      by_cases hp : (pivAns s).1 = true
      · have h3 : (pivCut s).2 = vecMulVecF (stN s, (pivAns s).2) := by
          simp only [pivCut, pivCutF, if_pos hp]
        rw [h3]
        exact le_trans hV hNcap
      · have h3 : (pivCut s).2 = ([] : List ℚ) := by
          simp only [pivCut, pivCutF, if_neg hp]
        rw [h3, EncodedList.nil]
        simp
    · have h2 : (threshV s).2 = stA s := by simp only [threshV, if_neg hth]
      rw [h2]
      exact hAterm
  · have h1 : (oracleV s).2 = diagSignF (stN s, stX s) := by
      simp only [oracleV, if_neg hdv]
    rw [h1]
    exact le_trans hD hDterm

/-! ## 2.  The cut branch of `roundV` -/

theorem roundV_eq (s : RSt) : roundV s = if (oracleV s).1 then roundCutV s else roundOk s := rfl

theorem stN_roundCutV (s : RSt) : stN (roundCutV s) = stN s := rfl
theorem stA_roundCutV (s : RSt) : stA (roundCutV s) = stA s := rfl
theorem stT_roundCutV (s : RSt) : stT (roundCutV s) = stT s := rfl
theorem stMu_roundCutV (s : RSt) : stMu (roundCutV s) = stMu s := rfl
theorem stD_roundCutV (s : RSt) : stD (roundCutV s) = stD s := rfl
theorem stX_roundCutV (s : RSt) : stX (roundCutV s) = snapY s := rfl
theorem stRec_roundCutV (s : RSt) : stRec (roundCutV s) = (oracleV s).2 := rfl
theorem skel_roundCutV (s : RSt) : skel (roundCutV s) = skel s := by
  simp only [skel, stN_roundCutV, stA_roundCutV, stT_roundCutV, stMu_roundCutV, stD_roundCutV]
theorem Lmu_roundCutV (s : RSt) : Lmu (roundCutV s) = Lmu s := by simp only [Lmu, stMu_roundCutV]
theorem Ld_roundCutV (s : RSt) : Ld (roundCutV s) = Ld s := by simp only [Ld, stD_roundCutV]

theorem aX_roundCutV_le_G (s : RSt) (hn : (stX s).length = stN s * stN s) :
    aX (roundCutV s) ≤ max (aX s) (capXG s) := by
  have hX : stX (roundCutV s) = snapY s := stX_roundCutV s
  have h1 : aX (roundCutV s) ≤ capX s := by
    simp only [aX, hX]
    have h2 : (encodeList (enc : ℚ → List Bool) (snapY s)).length
        ≤ (snapY s).length * (6 * (Lmu s + Ld s) + 21) :=
      encodeList_length_le _ _ (snapY_height s)
    have h3 : (snapY s).length ≤ stN s * stN s := snapY_length_le s
    have h4 : (snapY s).length * (6 * (Lmu s + Ld s) + 21)
        ≤ (stN s * stN s) * (6 * (Lmu s + Ld s) + 21) := Nat.mul_le_mul_right _ h3
    exact le_trans h2 (le_trans h4 (le_refl _))
  rw [capX_eq_capXG s hn] at h1
  exact le_trans h1 (le_max_right _ _)

theorem aRec_roundCutV_le_G (s : RSt) (hn : (stX s).length = stN s * stN s) :
    aRec (roundCutV s) ≤ capRecG s (max (aX s) (capXG s)) := by
  have h1 := oracleV_length_le s
  rw [capX_eq_capXG s hn] at h1
  have h2 : capRec s (max (aX s) (capXG s)) ≤ capRecG s (max (aX s) (capXG s)) :=
    capRec_le_capRecG s (stN_le_lenX_succ s hn) _
  simp only [aRec, stRec_roundCutV]
  exact le_trans h1 h2

theorem capRecL_roundCutV (s : RSt) (N H : ℕ) :
    capRecL (roundCutV s) N H = capRecL s N H := by
  simp only [capRecL, stA_roundCutV, Lmu_roundCutV, Ld_roundCutV]

theorem capRecG_roundCutV_le (s : RSt) (hn : (stX s).length = stN s * stN s) (H : ℕ) :
    capRecG (roundCutV s) H ≤ capRecG s H := by
  rw [capRecG_eq_capRecL, capRecG_eq_capRecL, capRecL_roundCutV]
  refine capRecL_mono_N s ?_
  rw [stX_roundCutV, hn]
  exact snapY_length_le s

theorem capXG_roundCutV_le (s : RSt) (hn : (stX s).length = stN s * stN s) :
    capXG (roundCutV s) ≤ capXG s := by
  have hlen : (stX (roundCutV s)).length ≤ (stX s).length := by
    rw [stX_roundCutV, hn]
    exact snapY_length_le s
  simp only [capXG, Lmu_roundCutV, Ld_roundCutV]
  exact Nat.mul_le_mul_right _ hlen

/-! ## 3.  The ledger at `roundV` (normalised states) -/

theorem MszG_roundV_cut_le_G (s : RSt) (hn : (stX s).length = stN s * stN s)
    (h : (oracleV s).1 = true) : MszG (roundV s) ≤ MszG s + 6 := by
  have hEq : roundV s = roundCutV s := by rw [roundV_eq, if_pos h]
  have hX : aX (roundV s) ≤ max (aX s) (capXG s) := by
    rw [hEq]; exact aX_roundCutV_le_G s hn
  have hR : aRec (roundV s) ≤ capRecG s (max (aX s) (capXG s)) := by
    rw [hEq]; exact aRec_roundCutV_le_G s hn
  have hXG : capXG (roundV s) ≤ max (aX s) (capXG s) := by
    rw [hEq]
    exact le_trans (capXG_roundCutV_le s hn) (le_max_right _ _)
  have hRG : capRecG (roundV s) (max (aX (roundV s)) (capXG (roundV s)))
      ≤ capRecG s (max (aX s) (capXG s)) := by
    refine le_trans (capRecG_mono_H (roundV s) (max_le hX hXG)) ?_
    rw [hEq]
    exact capRecG_roundCutV_le s hn _
  have hoks : (stOks (roundV s)).length ≤ (stOks s).length + 1 := by
    rw [stOks_roundV, List.length_append]; simp
  have hskel : skel (roundV s) ≤ skel s := by rw [hEq, skel_roundCutV]
  exact MszG_step (s' := roundV s) hskel hoks hX hXG
    (le_trans hR (le_max_right _ _)) (le_trans hRG (le_max_right _ _))

theorem enc_roundV_cut_le_G (s : RSt) (hn : (stX s).length = stN s * stN s)
    (h : (oracleV s).1 = true) : (enc (roundV s)).length ≤ MszG s := by
  have hEq : roundV s = roundCutV s := by rw [roundV_eq, if_pos h]
  have hR : aRec (roundV s) ≤ capRecG s (max (aX s) (capXG s)) := by
    rw [hEq]; exact aRec_roundCutV_le_G s hn
  have hX : aX (roundV s) ≤ max (aX s) (capXG s) := by
    rw [hEq]; exact aX_roundCutV_le_G s hn
  have hskel : skel (roundV s) = skel s := by rw [hEq, skel_roundCutV]
  have hoks : (stOks (roundV s)).length = (stOks s).length + 1 := by
    rw [stOks_roundV, List.length_append]; simp
  rw [enc_decomp (roundV s), hskel, hoks]
  simp only [MszG]
  have hcap : capRecG s (max (aX s) (capXG s))
      ≤ skel s + 4 * max (aX s) (capXG s) + max (aRec s) (capRecG s (max (aX s) (capXG s)))
        + 6 * (stOks s).length + 6 := by omega
  have h4 : 4 * aX (roundV s) ≤ 4 * max (aX s) (capXG s) := Nat.mul_le_mul_left 4 hX
  omega

theorem MszG_roundV_le_of_normalised (s : RSt) (hn : (stX s).length = stN s * stN s) :
    MszG (roundV s) ≤ MszG s + 6 := by
  by_cases h : (oracleV s).1 = true
  · exact MszG_roundV_cut_le_G s hn h
  · have hf : (oracleV s).1 = false := by simpa using h
    rw [roundV_eq, if_neg (by rw [hf]; exact Bool.false_ne_true)]
    exact MszG_roundOk_le s

theorem enc_roundV_le_of_normalised (s : RSt) (hn : (stX s).length = stN s * stN s) :
    (enc (roundV s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  by_cases h : (oracleV s).1 = true
  · exact le_trans (enc_roundV_cut_le_G s hn h) (le_max_right _ _)
  · have hf : (oracleV s).1 = false := by simpa using h
    rw [roundV_eq, if_neg (by rw [hf]; exact Bool.false_ne_true)]
    exact enc_roundOk_le s

theorem roundV_normalised (s : RSt) (hn : (stX s).length = stN s * stN s) :
    (stX (roundV s)).length = stN (roundV s) * stN (roundV s) := by
  by_cases h : (oracleV s).1 = true
  · rw [roundV_eq, if_pos h, stX_roundCutV, stN_roundCutV]
    exact QMCLeafB.GuardedRound.snapY_length_eq s hn
  · have hf : (oracleV s).1 = false := by simpa using h
    rw [roundV_eq, if_neg (by rw [hf]; exact Bool.false_ne_true)]
    rw [QMCLeafB.GuardedRound.stX_roundOk, QMCLeafB.GuardedRound.stN_roundOk]
    exact hn

/-! ## 4.  The guarded reported round `roundWG` — the size ledger needs the guard -/

/-- **The round the leaf should run**: freeze above the campaign slack *and* off the normalised set;
the lower-body engine on the interior of a normalised state.  On the run from `init0` (normalised) the
second guard is inert, so the orbit is `roundW`'s. -/
def roundWG (s : RSt) : RSt :=
  if 0 ≤ stT s + QMCLeafB.RoundT.epsOf s then roundOk s
  else if (stX s).length = stN s * stN s then roundV s else roundOk s

theorem roundWG_of_top (s : RSt) (h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s) :
    roundWG s = roundOk s := by
  unfold roundWG; rw [if_pos h]

theorem roundWG_of_interior_normalised (s : RSt)
    (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s))
    (hn : (stX s).length = stN s * stN s) : roundWG s = roundV s := by
  unfold roundWG; rw [if_neg h, if_pos hn]

theorem roundWG_of_abnormal (s : RSt)
    (hn : ¬ ((stX s).length = stN s * stN s)) : roundWG s = roundOk s := by
  unfold roundWG
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]
  · rw [if_neg h, if_neg hn]

theorem poly_roundWG : Automatic.Poly roundWG := by
  have hlen : Automatic.Poly (fun s : RSt => (stX s).length) :=
    Automatic.Poly.comp (f := (List.length : List ℚ → ℕ)) (g := stX)
      (Automatic.Poly.list_length (α := ℚ)) poly_stX
  have hnn : Automatic.Poly (fun s : RSt => stN s * stN s) :=
    Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
      (g := fun s : RSt => (stN s, stN s)) Automatic.Poly.nat_mul
      (Automatic.Poly.pair poly_stN poly_stN)
  have hp : Automatic.Poly (fun s : RSt => decide ((stX s).length = stN s * stN s)) :=
    Automatic.Poly.nat_eq_comp hlen hnn
  unfold roundWG
  exact Automatic.Poly.ite_prop (p := fun s : RSt => 0 ≤ stT s + QMCLeafB.RoundT.epsOf s)
    QMCLeafB.OkLower.poly_regimeW poly_roundOk
    (Automatic.Poly.ite_prop
      (p := fun s : RSt => (stX s).length = stN s * stN s) hp
      QMCLeafB.OkLower.poly_roundV poly_roundOk)

theorem MszG_roundWG_le (s : RSt) : MszG (roundWG s) ≤ MszG s + 6 := by
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundWG_of_top s h]; exact MszG_roundOk_le s
  · by_cases hn : (stX s).length = stN s * stN s
    · rw [roundWG_of_interior_normalised s h hn]
      exact MszG_roundV_le_of_normalised s hn
    · rw [roundWG_of_abnormal s hn]; exact MszG_roundOk_le s

theorem enc_roundWG_le (s : RSt) :
    (enc (roundWG s)).length ≤ max ((enc s).length + 6) (MszG s) := by
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundWG_of_top s h]; exact enc_roundOk_le s
  · by_cases hn : (stX s).length = stN s * stN s
    · rw [roundWG_of_interior_normalised s h hn]
      exact enc_roundV_le_of_normalised s hn
    · rw [roundWG_of_abnormal s hn]; exact enc_roundOk_le s

theorem roundWG_iterate_normalised (s : RSt) (hn : (stX s).length = stN s * stN s) (k : ℕ) :
    (stX (roundWG^[k] s)).length = stN (roundWG^[k] s) * stN (roundWG^[k] s) := by
  induction k with
  | zero => simpa using hn
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      by_cases h : 0 ≤ stT (roundWG^[j] s) + QMCLeafB.RoundT.epsOf (roundWG^[j] s)
      · rw [roundWG_of_top _ h]
        rw [QMCLeafB.GuardedRound.stX_roundOk, QMCLeafB.GuardedRound.stN_roundOk]
        exact ih
      · rw [roundWG_of_interior_normalised _ h ih]
        exact roundV_normalised _ ih

theorem roundWG_eq_roundW (s : RSt) (hn : (stX s).length = stN s * stN s) :
    roundWG s = roundW s := by
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [roundWG_of_top s h]
    unfold roundW
    rw [if_pos h]
  · rw [roundWG_of_interior_normalised s h hn]
    unfold roundW
    rw [if_neg h]

theorem roundWG_iterate_eq_roundW (s : RSt) (hn : (stX s).length = stN s * stN s) (k : ℕ) :
    roundWG^[k] s = roundW^[k] s := by
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hnorm := roundWG_iterate_normalised s hn j
      rw [ih] at hnorm
      exact roundWG_eq_roundW _ hnorm

theorem MszG_capW (s : RSt) : MszG s ≤ 11448595 * ((enc s).length + 1) ^ 6 :=
  MszG_le_pow s

#print axioms QMCLeafB.LedgerW.oracleV_length_le
#print axioms QMCLeafB.LedgerW.aX_roundCutV_le_G
#print axioms QMCLeafB.LedgerW.aRec_roundCutV_le_G
#print axioms QMCLeafB.LedgerW.capRecG_roundCutV_le
#print axioms QMCLeafB.LedgerW.capXG_roundCutV_le
#print axioms QMCLeafB.LedgerW.MszG_roundV_cut_le_G
#print axioms QMCLeafB.LedgerW.enc_roundV_cut_le_G
#print axioms QMCLeafB.LedgerW.MszG_roundV_le_of_normalised
#print axioms QMCLeafB.LedgerW.enc_roundV_le_of_normalised
#print axioms QMCLeafB.LedgerW.roundV_normalised
#print axioms QMCLeafB.LedgerW.poly_roundWG
#print axioms QMCLeafB.LedgerW.MszG_roundWG_le
#print axioms QMCLeafB.LedgerW.enc_roundWG_le
#print axioms QMCLeafB.LedgerW.roundWG_iterate_normalised
#print axioms QMCLeafB.LedgerW.roundWG_iterate_eq_roundW
#print axioms QMCLeafB.LedgerW.MszG_capW


/-! ## 5.  `htop`, the verdict read-out, and the endgame at `roundWG` -/

/-- **`htop` at `roundWG`** — from `roundW`'s, since the second guard is inert on a normalised start. -/
theorem htop_roundWG (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hoks : ∀ p, stOks (init p) = [])
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (hstT : ∀ p, stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundWG verdict T0 G t = true := by
  intro G t hlo hhi
  have h1 : QMCLeafB.FinalStroke.loopBit init roundWG verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit init roundW verdict T0 G t := by
    unfold QMCLeafB.FinalStroke.loopBit
    rw [roundWG_iterate_eq_roundW _ (hnorm _)]
  rw [h1]
  exact QMCLeafB.OkLower.htop_roundW init hoks hstT hmass T0 hpos G t hlo hhi

/-- **The verdict agreement at `roundWG`**: the run's `ok` stream is `okW`'s along `roundW`'s orbit,
i.e. the lower-body oracle's answer on the interior. -/
theorem verdict_iterate_eq_anyOk_WG {init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt}
    (hoks : ∀ p, stOks (init p) = [])
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (T : ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init roundWG verdict (fun _ _ => T) G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => QMCLeafB.OkLower.okW
            (roundW^[k] (init (QMCLeafB.FinalStroke.noTape G t)))) T := by
  have h1 : QMCLeafB.FinalStroke.loopBit init roundWG verdict (fun _ _ => T) G t
      = QMCLeafB.FinalStroke.loopBit init roundW verdict (fun _ _ => T) G t := by
    unfold QMCLeafB.FinalStroke.loopBit
    rw [roundWG_iterate_eq_roundW _ (hnorm _)]
  rw [h1]
  exact QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ (hoks _) T

/-! ## 6.  The endgame at `roundWG` -/

local instance instRequestCodingLedgerW : OAI.MetricKMedian.Binary.Automatic.Coding
    (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- `RunParts` sees the loop bit only through `hverdict`. -/
def runParts_congr {o₁ o₂ : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o₁ G t P) (h : o₂ G t = o₁ G t) :
    QMCLeafB.FinalStroke.RunParts o₂ G t P :=
  { B with hverdict := by rw [h]; exact B.hverdict }

/-- **`SolutionStatement` at the lower-body round**, from the init facts and ONE run bundle per
interior `(G,t)` at the campaign family `paramsKbc2`.  The `ok` branch of that run is a relaxation
point (`OkLower.relaxMem_of_oracleV_ok`), so m5's `hmem` needs no extra certificate. -/
theorem solution_roundWG_of_init_hd_round
    (init : QMCLeafB.FuelWire.Pkg → RSt) (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (hinit : Automatic.Poly init)
    (hnorm : ∀ p, (stX (init p)).length = stN (init p) * stN (init p))
    (hstT : ∀ p, stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (hoks : ∀ p, stOks (init p) = [])
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init roundW
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => QMCLeafB.UnionShallow.Kbc2
            (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
            * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  have hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      1 ≤ (fun G' _ => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t :=
    fun G t => QMCLeafB.UnionShallow.one_le_Kbc2_mul G
  refine QMCLeafB.UnionShallow.solution_union_shallow_final k hk
    init roundWG QMCLeafB.RoundProgram.verdict hinit poly_roundWG
    QMCLeafB.RoundProgram.poly_verdict MszG 11448595 6 6 (by norm_num)
    MszG_roundWG_le enc_roundWG_le MszG_capW hinitTape
    (fun G t _ hlo hhi => htop_roundWG init hoks hnorm hstT hmass _ hT G t hlo hhi) ?_
  intro G t hn hlo hlt
  refine runParts_congr (hd G t hn hlo hlt) ?_
  have h1 : QMCLeafB.FinalStroke.loopBit init roundWG QMCLeafB.RoundProgram.verdict
      (fun G' _ => QMCLeafB.UnionShallow.Kbc2
        (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
        * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t
      = QMCLeafB.FinalStroke.loopBit init roundW QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.UnionShallow.Kbc2
          (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
          * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G t := by
    unfold QMCLeafB.FinalStroke.loopBit
    rw [roundWG_iterate_eq_roundW _ (hnorm _)]
  exact h1

#print axioms QMCLeafB.LedgerW.runParts_congr
#print axioms QMCLeafB.LedgerW.htop_roundWG
#print axioms QMCLeafB.LedgerW.verdict_iterate_eq_anyOk_WG
#print axioms QMCLeafB.LedgerW.solution_roundWG_of_init_hd_round

end QMCLeafB.LedgerW


