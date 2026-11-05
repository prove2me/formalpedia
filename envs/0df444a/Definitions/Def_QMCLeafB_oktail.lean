-- Prove2me | Definitions.Def_QMCLeafB_oktail
-- name    : QMCLeafB_oktail
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:21:54.567231+00:00
-- url     : https://prove2.me/theorems/ea25fcef-676f-499c-a37f-2df261328e6a
-- title:
--   QMCLeafB oktail
-- statement:
--   # m7 (swarm `smw17fqzz`) — the `ok` tail of the guarded slack round
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_conformance_m8
/-
# m7 (swarm `smw17fqzz`) — the `ok` tail of the guarded slack round

Brick 4 (`RunParts` at the program's own orbit) needs two things about the flag stream that no
module supplies yet:

* **the `ok` rounds are a tail.**  `roundOk` freezes `(stN, stA, stX, stT, stMu, stD)` and only
  appends to `stOks`, so `okGT` is a function of the frozen data: once a round reports `ok`, every
  later round reports `ok`.  Hence one certificate at the first `ok` round serves *every* ok round
  `k < K·m` (`RunParts.hcert`), and the flag stream is eventually constant.
* **`anyOk` is monotone in the round count**, so `hverdict` proved at the campaign's `K·m` also
  holds at any larger count (and the tail makes the converse available at the small count when an
  `ok` has occurred).

This is the bookkeeping brick 4's `hcert`/`hverdict` need; it contains no geometry.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.OkTail

open QuantumMaxCutEnergy
open QMCLeafB.ConformanceM8

/-! ## 1.  `roundOk` does not move the flag -/

/-- `roundOk` keeps every field `okGT` reads: the flag of the frozen state is the old flag. -/
theorem okGT_roundOk (s : QMCLeafB.RoundProgram.RSt) :
    okGT (QMCLeafB.RoundProgram.roundOk s) = okGT s := rfl

/-- `roundOk` keeps the normalisation status. -/
theorem normalised_roundOk (s : QMCLeafB.RoundProgram.RSt)
    (h : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s) :
    (QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.roundOk s)).length
      = QMCLeafB.RoundProgram.stN (QMCLeafB.RoundProgram.roundOk s)
        * QMCLeafB.RoundProgram.stN (QMCLeafB.RoundProgram.roundOk s) := h

/-! ## 2.  The one-step tail -/

/-- **`okGT` is monotone along `roundGT`.**  On a normalised state the slack branch freezes, and on
the engine branch the state is only replaced when the oracle says `ok` (which freezes it); an
abnormal state is frozen by the guard.  In all three cases the flag can only go `false → true`. -/
theorem okGT_roundGT_of_true (s : QMCLeafB.RoundProgram.RSt) (h : okGT s = true) :
    okGT (roundGT s) = true := by
  by_cases hn : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s
  · rw [roundGT_of_normalised s hn]
    unfold QMCLeafB.RoundT.roundT
    split_ifs with hs
    · rw [okGT_roundOk]
      exact h
    · -- the engine branch: `okGT s = true` forces the oracle's `ok`, hence `round = roundOk`
      have hcut : (QMCLeafB.RoundProgram.oracleR s).1 = false := by
        by_contra hc
        have htrue : (QMCLeafB.RoundProgram.oracleR s).1 = true := by
          cases hb : (QMCLeafB.RoundProgram.oracleR s).1
          · exact absurd hb hc
          · rfl
        rw [okGT, if_pos hn, if_neg hs, htrue] at h
        simp at h
      rw [show QMCLeafB.RoundProgram.round s = QMCLeafB.RoundProgram.roundOk s from by
        unfold QMCLeafB.RoundProgram.round
        rw [hcut]
        simp]
      rw [okGT_roundOk]
      exact h
  · rw [roundGT_of_abnormal s hn, okGT_roundOk]
    exact h

/-! ## 3.  The tail along the orbit -/

/-- **Once `ok`, always `ok`** along the `roundGT` orbit. -/
theorem okGT_iterate_of_true (s : QMCLeafB.RoundProgram.RSt) :
    ∀ {j T : ℕ}, j ≤ T → okGT (roundGT^[j] s) = true → okGT (roundGT^[T] s) = true := by
  intro j T hjT h
  obtain ⟨d, rfl⟩ : ∃ d, T = j + d := ⟨T - j, by omega⟩
  have key : ∀ d, okGT (roundGT^[d] (roundGT^[j] s)) = true := by
    intro d
    induction d with
    | zero => simpa using h
    | succ d ih =>
        rw [Function.iterate_succ_apply']
        exact okGT_roundGT_of_true _ ih
  rw [Nat.add_comm j d, Function.iterate_add_apply]
  exact key d

/-! ## 4.  `anyOk` is monotone in the count -/

/-- `anyOk` over a longer prefix is at least as true. -/
theorem anyOk_mono (ok : ℕ → Bool) :
    ∀ {m n : ℕ}, m ≤ n → QMCLeafB.SimLoop.anyOk ok m = true
      → QMCLeafB.SimLoop.anyOk ok n = true := by
  intro m n hmn
  induction hmn with
  | refl => exact id
  | @step n hmn ih =>
      intro h
      rw [QMCLeafB.SimLoop.anyOk_succ]
      rw [ih h]
      simp

/-- **The `ok` tail makes `anyOk` independent of the count once the first `ok` is in.** -/
theorem anyOk_iterate_eq_true {s : QMCLeafB.RoundProgram.RSt} {j T : ℕ} (hjT : j + 1 ≤ T)
    (h : okGT (roundGT^[j] s) = true) :
    QMCLeafB.SimLoop.anyOk (fun k => okGT (roundGT^[k] s)) T = true := by
  refine anyOk_mono _ hjT ?_
  rw [QMCLeafB.SimLoop.anyOk_succ, h]
  simp

#print axioms QMCLeafB.OkTail.okGT_roundOk
#print axioms QMCLeafB.OkTail.okGT_roundGT_of_true
#print axioms QMCLeafB.OkTail.okGT_iterate_of_true
#print axioms QMCLeafB.OkTail.anyOk_mono
#print axioms QMCLeafB.OkTail.anyOk_iterate_eq_true

end QMCLeafB.OkTail


