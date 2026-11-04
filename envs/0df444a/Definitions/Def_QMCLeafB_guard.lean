-- Prove2me | Definitions.Def_QMCLeafB_guard
-- name    : QMCLeafB_guard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:50:54.069116+00:00
-- url     : https://prove2.me/theorems/0b0d8786-048f-43d6-b578-b015ec895341
-- title:
--   QMCLeafB guard
-- statement:
--   # leaf B phase 14 — the normalisation guard on `RoundProgram.round` (member m1, direction d7, round 2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_roundSizes
import Definitions.Def_QMCLeafB_roundsize_m6
/-
# leaf B phase 14 — the normalisation guard on `RoundProgram.round` (member m1, direction d7, round 2)

## Why

m6's `round-ledger-plan.md` identifies the last structural defect of the size slot at `RSt`: the round
rebuilds the primal code from `n`
(`stepFun`/`smulRaw` keep only `min n |X|` entries per side, `Check_matq_update_m4.stepFun_length`,
`Check_roundsize_m6.smulRaw_length`), while `n` itself is only `log n` bits of the state.  So from a
*non-normalised* state (`|X| ≠ n²`, e.g. `n = 10^12`, `X = []`, a few hundred bits) the orbit climbs
`|X| : 0 → n → n² → …` and no polynomial `sizes` bounds it: `hM` is false for `Msz`'s `n²`-based caps.

## The repair

Freeze the state unless it is normalised (`|X| = n·n`):

    roundG s := if (stX s).length = stN s * stN s then round s else roundOk s

On every state reachable from `RStInit.init0` the guard is inert — the initial state is normalised
(`RStInit.init_normalised`, `RStInit.stA_length_init0`, this file's §1) and a `cut` round of a
normalised state is normalised again (`snapY_length_eq`) — so the run is *literally* the same iterate
(`roundG_iterate_eq_round`).  Off the reachable set the state freezes, so the only growth left is the
`ok` flag, which `Msz`'s `max`-form already absorbs.

## What is here

* §1 `snapY_length_eq : (stX s).length = n² → (snapY s).length = n²` — the normalisation of the cut
  branch (the exact form of `Check_roundsize_m6.snapY_length_le`).
* §2 `roundG`, `poly_roundG`, `roundG_of_normalised`, `roundG_normalised`.
* §3 the normalised orbit from `init0`: `stX_length_iterate_roundG`, and the agreement
  `roundG_iterate_eq_round : roundG^[j] (init0 p) = round^[j] (init0 p)`.
* §4 the verdict read-out for `roundG` (`stOks_roundG`, `verdict_iterate_eq_anyOk_G`,
  `loopBit_eq_anyOk_G`), so the `hverdict` slot can be closed at the guarded loop too.

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.GuardedRound

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.RStInit

local instance instRequestCodingGuard :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  A `cut` round of a normalised state is normalised -/

/-- **The snap of a normalised shape has `n²` entries.**  `stepFun` keeps `n²` entries of a normalised
code (`stepFun_length`), `smulRaw` keeps `(take n).length²`, and `n ≤ n²` makes that `n²` again. -/
theorem snapY_length_eq (s : RSt) (h : (stX s).length = stN s * stN s) :
    (snapY s).length = stN s * stN s := by
  have ht : (stepY s).length = stN s * stN s :=
    QMCLeafB.MatQUpdate.Step.stepFun_length (stN s) (stX s) ((oracleR s).2) _ h
  have hmin : min (stN s) (stN s * stN s) = stN s := Nat.min_eq_left (self_le_mul_self (stN s))
  have hsm : (scaleY s).length = stN s * stN s := by
    unfold scaleY
    rw [QMCLeafB.RoundSizeM6.smulRaw_length, List.length_take, ht, hmin]
  simp only [snapY, nrmRow_length]
  exact hsm

/-! ## 2.  The guarded round -/

/-- **The round with the normalisation guard**: on a normalised state it is `RoundProgram.round`, and
on any other state the state is frozen (`roundOk`), so the only growth is the appended flag. -/
noncomputable def roundG (s : RSt) : RSt :=
  if (stX s).length = stN s * stN s then QMCLeafB.RoundProgram.round s
  else QMCLeafB.RoundProgram.roundOk s

theorem roundG_of_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    roundG s = QMCLeafB.RoundProgram.round s := by
  unfold roundG
  rw [if_pos h]

theorem roundG_of_abnormal (s : RSt) (h : ¬ ((stX s).length = stN s * stN s)) :
    roundG s = QMCLeafB.RoundProgram.roundOk s := by
  unfold roundG
  rw [if_neg h]

theorem stN_roundOk (s : RSt) : stN (QMCLeafB.RoundProgram.roundOk s) = stN s := rfl

theorem stX_roundOk (s : RSt) : stX (QMCLeafB.RoundProgram.roundOk s) = stX s := rfl

theorem stN_roundG (s : RSt) : stN (roundG s) = stN s := by
  by_cases h : (stX s).length = stN s * stN s
  · rw [roundG_of_normalised s h, QMCLeafB.RStInit.stN_round]
  · rw [roundG_of_abnormal s h]
    rfl

/-- **The guard is preserved**: a normalised state's successor under `roundG` is normalised. -/
theorem roundG_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    (stX (roundG s)).length = stN (roundG s) * stN (roundG s) := by
  rw [roundG_of_normalised s h, QMCLeafB.RStInit.stN_round]
  rcases QMCLeafB.RoundProgram.round_eq s with hr
  by_cases hc : (oracleR s).1 = true
  · rw [QMCLeafB.RStInit.stX_round_of_cut s hc]
    exact snapY_length_eq s h
  · have hf : (oracleR s).1 = false := by simpa using hc
    rw [QMCLeafB.RStInit.stX_round_of_ok s hf]
    exact h

/-- **`roundG` is a `Poly` program.** -/
theorem poly_roundG : Automatic.Poly roundG := by
  have hlen : Automatic.Poly (fun s : RSt => (stX s).length) :=
    Automatic.Poly.comp (f := (List.length : List ℚ → ℕ)) (g := stX)
      (Automatic.Poly.list_length (α := ℚ)) QMCLeafB.RoundProgram.poly_stX
  have hnn : Automatic.Poly (fun s : RSt => stN s * stN s) :=
    Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
      (g := fun s : RSt => (stN s, stN s)) Automatic.Poly.nat_mul
      (Automatic.Poly.pair QMCLeafB.RoundProgram.poly_stN QMCLeafB.RoundProgram.poly_stN)
  have hp : Automatic.Poly (fun s : RSt => decide ((stX s).length = stN s * stN s)) :=
    Automatic.Poly.nat_eq_comp hlen hnn
  have h := Automatic.Poly.ite_prop
    (p := fun s : RSt => (stX s).length = stN s * stN s) hp
    QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_roundOk
  exact QMCLeafB.FinishLine.poly_of_pointwise h (fun s => rfl)

/-! ## 3.  The orbit from `init0` is normalised, and `roundG` agrees with `round` there -/

/-- **Every state of the run is normalised** — and, equivalently, the guard never fires on the run. -/
theorem iterate_normalised_and_eq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    ∀ j : ℕ,
      (stX (roundG^[j] (init0 p))).length = stN (roundG^[j] (init0 p)) * stN (roundG^[j] (init0 p))
      ∧ roundG^[j] (init0 p) = QMCLeafB.RoundProgram.round^[j] (init0 p) := by
  intro j
  induction j with
  | zero => exact ⟨init_normalised p, rfl⟩
  | succ k ih =>
      obtain ⟨hn, he⟩ := ih
      have hstep : roundG^[k + 1] (init0 p) = roundG (roundG^[k] (init0 p)) :=
        Function.iterate_succ_apply' _ k _
      have hround : QMCLeafB.RoundProgram.round^[k + 1] (init0 p)
          = QMCLeafB.RoundProgram.round (roundG^[k] (init0 p)) := by
        rw [Function.iterate_succ_apply', he]
      refine ⟨?_, ?_⟩
      · rw [hstep]
        exact roundG_normalised _ hn
      · rw [hstep, hround, roundG_of_normalised _ hn]

/-- **On the run, the guard never fires**: the guarded loop is the shelf's loop. -/
theorem roundG_iterate_eq_round (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (j : ℕ) :
    roundG^[j] (init0 p) = QMCLeafB.RoundProgram.round^[j] (init0 p) :=
  (iterate_normalised_and_eq p j).2

/-- **Every visited state is normalised.** -/
theorem stX_length_iterate_roundG (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) (j : ℕ) :
    (stX (roundG^[j] (init0 p))).length = stN (roundG^[j] (init0 p)) * stN (roundG^[j] (init0 p)) :=
  (iterate_normalised_and_eq p j).1

/-! ## 4.  The verdict read-out at the guarded loop -/

/-- The flag `roundG` appends. -/
noncomputable def okG (s : RSt) : Bool :=
  if (stX s).length = stN s * stN s then !((oracleR s).1) else true

theorem stOks_roundG (s : RSt) : stOks (roundG s) = stOks s ++ [okG s] := by
  by_cases h : (stX s).length = stN s * stN s
  · rw [roundG_of_normalised s h, QMCLeafB.RStInit.stOks_round]
    simp only [okG, if_pos h]
  · rw [roundG_of_abnormal s h]
    simp only [okG, if_neg h]
    rfl

theorem stOks_iterate_G (s : RSt) (T : ℕ) :
    stOks (roundG^[T] s) = stOks s ++ (List.range T).map (fun k => okG (roundG^[k] s)) := by
  induction T generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundG, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

/-- **`hverdict` at the guarded loop.** -/
theorem verdict_iterate_eq_anyOk_G (s : RSt) (hs : stOks s = []) (T : ℕ) :
    QMCLeafB.RoundProgram.verdict (roundG^[T] s)
      = SimLoop.anyOk (fun k => okG (roundG^[k] s)) T := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_iterate_G, hs, List.nil_append]
  exact QMCLeafB.RStInit.decide_pos_filter_map_range _ T

/-- **The guarded loop's bit is the shelf loop's bit** on the tape-free start (the guard is inert
along the run). -/
theorem loopBit_G_eq (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init0 roundG QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict T0 G t := by
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundG_iterate_eq_round]

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.GuardedRound.snapY_length_eq
#print axioms QMCLeafB.GuardedRound.poly_roundG
#print axioms QMCLeafB.GuardedRound.roundG_normalised
#print axioms QMCLeafB.GuardedRound.stX_length_iterate_roundG
#print axioms QMCLeafB.GuardedRound.roundG_iterate_eq_round
#print axioms QMCLeafB.GuardedRound.verdict_iterate_eq_anyOk_G
#print axioms QMCLeafB.GuardedRound.loopBit_G_eq

end QMCLeafB.GuardedRound


