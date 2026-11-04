-- Prove2me | Definitions.Def_QMCLeafB_htop_okorient_m7
-- name    : QMCLeafB_htop_okorient_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:08:40.530856+00:00
-- url     : https://prove2.me/theorems/f682efa0-6035-4ed1-affc-9db8de257d8a
-- title:
--   QMCLeafB htop_okorient_m7
-- statement:
--   # leaf B phase 16 — the `ok` orientation of the round program vs `RelaxMem` (m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_finish_m7
import Definitions.Def_QMCLeafB_runparams_shallow_m5
/-
# leaf B phase 16 — the `ok` orientation of the round program vs `RelaxMem` (m7)

Two machine-checked facts about the *interfaces* (no orbit reasoning, so they are decisive):

1. `ok_thresh_le`: at an `ok` answer of the program's `RoundProgram.oracleR`, the state's value is
   at or **above** the threshold: `stT s ≤ fvR s = [A, X]`.  (`oracleR = threshB` on a unit-diagonal
   state, and `threshB` only asks the PSD test when `stT s ≤ fvR s`; the trace-cut branch answers
   `true`.)

2. `not_relaxMem_of_lower`: `RelaxOracle.RelaxMem A cX u δ` carries the **upper** trace bound
   `frob A cX ≤ u + δ/2`.

Consequently, at every `ok` round of the program's run,

    ¬ RelaxMem A cX (stT s − εw) δ        whenever  δ/2 < εw,

because `RelaxMem` would give `frob A cX ≤ stT s − εw + δ/2 < stT s ≤ frob A cX`.  In the campaign's
own numbers `εw = Rq G/40000` and `δ = dqShallowCore G = εw/(9·Rq G+1)`, so `δ/2 < εw` holds at every
`Rq G > 0` (`dqShallowCore_half_lt_eps` below).

That is the exact form brick 4's `hmem` asks for (`RelaxMem … (t − ε) P.dq` at `ok k = true`), so the
"program's `ok` bit agrees with the relax-oracle's `RelaxMem`" route is **closed**: the program's `ok`
is the *upper* event (`SepOracle.OkReport`'s orientation, `t − δ/2 ≤ frob`), while `RelaxMem` is the
*lower* body.  Brick 4 must either (i) run a round whose `ok` test is the lower-body one
(`fvR ≤ stT − ε + dq/2`), with `htop` then supplied on the top slice by the `roundU`/`roundGU`
regime split (the two regimes are separated by `0 ≤ stT + εw`, a run invariant), or (ii) certify
`hcert` from the *upper* ledger plus the extra fact `fvR ≤ stT + εw` — a point whose value is in the
window `[t, t + εw]`.

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace QMCLeafB.OkOrient

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram

/-- **At an `ok` answer of the program's oracle the state is at or above the threshold.** -/
theorem ok_thresh_le (s : RSt) (hok : (oracleR s).1 = false) : stT s ≤ fvR s := by
  unfold oracleR at hok
  by_cases hd : dvR s = 0
  · rw [if_pos hd] at hok
    unfold threshB at hok
    by_cases ht : stT s ≤ fvR s
    · exact ht
    · rw [if_neg ht] at hok
      exact absurd hok (by simp)
  · rw [if_neg hd] at hok
    exact absurd hok (by simp)

/-- **`RelaxMem`'s trace clause is an upper bound**, so it cannot hold above the threshold. -/
theorem not_relaxMem_of_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {cX : Matrix (Fin n) (Fin n) ℚ} {t u δ : ℚ}
    (ht : t ≤ QMCLeafB.SepOracle.frob A cX) (hu : u + δ / 2 < t) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A cX u δ := by
  intro h
  have := h.trace_le
  linarith

/-- **The obstruction, in the state's own terms.**  If the state's value is the matrix's Frobenius
pairing, then at an `ok` answer no `RelaxMem` at the shifted level `stT s − εw` can hold, for any
tolerance `δ` with `δ/2 < εw`. -/
theorem not_relaxMem_at_ok {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {s : RSt}
    (hF : fvR s = QMCLeafB.SepOracle.frob A cX) (hok : (oracleR s).1 = false)
    {δ : ℚ} (hδ : δ / 2 < QMCLeafB.RoundT.epsOf s) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A cX
        (stT s - QMCLeafB.RoundT.epsOf s) δ := by
  refine not_relaxMem_of_lower (t := stT s) (u := stT s - QMCLeafB.RoundT.epsOf s) ?_ ?_
  · rw [← hF]
    exact ok_thresh_le s hok
  · linarith

/-- **The campaign's own tolerance satisfies the hypothesis at every `Rq G > 0`.** -/
theorem dqShallowCore_half_lt_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallowCore G / 2 < QMCLeafB.RundataCert.eps G := by
  have he : 0 < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    linarith
  have hden : (0 : ℚ) < 2 * (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by linarith
  rw [show QMCLeafB.RundataParams.dqShallowCore G / 2
      = QMCLeafB.RundataCert.eps G / (2 * (9 * QMCLeafB.EngineRuntime.Rq G + 1)) from by
    unfold QMCLeafB.RundataParams.dqShallowCore
    field_simp]
  rw [div_lt_iff₀ hden]
  nlinarith

#print axioms QMCLeafB.OkOrient.ok_thresh_le
#print axioms QMCLeafB.OkOrient.not_relaxMem_of_lower
#print axioms QMCLeafB.OkOrient.not_relaxMem_at_ok
#print axioms QMCLeafB.OkOrient.dqShallowCore_half_lt_eps


