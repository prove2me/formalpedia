-- Prove2me | Definitions.Def_QMCLeafB_verdbridge
-- name    : QMCLeafB_verdbridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:21:42.549249+00:00
-- url     : https://prove2.me/theorems/393417bc-f200-4d8f-873e-6128219bd8f5
-- title:
--   QMCLeafB verdbridge
-- statement:
--   # leaf B phase 21 — brick `verdict-bridges` (swarm `smw1m5nkm`, member m4, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
import Definitions.Def_QMCLeafB_hmemStateB
import Definitions.Def_QMCLeafB_numcert_m6
/-
# leaf B phase 21 — brick `verdict-bridges` (swarm `smw1m5nkm`, member m4, direction d2)

`RecordsM2.hverdict_of_halves` splits the verdict slot of `CoreData` into two per-round
implications at the run's queried centres `cXst … k`:

* `hon` — the programme's `ok` answer at round `k` forces the canonical flag to be `true`;
* `hoff` — a `true` canonical flag forces the programme's `ok` answer at round `k`.

This file settles where those two halves live, and where they are **false**.

## §1–§3  `hon` is refuted at the shelf's round

`RoundProgram.oracleR`'s `ok` branch (`stT s ≤ fvR s`, i.e. `tr(A·centre) ≥ t`) is the **upper**
event, while `FlagsM5.flagOf` asks for `RelaxMem` at the level `t − eps G`, whose trace slot is the
**lower** bound `frob ≤ (t − eps G) + dq/2`.  So at any state whose weight code is `wMatrixQ G` and
whose threshold is `t`:

* `(oracleR s).1 = false → stT s ≤ fvR s` (`oracleR_ok_le_fvR`);
* the pinched centre's objective is the state's (`frob_diagPinch`, `fvR_eq_frob`), hence
  `¬ RelaxMem (wMatrixQ G) (cXst …) (t − eps G) P.dq` **whenever `P.dq / 2 < eps G`**
  (`not_relaxMem_diagPinch_of_oracleR_ok`, `flagOf_false_of_oracleR_ok`).

At the campaign family (`paramsKbc2`, `dq = dqShallow`) the condition `dq/2 < eps` holds
(`paramsKbc2_dq_half_lt_eps`), so **an `ok` answer and a member answer are mutually exclusive at the
same round**: `hon` is not merely unproved at `RoundProgram.round`, it is refuted there, and so is
`hoff` (the `ok` branch's trace test is violated by every member).  This is the quantitative form of
m7's `okorient` remark (`Check_htop_oklower_m7`'s header) and it is the reason a per-round agreement
proof at the shelf's round cannot exist.

## §4–§5  both halves at the *lower-body* round `OkLower.oracleV`

`OkLower.oracleV`'s `ok` branch is `dvR s = 0 ∧ fvR s ≤ levelOf s ∧ ¬pivAns`, i.e. *exactly* the
three `RelaxMem` clauses, so there both halves are true modulo the pivot's exactness:

* `relaxMem_diagPinch_of_okV` — an `ok` answer of `oracleV` **is** a membership certificate at the
  pinched centre, given the *exact* descent's `false` at the state's own rows
  (`PivExact.psd_of_false` for exact PSD, `OkLower.oracleV_ok` for the diagonal and the trace);
  `flag_true_of_okV` is the flag form.  So `hon` **closes** at `roundV` (`hmem_slot`'s shape, at the
  centre family the record actually uses).
* `oracleV_ok_of_mem` — conversely a member centre at the run's levels makes the `ok` answer true,
  provided the state is unit-diagonal (`dvR = 0`) and the descent reports no cut.  So `hoff` at
  `roundV` reduces to those two state facts (the trace clause is *free*: membership implies it).

## §6  the slot forms

`hon_slot`/`hoff_slot` are the `K·m`-window forms that `RecordsM2.hverdict_of_halves` consumes, at an
arbitrary state sequence: they are what a production direction instantiates along the concrete
iterate, and `hverdict_of_state_plugs` composes them into the verdict equation itself.  Nothing here
changes a `FlagsM5`/`RecordsM2` shape.

## §7  explicit states

`hoff` is refuted **unconditionally** at the shelf's round by the state `sCut` (`G₀`'s weights,
`t = -1/2`, diagonal off by `dq/8`, off-diagonal `-3/4`): its pinched centre is a member
(`relaxMem_pinchedCut`, hence `flag_true_at_sCut`) while the round reports a *cut*
(`oracleR_sCut`) — no descent evaluation is needed, the diagonal-repair branch fires.  `hon`'s
refutation at the state `sId` is §3 instantiated (its own descent verdict is the one premise).

## Recommendation (for the assembly)

The residual `ResidFinite` of `Check_records_m2` is stated at
`loopBit InitDq.init0 RoundProgram.round RoundProgram.verdict Tbc2`.  §1–§3 show that the verdict
slot cannot be discharged there at the campaign tolerance: the run's `ok` bit is the *upper* event
and the flag stream is the *lower* body.  The program must be `OkLower.roundV` (interior) /
`roundW` (both regimes, `Check_htop_oklower_m7`), whose `ok` bit is the lower event; then §4–§5 give
the two halves.  This is independent of the phase-21 `hcutfin` question: `hverdict` is a verdict
equation, not a budget slot, and its shape is untouched by a horizon restate.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.VerdictBridge

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram

/-! ## 1.  The shelf's `ok` answer is the upper event -/

/-- **An `ok` answer of `RoundProgram.oracleR` forces the upper trace test** `stT s ≤ fvR s`. -/
theorem oracleR_ok_le_fvR {s : RSt} (hok : (oracleR s).1 = false) : stT s ≤ fvR s := by
  by_cases hd : dvR s = 0
  · unfold oracleR at hok
    rw [if_pos hd] at hok
    by_cases hl : stT s ≤ fvR s
    · exact hl
    · unfold threshB at hok
      rw [if_neg hl] at hok
      exact absurd hok (by simp)
  · unfold oracleR at hok
    rw [if_neg hd] at hok
    exact absurd hok (by simp)

#print axioms QMCLeafB.VerdictBridge.oracleR_ok_le_fvR

/-- **An `ok` answer forces `dvR = 0`** (`CentreAdm`'s form, quoted here for the record). -/
theorem oracleR_ok_dvR {s : RSt} (hok : (oracleR s).1 = false) : dvR s = 0 :=
  QMCLeafB.CentreAdm.oracleR_ok_dvR_zero hok

#print axioms QMCLeafB.VerdictBridge.oracleR_ok_dvR

/-! ## 2.  The pinched centre of such a state is *outside* the relaxation

The two ingredients: the objective does not see the diagonal overwrite (`frob_diagPinch`, the
weight matrix has zero diagonal) and the state's own objective is `fvR` (`StateDiag.fvR_eq_frob`). -/

/-- **An `ok` answer at the campaign tolerance puts the pinched centre outside the body.** -/
theorem not_relaxMem_diagPinch_of_oracleR_ok {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {s : RSt} {t u dq : ℚ}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (stA s) = A) (hAdiag : ∀ i, A i i = 0)
    (hT : stT s = t) (hok : (oracleR s).1 = false) (hu : dq / 2 < t - u) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A
        (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat n (stX s)) dq) u dq := by
  intro hM
  have htr := hM.trace_le
  rw [QMCLeafB.CentreAdm.frob_diagPinch hAdiag] at htr
  have hfv : fvR s = QMCLeafB.SepOracle.frob A (QMCLeafB.StateDiag.stMat n (stX s)) := by
    rw [QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX, hA]
  have hge := oracleR_ok_le_fvR hok
  rw [hT, hfv] at hge
  linarith

#print axioms QMCLeafB.VerdictBridge.not_relaxMem_diagPinch_of_oracleR_ok

/-- **The flag form**: at a state whose weight code is `wMatrixQ G` and whose threshold is `t`, an
`ok` answer raises the canonical flag to `false` — the opposite of `hon`. -/
theorem flagOf_false_of_oracleR_ok {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {X : ℕ → List ℚ} {s : RSt} {k : ℕ}
    (hN : stN s = G.n) (hlenA : G.n ≤ (stA s).length) (hlenX : G.n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (stA s) = QMCLeafB.Finalization.wMatrixQ G)
    (hX : X k = stX s) (hT : stT s = t) (hok : (oracleR s).1 = false)
    (hu : P.dq / 2 < QMCLeafB.RundataCert.eps G) :
    QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false := by
  refine QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P _ k ?_
  have hX' : QMCLeafB.StateDiag.stMat G.n (X k) = QMCLeafB.StateDiag.stMat G.n (stX s) := by
    rw [hX]
  show ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
    (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G.n (X k)) P.dq)
    (t - QMCLeafB.RundataCert.eps G) P.dq
  rw [hX']
  exact not_relaxMem_diagPinch_of_oracleR_ok hN hlenA hlenX hA
    (fun i => QMCLeafB.RecordsM2.wMatrixQ_diag G i) hT hok (by linarith [hu])

#print axioms QMCLeafB.VerdictBridge.flagOf_false_of_oracleR_ok

/-! ## 3.  The tolerance separation at the campaign family -/

/-- **At the campaign family the tolerance is far inside the slack**: `dq/2 < eps` whenever the edge
mass is positive.  (`dqShallow ≤ eps` is `NumCert.dqShallowCore_le_eps`.) -/
theorem paramsKbc2_dq_half_lt_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2 < QMCLeafB.RundataCert.eps G := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq,
    QMCLeafB.NumCert.dqShallow_eq_core G hRq.ne']
  have h1 := QMCLeafB.NumCert.dqShallowCore_le_eps G
  have h2 : (0 : ℚ) < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    positivity
  linarith

#print axioms QMCLeafB.VerdictBridge.paramsKbc2_dq_half_lt_eps

/-- **The shelf programme's `ok` bit and the residual's flag stream are disjoint at every interior
point of the bracket.**  This is the machine-checked reason `hon`/`hoff` cannot be proved
per-round at `RoundProgram.round`. -/
theorem flagOf_false_of_oracleR_ok_kbc2 {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {X : ℕ → List ℚ} {s : RSt} {k : ℕ}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hN : stN s = G.n) (hlenA : G.n ≤ (stA s).length) (hlenX : G.n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (stA s) = QMCLeafB.Finalization.wMatrixQ G)
    (hX : X k = stX s) (hT : stT s = t) (hok : (oracleR s).1 = false) :
    QMCLeafB.FlagsM5.flagOf G t (QMCLeafB.UnionShallow.paramsKbc2 G)
      (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq) k = false :=
  flagOf_false_of_oracleR_ok hN hlenA hlenX hA hX hT hok
    (paramsKbc2_dq_half_lt_eps G hRq)

#print axioms QMCLeafB.VerdictBridge.flagOf_false_of_oracleR_ok_kbc2

/-! ## 4.  `hon` at the lower-body round: an `ok` answer *is* a member certificate -/

/-- **`RelaxMem` at the pinched centre from an `ok` answer of `OkLower.oracleV`.**  The diagonal
clause and unit-diagonality are the state's (`dvR = 0`), the trace clause is the round's own level
test (`fvR ≤ levelOf`), and the PSD clause is exact PSD — the exact descent's `false` at the state's
own rows (`PivExact.psd_of_false`), which is what `relaxMem_diagPinch` needs (it spends `dq/4` of the
margin lowering the diagonal). -/
theorem relaxMem_diagPinch_of_okV {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {s : RSt}
    {acc : QMCLeafB.PivotProgram.Acc} {u dq : ℚ}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (stA s) = A) (hAdiag : ∀ i, A i i = 0)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat n (stX s) i j
      = QMCLeafB.StateDiag.stMat n (stX s) j i)
    (hok : (QMCLeafB.OkLower.oracleV s).1 = false)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (n, stX s), acc)).1 = false)
    (hdqpos : 0 < dq) (hdq4 : dq ≤ 4)
    (hT : stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq) :
    QMCLeafB.RelaxOracle.RelaxMem A
      (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat n (stX s)) dq) u dq := by
  obtain ⟨hdv, hlvl, -⟩ := QMCLeafB.OkLower.oracleV_ok s hok
  have hpsd : ∀ x : Fin n → ℚ,
      0 ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat n (stX s)) x := by
    have hp := QMCLeafB.PivExact.psd_of_false (acc := acc) (X := stX s) hlenX hsym hpiv
    intro x
    exact hp x
  have hunit : ∀ i, QMCLeafB.StateDiag.stMat n (stX s) i i = 1 := by
    have hsum : QMCLeafB.RoundProgram.diagSumV (n, stX s) = 0 := by
      rw [← hN]
      exact hdv
    exact fun i => QMCLeafB.StateDiag.stMat_diag_eq_one hlenX hsum i
  have htrace : QMCLeafB.SepOracle.frob A (QMCLeafB.StateDiag.stMat n (stX s)) ≤ u + dq / 2 := by
    have hfv : fvR s = QMCLeafB.SepOracle.frob A (QMCLeafB.StateDiag.stMat n (stX s)) := by
      rw [QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX, hA]
    have hl : QMCLeafB.OkLower.levelOf s
        = stT s - QMCLeafB.RoundT.epsOf s + QMCLeafB.OkLower.dqOf s / 2 := rfl
    rw [hfv, hl, hT, hdq] at hlvl
    linarith
  exact QMCLeafB.CentreAdm.relaxMem_diagPinch hdqpos hdq4 hAdiag hunit hpsd htrace

#print axioms QMCLeafB.VerdictBridge.relaxMem_diagPinch_of_okV

/-- **The flag form of `hon` at the lower-body round**: the canonical flag is `true` at an `ok`
answer of `oracleV`. -/
theorem flag_true_of_okV {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {X : ℕ → List ℚ} {s : RSt}
    {acc : QMCLeafB.PivotProgram.Acc} {k : ℕ}
    (hN : stN s = G.n) (hlenA : G.n ≤ (stA s).length) (hlenX : G.n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (stA s) = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat G.n (stX s) i j
      = QMCLeafB.StateDiag.stMat G.n (stX s) j i)
    (hX : X k = stX s) (hok : (QMCLeafB.OkLower.oracleV s).1 = false)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, stX s), acc)).1 = false)
    (hdqpos : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hT : stT s - QMCLeafB.RoundT.epsOf s = t - QMCLeafB.RundataCert.eps G)
    (hdq : QMCLeafB.OkLower.dqOf s = P.dq) :
    QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true := by
  refine QMCLeafB.RecordsM2.flagOf_eq_true_of_mem ?_
  have hX' : QMCLeafB.StateDiag.stMat G.n (X k) = QMCLeafB.StateDiag.stMat G.n (stX s) := by
    rw [hX]
  show QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
    (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G.n (X k)) P.dq)
    (t - QMCLeafB.RundataCert.eps G) P.dq
  rw [hX']
  exact relaxMem_diagPinch_of_okV hN hlenA hlenX hA
    (fun i => QMCLeafB.RecordsM2.wMatrixQ_diag G i) hsym hok hpiv hdqpos hdq4 hT hdq

#print axioms QMCLeafB.VerdictBridge.flag_true_of_okV

/-! ## 5.  `hoff` at the lower-body round, reduced to two state facts -/

/-- **A member pinched centre forces the round's trace test** — the trace clause of `hoff` is free
at the lower-body round (`frob` is blind to the pinch, and the level test is exactly `trace_le`). -/
theorem fvR_le_levelOf_of_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {s : RSt} {u dq : ℚ}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (stA s) = A) (hAdiag : ∀ i, A i i = 0)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A
      (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat n (stX s)) dq) u dq)
    (hT : stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq) :
    fvR s ≤ QMCLeafB.OkLower.levelOf s := by
  have htr := hM.trace_le
  rw [QMCLeafB.CentreAdm.frob_diagPinch hAdiag] at htr
  have hfv : fvR s = QMCLeafB.SepOracle.frob A (QMCLeafB.StateDiag.stMat n (stX s)) := by
    rw [QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX, hA]
  have hl : QMCLeafB.OkLower.levelOf s
      = stT s - QMCLeafB.RoundT.epsOf s + QMCLeafB.OkLower.dqOf s / 2 := rfl
  rw [hfv, hl, hT, hdq]
  linarith

#print axioms QMCLeafB.VerdictBridge.fvR_le_levelOf_of_mem

/-- **`pivCut` is `ok` exactly when the descent finds no cut.** -/
theorem pivCut_fst_of_pivAns (s : RSt) (h : (pivAns s).1 = false) : (pivCut s).1 = false := by
  simp [pivCut, pivCutF, h]

#print axioms QMCLeafB.VerdictBridge.pivCut_fst_of_pivAns

/-- **`hoff` at the lower-body round.**  A member pinched centre makes the `ok` answer true as soon
as the state is unit-diagonal (`dvR = 0`, the diagonal clause the pinch hides) and the descent reports
no cut. -/
theorem oracleV_ok_of_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {s : RSt} {u dq : ℚ}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (stA s) = A) (hAdiag : ∀ i, A i i = 0)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A
      (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat n (stX s)) dq) u dq)
    (hT : stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq)
    (hdv : dvR s = 0) (hpiv : (pivCut s).1 = false) :
    (QMCLeafB.OkLower.oracleV s).1 = false := by
  have hlvl := fvR_le_levelOf_of_mem hN hlenA hlenX hA hAdiag hM hT hdq
  have hth : (QMCLeafB.OkLower.threshV s).1 = false := by
    unfold QMCLeafB.OkLower.threshV
    rw [if_pos hlvl]
    exact hpiv
  unfold QMCLeafB.OkLower.oracleV
  rw [if_pos hdv]
  exact hth

#print axioms QMCLeafB.VerdictBridge.oracleV_ok_of_mem

/-- The same with the descent's answer instead of the cut record. -/
theorem oracleV_ok_of_mem_pivAns {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {s : RSt} {u dq : ℚ}
    (hN : stN s = n) (hlenA : n ≤ (stA s).length) (hlenX : n ≤ (stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (stA s) = A) (hAdiag : ∀ i, A i i = 0)
    (hM : QMCLeafB.RelaxOracle.RelaxMem A
      (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat n (stX s)) dq) u dq)
    (hT : stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq)
    (hdv : dvR s = 0) (hpiv : (pivAns s).1 = false) :
    (QMCLeafB.OkLower.oracleV s).1 = false :=
  oracleV_ok_of_mem hN hlenA hlenX hA hAdiag hM hT hdq hdv (pivCut_fst_of_pivAns s hpiv)

#print axioms QMCLeafB.VerdictBridge.oracleV_ok_of_mem_pivAns

/-! ## 6.  The two halves as `K·m`-window slots

These are the shapes `RecordsM2.hverdict_of_halves` consumes (`hon`/`hoff` over `k < P.K * P.m`), at
an arbitrary state sequence and at the lower-body round.  `hX` identifies the residual's centre family
with the run's states, as `hmem_slot` does. -/

/-- **`hon` over the run's window at `oracleV`.** -/
theorem hon_slot {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (rb : ℕ → Bool) (X : ℕ → List ℚ) (s : ℕ → RSt) (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hX : ∀ k, X k = stX (s k))
    (hN : ∀ k, stN (s k) = G.n)
    (hlenA : ∀ k, G.n ≤ (stA (s k)).length)
    (hlenX : ∀ k, G.n ≤ (stX (s k)).length)
    (hA : ∀ k, QMCLeafB.StateDiag.stMat G.n (stA (s k)) = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (s k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (s k)) j i)
    (hbit : ∀ k, rb k = true → (QMCLeafB.OkLower.oracleV (s k)).1 = false)
    (hpiv : ∀ k, rb k = true → (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, stX (s k)), acc k)).1 = false)
    (hdqpos : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hT : ∀ k, stT (s k) - QMCLeafB.RoundT.epsOf (s k)
      = t - QMCLeafB.RundataCert.eps G)
    (hdq : ∀ k, QMCLeafB.OkLower.dqOf (s k) = P.dq) :
    ∀ k, k < P.K * P.m → rb k = true →
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true := by
  intro k _ hb
  exact flag_true_of_okV (hN k) (hlenA k) (hlenX k) (hA k) (hsym k) (hX k) (hbit k hb)
    (hpiv k hb) hdqpos hdq4 (hT k) (hdq k)

#print axioms QMCLeafB.VerdictBridge.hon_slot

/-- **`hoff` over the run's window at `oracleV`**, reduced to the two per-round state facts
`dvR = 0` and "the descent finds no cut" at member rounds. -/
theorem hoff_slot {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (rb : ℕ → Bool) (X : ℕ → List ℚ) (s : ℕ → RSt)
    (hX : ∀ k, X k = stX (s k))
    (hN : ∀ k, stN (s k) = G.n)
    (hlenA : ∀ k, G.n ≤ (stA (s k)).length)
    (hlenX : ∀ k, G.n ≤ (stX (s k)).length)
    (hA : ∀ k, QMCLeafB.StateDiag.stMat G.n (stA (s k)) = QMCLeafB.Finalization.wMatrixQ G)
    (hbit : ∀ k, rb k = true ↔ (QMCLeafB.OkLower.oracleV (s k)).1 = false)
    (hdv : ∀ k,
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        dvR (s k) = 0)
    (hpiv : ∀ k,
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        (pivCut (s k)).1 = false)
    (hT : ∀ k, stT (s k) - QMCLeafB.RoundT.epsOf (s k)
      = t - QMCLeafB.RundataCert.eps G)
    (hdq : ∀ k, QMCLeafB.OkLower.dqOf (s k) = P.dq) :
    ∀ k, k < P.K * P.m →
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        rb k = true := by
  intro k _ hf
  have hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G.n (stX (s k))) P.dq)
      (t - QMCLeafB.RundataCert.eps G) P.dq := by
    have h1 := QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P
      (QMCLeafB.RecordsM2.cXst G.n X P.dq) k hf
    have hX' : QMCLeafB.StateDiag.stMat G.n (X k)
        = QMCLeafB.StateDiag.stMat G.n (stX (s k)) := by rw [hX k]
    simpa [QMCLeafB.RecordsM2.cXst, hX'] using h1
  have hok := oracleV_ok_of_mem (hN k) (hlenA k) (hlenX k) (hA k)
    (fun i => QMCLeafB.RecordsM2.wMatrixQ_diag G i) hM (hT k) (hdq k) (hdv k hf) (hpiv k hf)
  exact (hbit k).mpr hok

#print axioms QMCLeafB.VerdictBridge.hoff_slot


/-! ## 7.  Explicit states: the two halves are refuted, not merely unproved

`hon` is refuted at `ParamsKbc2`-tolerance by §3; §7 exhibits the concrete state at `G₀`'s own weight
code and `t = -1/2` (the campaign's banked anchor point) at which the programme (conditionally on its
own descent verdict, §7.1) reports `ok` while the canonical flag is `false`.

`hoff` is refuted **unconditionally** here: the state `sCut` below is off the unit diagonal by
`dq/8` per entry, so the diagonal-repair branch fires and the round reports a *cut* (`oracleR_sCut`),
while its pinched centre `!![1 - dq/4, -3/4; -3/4, 1 - dq/4]` *is* a member at `(t - ε, dq)`
(`relaxMem_pinch_sCut`).  So a `true` canonical flag coexists with a `cut` answer: no per-round
`flag → ok` implication holds at the shelf's round.
-/

/-- The campaign tolerance at `G₀`, as a name. -/
noncomputable def dqK : ℚ := (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq

theorem dqK_def : dqK = (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq := rfl

theorem dqK_pos : 0 < dqK := dqK_def ▸ (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).hdq

theorem dqK_le_four : dqK ≤ 4 := by
  have h1 : dqK ≤ 1 := dqK_def ▸ QMCLeafB.NumCert.dqShallow_le_one QMCLeafB.ResidRefute.G₀
  linarith

theorem eps_G₀_eq : QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀ = 1 / 40000 :=
  QMCLeafB.FlagsM5.eps_G₀

/-- `G₀`'s weight matrix `!![0, 1/2; 1/2, 0]`, entrywise. -/
theorem wMatrixQ_G₀_zero_zero :
    QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (0 : Fin QMCLeafB.ResidRefute.G₀.n) (0 : Fin QMCLeafB.ResidRefute.G₀.n) = 0 :=
  QMCLeafB.Finalization.wMatrixQ_apply_of_eq

theorem wMatrixQ_G₀_one_one :
    QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (1 : Fin QMCLeafB.ResidRefute.G₀.n) (1 : Fin QMCLeafB.ResidRefute.G₀.n) = 0 :=
  QMCLeafB.Finalization.wMatrixQ_apply_of_eq

theorem wMatrixQ_G₀_zero_one :
    QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (0 : Fin QMCLeafB.ResidRefute.G₀.n) (1 : Fin QMCLeafB.ResidRefute.G₀.n) = 1 / 2 := by
  rw [QMCLeafB.Finalization.wMatrixQ_apply_of_lt (by decide)]
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrixQ_G₀_one_zero :
    QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (1 : Fin QMCLeafB.ResidRefute.G₀.n) (0 : Fin QMCLeafB.ResidRefute.G₀.n) = 1 / 2 := by
  rw [QMCLeafB.Finalization.wMatrixQ_apply_of_gt (by decide)]
  norm_num [QMCLeafB.ResidRefute.G₀]

/-- **The state's weight code is `G₀`'s weight matrix.** -/
theorem stMat_wCode :
    QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n [0, 1 / 2, 1 / 2, 0]
      = QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [QMCLeafB.StateDiag.stMat_apply, List.getD_cons_zero, List.getD_cons_succ,
      Nat.zero_mul, Nat.zero_add, Nat.add_zero]
    first
      | exact (wMatrixQ_G₀_zero_zero).symm
      | exact (wMatrixQ_G₀_one_one).symm
      | exact (wMatrixQ_G₀_zero_one).symm
      | exact (wMatrixQ_G₀_one_zero).symm

/-- The `ok`-side state: `G₀`'s weights, the unit-diagonal identity block, `t = -1/2`. -/
noncomputable def sId : RSt :=
  mkSt QMCLeafB.ResidRefute.G₀.n [0, 1 / 2, 1 / 2, 0] [1, 0, 0, 1] (-(1 / 2)) 2 1 [] []

/-! ### 7.1  the `ok`-side state (conditionally on the descent's own verdict) -/

/-- **`hon` is refuted at an explicit state**: at the identity block the programme's `ok` answer
(its descent verdict is the only premise) coexists with a `false` canonical flag at the campaign
tolerance.  The state's descent answer is `false` on evaluation (`runPivL` on `[[1,0],[0,1]]`); the
kernel does not reduce the snapped descent, so it stays a hypothesis. -/
theorem flag_false_at_sId (hok : (oracleR sId).1 = false) :
    QMCLeafB.FlagsM5.flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.RecordsM2.cXst QMCLeafB.ResidRefute.G₀.n (fun _ => [1, 0, 0, 1])
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq) 0 = false := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num
  have hN : stN sId = QMCLeafB.ResidRefute.G₀.n := rfl
  have hlenA : QMCLeafB.ResidRefute.G₀.n ≤ (stA sId).length := by
    simp [sId, QMCLeafB.ResidRefute.G₀]
  have hlenX : QMCLeafB.ResidRefute.G₀.n ≤ (stX sId).length := by
    simp [sId, QMCLeafB.ResidRefute.G₀]
  have hT : stT sId = -(1 / 2) := rfl
  exact flagOf_false_of_oracleR_ok_kbc2 hRq hN hlenA hlenX stMat_wCode rfl hT hok

#print axioms QMCLeafB.VerdictBridge.flag_false_at_sId

/-! ### 7.2  the `cut`-side state: `hoff` is refuted unconditionally -/

/-- The `cut`-side state: the diagonal is off by `dq/8` per entry, the off-diagonal is `-3/4`. -/
noncomputable def sCut : RSt :=
  mkSt QMCLeafB.ResidRefute.G₀.n [0, 1 / 2, 1 / 2, 0]
    [1 + dqK / 8, -(3 / 4), -(3 / 4), 1 - dqK / 8] (-(1 / 2)) 2 1 [] []

/-- The diagonal read-out of a `2 × 2` code with four entries. -/
theorem diagSumV_four' (a b c d : ℚ) :
    QMCLeafB.RoundProgram.diagSumV (2, [a, b, c, d])
      = QMCLeafB.RoundProgram.absq (a - 1) + QMCLeafB.RoundProgram.absq (d - 1) := by
  simp [QMCLeafB.RoundProgram.diagSumV, QMCLeafB.RoundProgram.idxs, QMCLeafB.RoundProgram.entV,
    List.range_succ]

#print axioms QMCLeafB.VerdictBridge.diagSumV_four'

/-- **The diagonal repair branch fires**: `dvR` at `sCut` is `dq/4 > 0`. -/
theorem dvR_sCut : dvR sCut = dqK / 4 := by
  have hX : stX sCut = [1 + dqK / 8, -(3 / 4), -(3 / 4), 1 - dqK / 8] := rfl
  have hN : stN sCut = 2 := rfl
  rw [dvR, hN, hX, diagSumV_four',
    show (1 + dqK / 8 - 1 : ℚ) = dqK / 8 by ring,
    show (1 - dqK / 8 - 1 : ℚ) = -(dqK / 8) by ring,
    QMCLeafB.RoundProgram.absq_eq, QMCLeafB.RoundProgram.absq_eq,
    abs_of_pos (by linarith [dqK_pos] : (0 : ℚ) < dqK / 8), abs_neg,
    abs_of_pos (by linarith [dqK_pos] : (0 : ℚ) < dqK / 8)]
  ring

#print axioms QMCLeafB.VerdictBridge.dvR_sCut

/-- **The programme answers `cut` at `sCut`** — no descent evaluation needed. -/
theorem oracleR_sCut : (oracleR sCut).1 = true := by
  have h : dvR sCut ≠ 0 := by
    rw [dvR_sCut]
    have := dqK_pos
    intro h0
    linarith [div_eq_zero_iff.mp h0]
  unfold oracleR
  rw [if_neg h]

#print axioms QMCLeafB.VerdictBridge.oracleR_sCut

/-- The pinched centre of `sCut`. -/
noncomputable def pinchedCut : Matrix (Fin QMCLeafB.ResidRefute.G₀.n)
    (Fin QMCLeafB.ResidRefute.G₀.n) ℚ :=
  QMCLeafB.CentreAdm.diagPinch
    (QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n (stX sCut)) dqK

theorem pinchedCut_00 : pinchedCut 0 0 = 1 - dqK / 4 :=
  QMCLeafB.CentreAdm.diagPinch_diag _ _ _

theorem pinchedCut_11 : pinchedCut 1 1 = 1 - dqK / 4 :=
  QMCLeafB.CentreAdm.diagPinch_diag _ _ _

theorem pinchedCut_01 : pinchedCut 0 1 = -(3 / 4) := by
  have hne : (0 : Fin QMCLeafB.ResidRefute.G₀.n) ≠ 1 := by decide
  rw [pinchedCut, QMCLeafB.CentreAdm.diagPinch_off hne]
  simp [QMCLeafB.StateDiag.stMat_apply, sCut]

theorem pinchedCut_10 : pinchedCut 1 0 = -(3 / 4) := by
  have hne : (1 : Fin QMCLeafB.ResidRefute.G₀.n) ≠ 0 := by decide
  rw [pinchedCut, QMCLeafB.CentreAdm.diagPinch_off hne]
  simp [QMCLeafB.StateDiag.stMat_apply, sCut]

/-- **`hoff` is refuted: the pinched centre of `sCut` is a member.**  The state's off-diagonal part
is `-3/4`, so the pinched matrix is `!![1 - dq/4, -3/4; -3/4, 1 - dq/4]`, whose quadratic form is
bounded below by `(1/4 - dq/4)·‖x‖² ≥ -(dq/2)·‖x‖²` and whose objective is `-3/4 ≤ t - ε + dq/2`. -/
theorem relaxMem_pinchedCut :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
      pinchedCut (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀) dqK := by
  have hdq := dqK_pos
  have hdq4 := dqK_le_four
  refine ⟨hdq, ?_, ?_, ?_⟩
  · intro x
    have hq : QMCLeafB.SepOracle.qf pinchedCut x
        = (1 - dqK / 4) * (x 0 ^ 2 + x 1 ^ 2) + 2 * (-(3 / 4)) * (x 0 * x 1) := by
      rw [QMCLeafB.SepOracle.qf_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [pinchedCut_00, pinchedCut_11, pinchedCut_01, pinchedCut_10]
      ring
    have h1 : 2 * (x 0 * x 1) ≤ x 0 ^ 2 + x 1 ^ 2 := by
      have := sq_nonneg (x 0 - x 1)
      linarith
    have h2 : (0 : ℚ) ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    have hsum2 : (∑ i, x i ^ 2 : ℚ) = x 0 ^ 2 + x 1 ^ 2 := by
      rw [Fin.sum_univ_two]
    rw [hq, hsum2]
    nlinarith [h1, h2, hdq]
  · intro i
    exact QMCLeafB.CentreAdm.abs_diagPinch _ hdq hdq4 i
  · have h00 : QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n (stX sCut) 0 0
        = 1 + dqK / 8 := by
      simp [QMCLeafB.StateDiag.stMat_apply, sCut]
    have h01 : QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n (stX sCut) 0 1 = -(3 / 4) := by
      simp [QMCLeafB.StateDiag.stMat_apply, sCut]
    have h10 : QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n (stX sCut) 1 0 = -(3 / 4) := by
      simp [QMCLeafB.StateDiag.stMat_apply, sCut]
    have h11 : QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n (stX sCut) 1 1
        = 1 - dqK / 8 := by
      simp [QMCLeafB.StateDiag.stMat_apply, sCut]
    have hfrob : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
        (QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n (stX sCut)) = -(3 / 4) := by
      rw [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [h00, h01, h10, h11, wMatrixQ_G₀_zero_zero, wMatrixQ_G₀_zero_one,
        wMatrixQ_G₀_one_one, wMatrixQ_G₀_one_zero]
      norm_num
    rw [pinchedCut, QMCLeafB.CentreAdm.frob_diagPinch
      (fun i => QMCLeafB.RecordsM2.wMatrixQ_diag QMCLeafB.ResidRefute.G₀ i), hfrob, eps_G₀_eq]
    linarith [dqK_le_four]

#print axioms QMCLeafB.VerdictBridge.relaxMem_pinchedCut

/-- **The canonical flag at `sCut` is `true`** — while the programme's answer there is `cut`. -/
theorem flag_true_at_sCut :
    QMCLeafB.FlagsM5.flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.RecordsM2.cXst QMCLeafB.ResidRefute.G₀.n (fun _ => stX sCut)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq) 0 = true := by
  refine QMCLeafB.RecordsM2.flagOf_eq_true_of_mem ?_
  exact relaxMem_pinchedCut

#print axioms QMCLeafB.VerdictBridge.flag_true_at_sCut

/-! ## 8.  The verdict equation at the lower-body round, from the state plugs -/

/-- **`hverdict` at `oracleV`'s round from explicit per-round state data.**  `hrb` says the run's own
`ok` bit is `oracleV`'s answer; `hon_slot`/`hoff_slot` then give the two halves and
`RecordsM2.hverdict_of_halves` gives the equation.  This is the shape a production direction
instantiates along the concrete iterate — the verdict slot, with no pointwise agreement at
`RoundProgram.oracleR` anywhere. -/
theorem hverdict_of_state_plugs {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (rb : ℕ → Bool) (X : ℕ → List ℚ) (s : ℕ → RSt) (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hX : ∀ k, X k = stX (s k))
    (hN : ∀ k, stN (s k) = G.n)
    (hlenA : ∀ k, G.n ≤ (stA (s k)).length)
    (hlenX : ∀ k, G.n ≤ (stX (s k)).length)
    (hA : ∀ k, QMCLeafB.StateDiag.stMat G.n (stA (s k)) = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (s k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (s k)) j i)
    (hrb : ∀ k, rb k = true ↔ (QMCLeafB.OkLower.oracleV (s k)).1 = false)
    (hpiv : ∀ k, rb k = true → (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, stX (s k)), acc k)).1 = false)
    (hdv : ∀ k,
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        dvR (s k) = 0)
    (hpivf : ∀ k,
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        (pivCut (s k)).1 = false)
    (hdqpos : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hT : ∀ k, stT (s k) - QMCLeafB.RoundT.epsOf (s k)
      = t - QMCLeafB.RundataCert.eps G)
    (hdq : ∀ k, QMCLeafB.OkLower.dqOf (s k) = P.dq) :
    o G t = QMCLeafB.SimLoop.anyOk
      (QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq)) (P.K * P.m) :=
  QMCLeafB.RecordsM2.hverdict_of_halves hbit
    (hon_slot rb X s acc hX hN hlenA hlenX hA hsym
      (fun k hk => (hrb k).mp hk) hpiv hdqpos hdq4 hT hdq)
    (hoff_slot rb X s hX hN hlenA hlenX hA hrb hdv hpivf hT hdq)

#print axioms QMCLeafB.VerdictBridge.hverdict_of_state_plugs


/-! ## 9.  `hverdict` at the *reported* round `roundW`, on the interior

§8 is the verdict equation from the state plugs; the remaining step at the level of the actual
programme is that the loop's own bit stream be `oracleV`'s.  At `roundW` this is `OkLower`'s read-out
(`verdict_iterate_eq_anyOk_W`) plus `okW_eq_engine` (below the campaign slack the appended flag is
`!oracleV`), so the verdict equation follows with `hon_slot`/`hoff_slot`.  The per-round state
read-outs (`stN`, lengths, the weight code, symmetry) and the three behavioural plugs (the exact
descent's `false` at `ok` rounds; `dvR = 0` and no descent cut at member rounds) are hypotheses —
they are what the production bricks at the run supply. -/

/-- **The `(G, t)`-run of the reported round.** -/
noncomputable def runW (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) : ℕ → RSt :=
  fun k => QMCLeafB.OkLower.roundW^[k] (init (QMCLeafB.FinalStroke.noTape G t))

/-- **`hverdict` at the reported round, on the interior bracket.**  This is the verdict slot of
`CoreDataF`/`StreamCore` at the programme the ok-branch bricks actually live on; at
`RoundProgram.round` the same slot is refuted (§1–§3, §7.2). -/
theorem hverdict_at_roundW
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hint : ¬ (0 ≤ stT (init (QMCLeafB.FinalStroke.noTape G t))
      + QMCLeafB.RoundT.epsOf (init (QMCLeafB.FinalStroke.noTape G t))))
    (hoks : stOks (init (QMCLeafB.FinalStroke.noTape G t)) = [])
    (hKm : T0 G t = P.K * P.m)
    (X : ℕ → List ℚ) (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hX : ∀ k, X k = stX (runW init T0 G t k))
    (hN : ∀ k, stN (runW init T0 G t k) = G.n)
    (hlenA : ∀ k, G.n ≤ (stA (runW init T0 G t k)).length)
    (hlenX : ∀ k, G.n ≤ (stX (runW init T0 G t k)).length)
    (hA : ∀ k, QMCLeafB.StateDiag.stMat G.n (stA (runW init T0 G t k))
      = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.StateDiag.stMat G.n (stX (runW init T0 G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (stX (runW init T0 G t k)) j i)
    (hpiv : ∀ k, QMCLeafB.OkLower.okW (runW init T0 G t k) = true →
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, stX (runW init T0 G t k)), acc k)).1 = false)
    (hdv : ∀ k,
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        dvR (runW init T0 G t k) = 0)
    (hpivf : ∀ k,
      QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = true →
        (pivCut (runW init T0 G t k)).1 = false)
    (hdqpos : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hT : ∀ k, stT (runW init T0 G t k) - QMCLeafB.RoundT.epsOf (runW init T0 G t k)
      = t - QMCLeafB.RundataCert.eps G)
    (hdq : ∀ k, QMCLeafB.OkLower.dqOf (runW init T0 G t k) = P.dq) :
    QMCLeafB.FinalStroke.loopBit init QMCLeafB.OkLower.roundW
        QMCLeafB.RoundProgram.verdict T0 G t
      = QMCLeafB.SimLoop.anyOk
        (QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq)) (P.K * P.m) := by
  haveI : Nonempty (ℕ → RSt) := ⟨fun _ => init (QMCLeafB.FinalStroke.noTape G t)⟩
  refine hverdict_of_state_plugs
    (o := QMCLeafB.FinalStroke.loopBit init QMCLeafB.OkLower.roundW
      QMCLeafB.RoundProgram.verdict T0)
    (rb := fun k => QMCLeafB.OkLower.okW (runW init T0 G t k)) X
    (runW init T0 G t) acc ?_ hX hN hlenA hlenX hA hsym ?_ hpiv hdv hpivf hdqpos hdq4 hT hdq
  · rw [QMCLeafB.FinalStroke.loopBit_apply, hKm,
      QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W _ hoks]
    rfl
  · intro k
    have he := QMCLeafB.OkLower.okW_eq_engine (init (QMCLeafB.FinalStroke.noTape G t)) k hint
    have h1 : QMCLeafB.OkLower.okW (runW init T0 G t k)
        = !((QMCLeafB.OkLower.oracleV (runW init T0 G t k)).1) := he
    rw [h1]
    cases (QMCLeafB.OkLower.oracleV (runW init T0 G t k)).1 <;> simp

#print axioms QMCLeafB.VerdictBridge.hverdict_at_roundW


end QMCLeafB.VerdictBridge


