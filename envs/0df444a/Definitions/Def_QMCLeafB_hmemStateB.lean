-- Prove2me | Definitions.Def_QMCLeafB_hmemStateB
-- name    : QMCLeafB_hmemStateB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:19:05.917209+00:00
-- url     : https://prove2.me/theorems/79bd6440-0a9e-472b-a233-81a409f5e6af
-- title:
--   QMCLeafB hmemStateB
-- statement:
--   # leaf B phase 19 — brick `hmem-at-state` (swarm `smw1k12jb`, member m8, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_stateDiag
import Definitions.Def_QMCLeafB_pivexact
import Definitions.Def_QMCLeafB_bundleFull
/-
# leaf B phase 19 — brick `hmem-at-state` (swarm `smw1k12jb`, member m8, direction d9)

`Check_residkill_m8` shows the phase-18 residual `Resid` (all-`false` flag stream) is
unsatisfiable, and re-aims the closing stroke at `BundleFull`, i.e. `Bundle` **plus** the `ok`-round
`RelaxMem` slot

    hmem : ∀ k, k < P.K * P.m → ok k = true →
      RelaxMem (wMatrixQ G) (cX k) (t - eps G) P.dq.

This file is the positive half of that repair: it produces `hmem` from the state, with no grid-error
or snapping hypothesis, by chaining

* `StateDiag.relaxMem_of_oracleV_ok_state` (`Check_stateDiag_m2`) — `RelaxMem` at the state from the
  `ok` answer, with `diag_near` and unit-diagonality free on the `dvR = 0` branch;
* `PivExact.psd_margin_of_false` (`Check_pivexact_m8`) — the remaining PSD clause, from the **exact**
  descent's `false` verdict at the state's own rows;
* `StateDiag.fvR_eq_frob` — the objective bridge, from the state's weight code being `wMatrixQ G`.

§2 is the single-state form; §3 is the slot form, which is *literally* the `hmem` field of
`BundleFull` (the caller identifies `cX k` with the round's state block).  So the price of the
repair is exactly: (i) the state invariants (`stN`, `stA`, `stX` lengths, the weight code, symmetry),
and (ii) the exact pivot verdict `false` at each `ok` round — which is what the `runPivL` spelling
cannot supply (`Check_pivsnap_m1`) and `runPiv` can (`Check_pivexact_m8`).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.HmemState

open QuantumMaxCutEnergy

/-! ## 1.  The two spellings of the state's block agree -/

/-- `PivExact.matOf` is `StateDiag.stMat`. -/
theorem matOf_eq_stMat (n : ℕ) (X : List ℚ) :
    QMCLeafB.PivExact.matOf n X = QMCLeafB.StateDiag.stMat n X := rfl

/-! ## 2.  `RelaxMem` at the state, from the `ok` answer and the exact pivot verdict -/

/-- **The `ok`-round `RelaxMem` certificate at the state.**  Every hypothesis except the pivot
verdict is a state read-out: the block's PSD clause comes from `runPiv`'s `false` on the state's own
rows (`PivExact.psd_margin_of_false`), the objective bridge from the state's weight code. -/
theorem hmem_at_state {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {s : QMCLeafB.RoundProgram.RSt}
    {acc : QMCLeafB.PivotProgram.Acc} {dq : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = n)
    (hlenA : n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hAcode : QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stA s) = A)
    (hok : (QMCLeafB.OkLower.oracleV s).1 = false)
    (hpos : 0 < QMCLeafB.RoundT.massV s)
    (hsym : ∀ i j : Fin n,
      QMCLeafB.PivExact.matOf n (QMCLeafB.RoundProgram.stX s) i j
        = QMCLeafB.PivExact.matOf n (QMCLeafB.RoundProgram.stX s) j i)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (n, QMCLeafB.RoundProgram.stX s), acc)).1 = false)
    (hdq : QMCLeafB.OkLower.dqOf s = dq) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s))
      (QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s) dq := by
  have hF : QMCLeafB.RoundProgram.fvR s
      = QMCLeafB.SepOracle.frob A
        (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) := by
    rw [QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX, hAcode]
  have hdq0 : (0 : ℚ) ≤ QMCLeafB.OkLower.dqOf s := by
    unfold QMCLeafB.OkLower.dqOf QMCLeafB.RoundT.epsOf
    have h2 : (0 : ℚ) < 9 * QMCLeafB.RoundT.massV s + 1 := by linarith
    positivity
  have hpsd : ∀ x : Fin n → ℚ,
      -(QMCLeafB.OkLower.dqOf s / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) x :=
    QMCLeafB.PivExact.psd_margin_of_false (dq := QMCLeafB.OkLower.dqOf s) hdq0 hlenX hsym hpiv
  rw [← hdq]
  exact QMCLeafB.StateDiag.relaxMem_of_oracleV_ok_state hN hlenX hF hok hpos hpsd

/-! ## 3.  The slot form: literally `BundleFull.hmem` -/

/-- **The `hmem` field of `BundleFull`**, produced from the per-round states.  `s k` is the `RSt` at
round `k` and `cX k` its block; `hdq` ties the state's own tolerance to the run's. -/
theorem hmem_slot {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (ok : ℕ → Bool) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (s : ℕ → QMCLeafB.RoundProgram.RSt) (acc : ℕ → QMCLeafB.PivotProgram.Acc)
    (hcX : ∀ k, cX k = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (s k)))
    (hN : ∀ k, QMCLeafB.RoundProgram.stN (s k) = G.n)
    (hlenA : ∀ k, G.n ≤ (QMCLeafB.RoundProgram.stA (s k)).length)
    (hlenX : ∀ k, G.n ≤ (QMCLeafB.RoundProgram.stX (s k)).length)
    (hAcode : ∀ k, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (s k))
      = QMCLeafB.Finalization.wMatrixQ G)
    (hok : ∀ k, ok k = true → (QMCLeafB.OkLower.oracleV (s k)).1 = false)
    (hpos : ∀ k, ok k = true → 0 < QMCLeafB.RoundT.massV (s k))
    (hsym : ∀ (k : ℕ) (i j : Fin G.n),
      QMCLeafB.PivExact.matOf G.n (QMCLeafB.RoundProgram.stX (s k)) i j
        = QMCLeafB.PivExact.matOf G.n (QMCLeafB.RoundProgram.stX (s k)) j i)
    (hpiv : ∀ k, ok k = true → (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (s k)), acc k)).1 = false)
    (hT : ∀ k, ok k = true →
      QMCLeafB.RoundProgram.stT (s k) - QMCLeafB.RoundT.epsOf (s k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdq : ∀ k, QMCLeafB.OkLower.dqOf (s k) = P.dq) :
    ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
  intro k _ hk
  rw [hcX k, ← hT k hk]
  exact hmem_at_state (hN k) (hlenA k) (hlenX k) (hAcode k) (hok k hk) (hpos k hk)
    (hsym k) (hpiv k hk) (hdq k)

end QMCLeafB.HmemState

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.HmemState.matOf_eq_stMat
#print axioms QMCLeafB.HmemState.hmem_at_state
#print axioms QMCLeafB.HmemState.hmem_slot


