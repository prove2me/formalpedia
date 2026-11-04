-- Prove2me | Definitions.Def_QMCLeafB_unitdiag_m7
-- name    : QMCLeafB_unitdiag_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:04:12.916796+00:00
-- url     : https://prove2.me/theorems/ca4f219c-fc87-427a-ac35-fbac41dfb474
-- title:
--   QMCLeafB unitdiag_m7
-- statement:
--   # leaf B phase 19 — `unit-diagonal-pivot` (swarm `smw1k12jb`, member m7, direction d3, part 2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_contract_m7
import Definitions.Def_QMCLeafB_pivsnap
/-
# leaf B phase 19 — `unit-diagonal-pivot` (swarm `smw1k12jb`, member m7, direction d3, part 2)

Phase 19's brick 1 (`snapped-pivot-spec`) cannot be rescued by restricting it to the states on which
the campaign's `ok` branch is ever asked to certify `RelaxMem`: this file shows the **unit-diagonal**
restriction is false too, at the campaign's own grid (`d = gridOf 2 = 81`) and box (`mu = 8`).

The state

    `Xud = [1, 325/324, 325/324, 1]`      (`n = 2`, unit diagonal, `mu = 8`, `d = 81`)

is unit-diagonal, i.e. `dvR sUd = 0` — exactly the condition `RoundProgram.round`'s `ok` test
imposes (`Check_stateDiag_m2`: `dvR = 0` **iff** unit diagonal) and the one under which
`StateDiag.relaxMem_of_oracleV_ok_state` discharges `diag_near`, the trace slot and `fvR = frob`.

* the **snapped** descent answers `ok`:  `pivAns sUd = (false, [])`
  (its Schur complement `1 - (325/324)² = -649/104976` is truncated to `0` on the `(1/81)ℤ` grid,
  after which the zero pivot is dropped and the descent stops with `false`);
* the **exact** descent cuts:  `runPiv (toRows (2, Xud), []) = (true, [1])`;
* the state's matrix is **not PSD**: `qf (stMat sUd) (1, -1) = -1/162`, so a `δ`-margined
  `RelaxMem.psd_margin` at this state needs `δ ≥ 2·(1/162)/2 = 1/162` (`tolerance_floor` in
  `Check_contract_m7`), while the campaign tolerance is `dqShallow G ≤ 1/360000 < 1/162`.

So `¬ (∀ s, dvR s = 0 → pivAns s = false → PivPsdMargin s (dqShallow G))`: **the campaign's `ok`
test, at the campaign's grid, does not certify the PSD clause at the states where it fires** — the
defect is not an artefact of asking the pivot test about arbitrary states, and the `dvR = 0` retreat
does not repair brick 1.  (The repair has to be the grid: the certifiable margin is `≳ 4/(13 d)`,
`Check_contract_m7`'s §2, so `d ≳ 1/dq` is needed — the campaign's `gridOf n = (n+1)^4` is far too
coarse at `n = 2`.)

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.UnitDiagPivotM7

open QuantumMaxCutEnergy
open QMCLeafB.PivotProgram

/-! ## 1.  The unit-diagonal state -/

/-- Row-major code of `[[1, 325/324], [325/324, 1]]`: unit diagonal, `eigenvalues 1 ± 325/324`, so
`λ_min = -1/324` in magnitude `1/324` — just below the diagonal, and *one grid unit* wide at
`d = 81` (its Schur complement `-649/104976` truncates to `0`). -/
def Xud : List ℚ := [1, 325/324, 325/324, 1]

/-- The state: `n = 2`, empty weight code, code `Xud`, `t = 0`, `mu = 8` (`muOf 2`), `d = 81`
(`gridOf 2`), no flags, no records. -/
def sUd : RSt := mkSt 2 [] Xud 0 8 81 [] []

theorem toRows_ud : toRows (2, Xud) = [[(1 : ℚ), 325/324], [325/324, 1]] := by
  rw [Xud]
  exact QMCLeafB.PivSnapM1.toRows_two' 1 (325/324) (325/324) 1

theorem Xud_toMatrix : MatQ.toMatrix 2 Xud = !![(1 : ℚ), 325/324; 325/324, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatQ.toMatrix, MatQ.entry, Xud]

/-- **The state's matrix is not PSD**: `qf` at `(1, -1)` is `-1/162`. -/
theorem qf_Xud :
    QMCLeafB.SepOracle.qf (MatQ.toMatrix 2 Xud)
      (fun i : Fin 2 => if i = 0 then (1 : ℚ) else -1) = -1 / 162 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, Xud_toMatrix]
  simp [Fin.sum_univ_two]
  norm_num

/-- The witness `(1, -1)` has norm squared `2`. -/
theorem sum_sq_ud : (∑ i : Fin 2, (fun j : Fin 2 => if j = 0 then (1 : ℚ) else -1) i ^ 2) = 2 := by
  rw [Fin.sum_univ_two]
  norm_num

theorem not_psd_Xud : ¬ QMCLeafB.SepOracle.PSD (MatQ.toMatrix 2 Xud) := by
  intro h
  have h2 := h (fun i : Fin 2 => if i = 0 then (1 : ℚ) else -1)
  rw [qf_Xud] at h2
  norm_num at h2

/-! ## 2.  The two descents disagree at `Xud` -/

theorem pivStep_ud :
    pivStep ([[(1 : ℚ), 325/324], [325/324, 1]], ([] : Acc))
      = Sum.inr ([[1 - (325/324) * (325/324)]], [(1, [325/324])]) := by
  rw [pivStep]
  norm_num [piv, headRowD, headTail, List.isEmpty, brSchur, schurRows, schurRowStep]

theorem pivStep_ud2 :
    pivStep ([[(1 : ℚ) - (325/324) * (325/324)]], [(1, [325/324])])
      = Sum.inl (true, [1]) := by
  rw [pivStep]
  norm_num [piv, headRowD, headTail, List.isEmpty, brNeg, negWitness]

/-- **The exact descent cuts** the unit-diagonal state (correctly: the state is not PSD). -/
theorem runPiv_ud :
    runPiv (toRows (2, Xud), ([] : Acc)) = (true, [1]) := by
  rw [toRows_ud]
  have hlen : ([[(1 : ℚ), 325/324], [325/324, 1]] : Rows).length = 2 := rfl
  rw [QMCLeafB.PivotProgram.runPiv, hlen]
  show (match pivStep ([[(1 : ℚ), 325/324], [325/324, 1]], ([] : Acc)) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.PivotProgram.runPivFuel 1 p') = (true, [1])
  rw [pivStep_ud]
  show (match pivStep ([[(1 : ℚ) - (325/324) * (325/324)]], [(1, [325/324])]) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.PivotProgram.runPivFuel 0 p') = (true, [1])
  rw [pivStep_ud2]

/-- **The snapped descent says `ok`**: the Schur complement `-649/104976` is truncated to `0` at
`d = 81` (`81 · 649/104976 = 0.5007…`). -/
theorem pivStepL_ud1 :
    pivStepL ((8, 81), ([[(1 : ℚ), 325/324], [325/324, 1]], ([] : Acc)))
      = Sum.inr ((8, 81), ([[0]], [(1, [1])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, brSchurL, schurRows, schurRowStep, mul_one,
    nrmRows, nrmRow, nrmQ, nrmAcc, nrmPair, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem pivStepL_ud2 :
    pivStepL ((8, 81), ([[(0 : ℚ)]], [(1, [1])])) = Sum.inr ((8, 81), ([], [(1, [1])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, rowSq, brDropL, dropRows,
    nrmRows, nrmRow, nrmQ, nrmAcc, nrmPair, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem runPivL_ud : runPivL ((8, 81), (toRows (2, Xud), ([] : Acc))) = (false, []) := by
  rw [toRows_ud]
  have hlen : ([[(1 : ℚ), 325/324], [325/324, 1]] : Rows).length = 2 := rfl
  rw [runPivL, hlen]
  show (match pivStepL ((8, 81), ([[(1 : ℚ), 325/324], [325/324, 1]], ([] : Acc))) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 1 p') = (false, [])
  rw [pivStepL_ud1]
  show (match pivStepL ((8, 81), ([[(0 : ℚ)]], [(1, [1])])) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 0 p') = (false, [])
  rw [pivStepL_ud2]
  rfl

/-- **The two descents disagree at a unit-diagonal state.** -/
theorem descents_disagree_ud :
    runPivL ((8, 81), (toRows (2, Xud), ([] : Acc))) ≠ runPiv (toRows (2, Xud), ([] : Acc)) := by
  rw [runPivL_ud, runPiv_ud]
  exact fun h => Bool.noConfusion (congrArg Prod.fst h)

/-! ## 3.  The state's own verdicts -/

theorem sUd_pivAns : (pivAns sUd).1 = false := by
  rw [pivAns]
  show (runPivL ((8, 81), (toRows (2, Xud), ([] : Acc)))).1 = false
  rw [runPivL_ud]

/-- The index list of the `2 x 2` code is `[0, 1]`. -/
theorem idxs_ud : QMCLeafB.RoundProgram.idxs (2, Xud) = [0, 1] := by
  unfold QMCLeafB.RoundProgram.idxs
  norm_num [Xud, Nat.min_def, List.range_succ]

/-- **`sUd` is unit-diagonal** (`dvR = 0`) — computed on the diagonal read-out. -/
theorem sUd_unitDiag : dvR sUd = 0 := by
  rw [dvR]
  have hN : stN sUd = 2 := rfl
  have hX : stX sUd = Xud := rfl
  rw [hN, hX]
  unfold QMCLeafB.RoundProgram.diagSumV
  rw [idxs_ud]
  simp [QMCLeafB.RoundProgram.entV, QMCLeafB.RoundProgram.absq, Xud]

theorem sUd_matrix : MatQ.toMatrix (stN sUd) (stX sUd) = MatQ.toMatrix 2 Xud := rfl

/-- The state's diagonal entries are all `1`. -/
theorem sUd_diag_one (i : Fin 2) : MatQ.toMatrix 2 Xud i i = 1 := by
  fin_cases i <;> simp [MatQ.toMatrix, MatQ.entry, Xud]

/-- The state's trace read-out is `n = 2` (unit diagonal), the second structural side condition.
(The matrix is the state's up to the definitional `stN sUd = 2`, so the sum is stated over `Fin 2`.) -/
theorem sUd_trace : (∑ i : Fin 2, MatQ.toMatrix 2 Xud i i) = 2 := by
  rw [Fin.sum_univ_two, sUd_diag_one 0, sUd_diag_one 1]
  norm_num

/-! ## 4.  The PSD-margin clause fails at the unit-diagonal state -/

/-- The `qf` value in the *state's* index type (`Fin (stN sUd)` has no `OfNat`, so the witness is
written with a natural-number comparison). -/
theorem qf_Xud_nat :
    QMCLeafB.SepOracle.qf
      (MatQ.toMatrix (stN sUd) (stX sUd))
      (fun i : Fin (stN sUd) => if (i : ℕ) = 0 then (1 : ℚ) else -1) = -1 / 162 := by
  have hN : stN sUd = 2 := rfl
  rw [sUd_matrix]
  exact qf_Xud

/-- **At the unit-diagonal state, the `δ`-margined PSD clause needs `δ ≥ 1/162`.** -/
theorem not_pivPsdMargin_sUd {δ : ℚ} (h : δ < 1 / 162) :
    ¬ QMCLeafB.ContractM7.PivPsdMargin sUd δ := by
  intro hm
  have hN : stN sUd = 2 := rfl
  have h0 := hm (fun i : Fin (stN sUd) => if (i : ℕ) = 0 then (1 : ℚ) else -1)
  have hs : (∑ i : Fin (stN sUd),
      (if (i : ℕ) = 0 then (1 : ℚ) else -1) ^ 2) = 2 := by
    rw [hN]
    rw [Fin.sum_univ_two]
    norm_num
  rw [hs, qf_Xud_nat] at h0
  linarith

#print axioms QMCLeafB.UnitDiagPivotM7.not_pivPsdMargin_sUd

/-- **Brick 1 does not survive restriction to the campaign's `ok`-round states.**  For every
`δ < 1/162` there is a unit-diagonal state (`dvR = 0`) whose own snapped PSD test answers `false`
while the `δ`-margined PSD clause fails there. -/
theorem unitDiag_pivFSpec_false {δ : ℚ} (h : δ < 1 / 162) :
    ¬ (∀ s : RSt, dvR s = 0 → (pivAns s).1 = false →
        QMCLeafB.ContractM7.PivPsdMargin s δ) := by
  intro hf
  exact not_pivPsdMargin_sUd h (hf sUd sUd_unitDiag sUd_pivAns)

#print axioms QMCLeafB.UnitDiagPivotM7.unitDiag_pivFSpec_false

/-- **The campaign tolerance is below the unit-diagonal floor too** (`1/162 ≈ 6.2·10⁻³` against
`dqShallow G ≤ 1/360000`). -/
theorem dqShallow_lt_unitDiag_floor (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G < 1 / 162 := by
  have h := QMCLeafB.ContractM7.dqShallow_lt_floor hRq
  linarith

#print axioms QMCLeafB.UnitDiagPivotM7.dqShallow_lt_unitDiag_floor

/-- **The `ok` branch at the campaign's parameters is not certified by its own descent** — the
answer to phase 19's brick 1 on exactly the states the `ok` branch fires at. -/
theorem unitDiag_pivFSpec_false_campaign (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    ¬ (∀ s : RSt, dvR s = 0 → (pivAns s).1 = false →
        QMCLeafB.ContractM7.PivPsdMargin s (QMCLeafB.RundataParams.dqShallow G)) :=
  unitDiag_pivFSpec_false (dqShallow_lt_unitDiag_floor G hRq)

#print axioms QMCLeafB.UnitDiagPivotM7.unitDiag_pivFSpec_false_campaign

/-! ## 5.  Non-vacuity: every structural side condition of the `ok` branch holds at `sUd`

`StateDiag.relaxMem_of_oracleV_ok_state` needs (i) unit diagonal (`dvR = 0`, here), (ii) the trace
slot (here), (iii) `fvR = frob` (a definitional bridge, not a property of the state), and (iv) the
PSD clause — which is exactly what fails.  So the failure is not an artefact of a degenerate state. -/

theorem sUd_side_conditions :
    dvR sUd = 0
      ∧ (∀ i : Fin (stN sUd), |MatQ.toMatrix (stN sUd) (stX sUd) i i - 1| ≤ (1 / 162) / 4)
      ∧ ¬ QMCLeafB.SepOracle.PSD (MatQ.toMatrix (stN sUd) (stX sUd)) := by
  refine ⟨sUd_unitDiag, fun i => ?_, ?_⟩
  · have h : MatQ.toMatrix (stN sUd) (stX sUd) i i = 1 := sUd_diag_one i
    rw [h]
    norm_num
  · rw [sUd_matrix]
    exact not_psd_Xud

#print axioms QMCLeafB.UnitDiagPivotM7.sUd_side_conditions

end QMCLeafB.UnitDiagPivotM7

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.UnitDiagPivotM7.toRows_ud
#print axioms QMCLeafB.UnitDiagPivotM7.Xud_toMatrix
#print axioms QMCLeafB.UnitDiagPivotM7.qf_Xud
#print axioms QMCLeafB.UnitDiagPivotM7.not_psd_Xud
#print axioms QMCLeafB.UnitDiagPivotM7.pivStep_ud
#print axioms QMCLeafB.UnitDiagPivotM7.pivStep_ud2
#print axioms QMCLeafB.UnitDiagPivotM7.runPiv_ud
#print axioms QMCLeafB.UnitDiagPivotM7.pivStepL_ud1
#print axioms QMCLeafB.UnitDiagPivotM7.pivStepL_ud2
#print axioms QMCLeafB.UnitDiagPivotM7.runPivL_ud
#print axioms QMCLeafB.UnitDiagPivotM7.descents_disagree_ud
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_pivAns
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_unitDiag
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_trace
#print axioms QMCLeafB.UnitDiagPivotM7.qf_Xud_nat
#print axioms QMCLeafB.UnitDiagPivotM7.not_pivPsdMargin_sUd
#print axioms QMCLeafB.UnitDiagPivotM7.unitDiag_pivFSpec_false
#print axioms QMCLeafB.UnitDiagPivotM7.dqShallow_lt_unitDiag_floor
#print axioms QMCLeafB.UnitDiagPivotM7.unitDiag_pivFSpec_false_campaign
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_side_conditions


