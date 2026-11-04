-- Prove2me | Definitions.Def_QMCLeafB_pivsnap
-- name    : QMCLeafB_pivsnap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:31:10.269758+00:00
-- url     : https://prove2.me/theorems/3c1ef1e0-45d0-44ad-9169-484ff18396e5
-- title:
--   QMCLeafB pivsnap
-- statement:
--   # leaf B phase 18 — `round`'s PSD test is unsound: the snapped descent certifies an indefinite block
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_round_program_m3
import Definitions.Def_QMCLeafB_run_induction_m1
/-
# leaf B phase 18 — `round`'s PSD test is unsound: the snapped descent certifies an indefinite block
(swarm `smw1ez4a9`, member m1)

The residual `hd` needs `RunParts.hcert` at every `ok` round, and at `RoundProgram.round` a round is
`ok` exactly when `dvR s = 0`, `stT s ≤ fvR s` and `¬(pivAns s).1`.  The published route to the PSD
half of that certificate is `RunInduction.runPiv_psd`,

    (runPiv (rows, acc)).1 = false → SepOracle.PSD X      (given RowCode k X rows, X symmetric),

i.e. the spec of the **exact** LDLᵀ descent `PivotProgram.pivStep` / `runPiv`, whose Schur branch is
`brSchur st = Sum.inr (schurRows st.1, …)` — *no clip, no snap*.

But the state's test is **not** `runPiv`.  `RoundProgram.pivAns s` is `runPivL`, whose Schur branch is

    brSchurL p = Sum.inr (p.1, (nrmRows p.1.1 p.1.2 (schurRows p.2.1), …)),

and `nrmRows mu d` clips every entry into `[-mu, mu]` and then **truncates toward zero** onto the grid
`(1/d)ℤ` (`nrmQ mu d q = snapDiv d (clipRat mu q)`, `snapDiv d q = mkRat (snapTrunc (q*d)) d`,
`snapTrunc` truncates).  So `runPivL` descends on a *perturbed* matrix, and `¬(pivAns s).1` is a
statement about the perturbed trajectory, not about the state's block.

This file makes the gap concrete and machine-checked on the smallest indefinite block:

    Xbad = [[2, 3], [3, 4]]      (row-major code [2, 3, 3, 4];  det = -1, so not PSD)

* the exact descent cuts:      `runPiv ([[2,3],[3,4]], []) = (true, [1])`;
* the state's descent says ok: `runPivL ((1,1), ([[2,3],[3,4]], [])) = (false, [])`
  — its Schur complement `4 - 3²/2 = -1/2` is truncated to `0` on the grid `1/1`, after which the
  descent drops the zero pivot and stops with `(false, [])`;
* and `qf Xbad (3, -2) = -2 < 0`, so `¬ PSD Xbad`.

Hence `∃ s : RSt, (pivAns s).1 = false ∧ ¬ PSD (stMat s)`: **the implication the ok-branch certificate
needs is false**, so `hmem`'s PSD clause cannot be obtained from `¬(pivAns s).1` at
`RoundProgram.round`, and `RunParts.hcert` at an `ok` round of that round is not derivable from the
oracle's answer.

The repair is small and worth stating: `runPiv` needs **no** `mu` and **no** `d` — the rational box
bound exists only to make the clip/snap a `Poly` machine.  Running the *exact* descent on
`toRows (stN s, stX s)` restores `runPiv_psd` verbatim (and `runPiv_cut` for the cut branch), at the
cost of re-proving `Poly (fun s => runPiv (toRows (stN s, stX s), []))` — a list-recursion `Poly`
along the lines of the existing `poly_runPivN`/`poly_runPivL`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram
open QMCLeafB.PivotProgram

namespace QMCLeafB.PivSnapM1

/-! ## 1.  The indefinite block -/

/-- `[[2,3],[3,4]]` in row-major form: an indefinite `2 × 2` block (`det = -1`). -/
def Xbad : List ℚ := [2, 3, 3, 4]

theorem toRows_two' (a b c d : ℚ) : toRows (2, [a, b, c, d]) = [[a, b], [c, d]] := by
  simp [toRows, idxs, rowOf, entV, List.range_succ, List.range_zero, List.getD]

theorem Xbad_rows : toRows (2, Xbad) = [[2, 3], [3, 4]] := by
  rw [Xbad]
  exact toRows_two' 2 3 3 4

theorem Xbad_toMatrix :
    MatQ.toMatrix 2 Xbad = !![(2 : ℚ), 3; 3, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatQ.toMatrix, MatQ.entry, Xbad]

theorem qf_Xbad :
    QMCLeafB.SepOracle.qf (MatQ.toMatrix 2 Xbad)
      (fun i : Fin 2 => if i = 0 then (3 : ℚ) else -2) = -2 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, Xbad_toMatrix]
  simp [Fin.sum_univ_two]
  norm_num

/-- **`Xbad` is not PSD**: the direction `(3, -2)` has `qf = -2`. -/
theorem not_psd_Xbad : ¬ QMCLeafB.SepOracle.PSD (MatQ.toMatrix 2 Xbad) := by
  intro h
  have h2 := h (fun i : Fin 2 => if i = 0 then (3 : ℚ) else -2)
  rw [qf_Xbad] at h2
  norm_num at h2

/-! ## 2.  The exact descent cuts -/

theorem schur_rows_bad : schurRows ([[2, 3], [3, 4]] : Rows) = [[-1 / 2]] := by
  norm_num [schurRows, schurRowStep, piv, headRowD, headTail, mul_one]

theorem pivStep_bad : pivStep ([[2, 3], [3, 4]], ([] : Acc)) = Sum.inr ([[-1 / 2]], [(2, [3])]) := by
  rw [pivStep]
  norm_num [piv, headRowD, headTail, List.isEmpty, brSchur, schurRows, schurRowStep, mul_one]

theorem pivStep_bad2 : pivStep ([[-1 / 2]], [(2, [3])]) = Sum.inl (true, [1]) := by
  rw [pivStep]
  norm_num [piv, headRowD, headTail, List.isEmpty, brNeg, negWitness]

theorem runPiv_Xbad : QMCLeafB.PivotProgram.runPiv (([[2, 3], [3, 4]] : Rows), ([] : Acc))
    = (true, [1]) := by
  have hlen : ([[2, 3], [3, 4]] : Rows).length = 2 := rfl
  rw [QMCLeafB.PivotProgram.runPiv, hlen]
  show (match pivStep ([[2, 3], [3, 4]], ([] : Acc)) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.PivotProgram.runPivFuel 1 p') = (true, [1])
  rw [pivStep_bad]
  show (match pivStep ([[-1 / 2]], [(2, [3])]) with
    | Sum.inl a => a
    | Sum.inr p' => QMCLeafB.PivotProgram.runPivFuel 0 p') = (true, [1])
  rw [pivStep_bad2]

/-! ## 3.  The state's descent says `ok`

The snap: the Schur complement `4 - 3·3/2 = -1/2` is truncated to `0` on the grid `(1/1)ℤ`. -/

theorem nrm_one_half : nrmRows 4 1 ([[-1 / 2]] : Rows) = [[0]] := by
  norm_num [nrmRows, nrmRow, nrmQ, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem nrmAcc_bad : nrmAcc 4 1 ([(2, [3])] : Acc) = [(2, [3])] := by
  norm_num [nrmAcc, nrmPair, nrmRow, nrmQ, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem pivStepL_bad : pivStepL ((4, 1), ([[2, 3], [3, 4]], ([] : Acc)))
    = Sum.inr ((4, 1), ([[0]], [(2, [3])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, brSchurL, schurRows, schurRowStep, mul_one,
    nrmRows, nrmRow, nrmQ, nrmAcc, nrmPair, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem pivStepL_bad2 : pivStepL ((4, 1), ([[0]], [(2, [3])]))
    = Sum.inr ((4, 1), ([], [(2, [3])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, rowSq, brDropL, dropRows,
    nrmRows, nrmRow, nrmQ, nrmAcc, nrmPair, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem runPivL_Xbad : runPivL ((4, 1), ([[2, 3], [3, 4]], ([] : Acc))) = (false, []) := by
  have hlen : ([[2, 3], [3, 4]] : Rows).length = 2 := rfl
  rw [runPivL, hlen]
  show (match pivStepL ((4, 1), ([[2, 3], [3, 4]], ([] : Acc))) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 1 p') = (false, [])
  rw [pivStepL_bad]
  show (match pivStepL ((4, 1), ([[0]], [(2, [3])])) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 0 p') = (false, [])
  rw [pivStepL_bad2]
  rfl

/-! ## 4.  The two descents disagree on the same rows -/

theorem descents_disagree :
    runPivL ((4, 1), ([[2, 3], [3, 4]], ([] : Acc)))
      ≠ QMCLeafB.PivotProgram.runPiv (([[2, 3], [3, 4]] : Rows), ([] : Acc)) := by
  rw [runPivL_Xbad, runPiv_Xbad]
  exact fun h => Bool.noConfusion (congrArg Prod.fst h)

/-! ## 5.  The consequence: the ok branch of `round` is not certified by its own descent -/

/-- The state carrying the indefinite block: `n = 2`, `X = Xbad`, `mu = 4`, `d = 1`. -/
def sBad : RSt := mkSt 2 [] Xbad 0 4 1 [] []

theorem sBad_pivAns : (pivAns sBad).1 = false := by
  rw [pivAns]
  show (runPivL ((4, 1), (toRows (2, Xbad), ([] : Acc)))).1 = false
  rw [Xbad_rows, runPivL_Xbad]

theorem sBad_matrix : MatQ.toMatrix (stN sBad) (stX sBad) = MatQ.toMatrix 2 Xbad := rfl

/-- **The unsoundness, in the form the residual needs.**  There is a state whose own PSD test answers
`ok` (`(pivAns s).1 = false`) while the state's block is provably not PSD — so
`¬(pivAns s).1 → SepOracle.PSD (MatQ.toMatrix (stN s) (stX s))` is false, and the `ok`-branch
certificate cannot be read off the descent at `RoundProgram.round`. -/
theorem pivAns_not_sound :
    ∃ s : RSt, (pivAns s).1 = false
      ∧ ¬ QMCLeafB.SepOracle.PSD (MatQ.toMatrix (stN s) (stX s)) := by
  refine ⟨sBad, sBad_pivAns, ?_⟩
  rw [sBad_matrix]
  exact not_psd_Xbad


/-! ## 6.  The same at a state whose code lies on the campaign's own grid

`sBad` uses `d = 1`; that invites the objection that only coarse grids are fooled.  At `n = 2` the
campaign's grid is `gridOf 2 = 81` and the box bound is `muOf G ≥ 8`, and the block

    Xgrid = [[2/81, 3/81], [3/81, 4/81]]      (all four entries on the grid (1/81)ℤ)

does the same job: its Schur complement is `4/81 - (3/81)²/(2/81) = -1/162`, and snapping at
`1/81` truncates `-1/162 · 81 = -1/2` to `0`. -/

def Xgrid : List ℚ := [2 / 81, 3 / 81, 3 / 81, 4 / 81]

theorem Xgrid_rows : toRows (2, Xgrid) = [[2 / 81, 3 / 81], [3 / 81, 4 / 81]] := by
  rw [Xgrid]
  exact toRows_two' _ _ _ _

theorem Xgrid_toMatrix :
    MatQ.toMatrix 2 Xgrid = !![(2 / 81 : ℚ), 3 / 81; 3 / 81, 4 / 81] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatQ.toMatrix, MatQ.entry, Xgrid]

theorem qf_Xgrid :
    QMCLeafB.SepOracle.qf (MatQ.toMatrix 2 Xgrid)
      (fun i : Fin 2 => if i = 0 then (3 : ℚ) else -2) = -2 / 81 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, Xgrid_toMatrix]
  simp [Fin.sum_univ_two]
  norm_num

theorem not_psd_Xgrid : ¬ QMCLeafB.SepOracle.PSD (MatQ.toMatrix 2 Xgrid) := by
  intro h
  have h2 := h (fun i : Fin 2 => if i = 0 then (3 : ℚ) else -2)
  rw [qf_Xgrid] at h2
  norm_num at h2

theorem pivStepL_grid :
    pivStepL ((8, 81), ([[2 / 81, 3 / 81], [3 / 81, 4 / 81]], ([] : Acc)))
      = Sum.inr ((8, 81), ([[0]], [(2 / 81, [3 / 81])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, brSchurL, schurRows, schurRowStep, mul_one,
    nrmRows, nrmRow, nrmQ, nrmAcc, nrmPair, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem pivStepL_grid2 :
    pivStepL ((8, 81), ([[0]], [(2 / 81, [3 / 81])]))
      = Sum.inr ((8, 81), ([], [(2 / 81, [3 / 81])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, rowSq, brDropL, dropRows,
    nrmRows, nrmRow, nrmQ, nrmAcc, nrmPair, clipRat, inBoxR,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

theorem runPivL_grid :
    runPivL ((8, 81), ([[2 / 81, 3 / 81], [3 / 81, 4 / 81]], ([] : Acc))) = (false, []) := by
  have hlen : ([[2 / 81, 3 / 81], [3 / 81, 4 / 81]] : Rows).length = 2 := rfl
  rw [runPivL, hlen]
  show (match pivStepL ((8, 81), ([[2 / 81, 3 / 81], [3 / 81, 4 / 81]], ([] : Acc))) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 1 p') = (false, [])
  rw [pivStepL_grid]
  show (match pivStepL ((8, 81), ([[0]], [(2 / 81, [3 / 81])])) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 0 p') = (false, [])
  rw [pivStepL_grid2]
  rfl

/-- The grid-aligned state: `n = 2`, `d = gridOf 2 = 81`, `mu = 8`, code `Xgrid`. -/
def sGrid : RSt := mkSt 2 [] Xgrid 0 8 81 [] []

theorem sGrid_pivAns : (pivAns sGrid).1 = false := by
  rw [pivAns]
  show (runPivL ((8, 81), (toRows (2, Xgrid), ([] : Acc)))).1 = false
  rw [Xgrid_rows, runPivL_grid]

theorem sGrid_matrix : MatQ.toMatrix (stN sGrid) (stX sGrid) = MatQ.toMatrix 2 Xgrid := rfl

/-- **The unsoundness at a grid state**: the PSD test answers `ok` while the block is indefinite, with
every entry of the code on the campaign's own `(1/81)ℤ` and `mu = 8`. -/
theorem pivAns_not_sound_grid :
    ∃ s : RSt, stD s = 81 ∧ stMu s = 8 ∧ (pivAns s).1 = false
      ∧ ¬ QMCLeafB.SepOracle.PSD (MatQ.toMatrix (stN s) (stX s)) := by
  refine ⟨sGrid, rfl, rfl, sGrid_pivAns, ?_⟩
  rw [sGrid_matrix]
  exact not_psd_Xgrid

end QMCLeafB.PivSnapM1

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.PivSnapM1.Xbad_rows
#print axioms QMCLeafB.PivSnapM1.qf_Xbad
#print axioms QMCLeafB.PivSnapM1.not_psd_Xbad
#print axioms QMCLeafB.PivSnapM1.runPiv_Xbad
#print axioms QMCLeafB.PivSnapM1.schur_rows_bad
#print axioms QMCLeafB.PivSnapM1.pivStep_bad
#print axioms QMCLeafB.PivSnapM1.nrm_one_half
#print axioms QMCLeafB.PivSnapM1.nrmAcc_bad
#print axioms QMCLeafB.PivSnapM1.pivStepL_bad
#print axioms QMCLeafB.PivSnapM1.runPivL_Xbad
#print axioms QMCLeafB.PivSnapM1.descents_disagree
#print axioms QMCLeafB.PivSnapM1.sBad_matrix
#print axioms QMCLeafB.PivSnapM1.sBad_pivAns
#print axioms QMCLeafB.PivSnapM1.pivAns_not_sound
#print axioms QMCLeafB.PivSnapM1.qf_Xgrid
#print axioms QMCLeafB.PivSnapM1.not_psd_Xgrid
#print axioms QMCLeafB.PivSnapM1.runPivL_grid
#print axioms QMCLeafB.PivSnapM1.pivAns_not_sound_grid


