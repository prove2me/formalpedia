-- Prove2me | Definitions.Def_QMCLeafB_pivspec_m3
-- name    : QMCLeafB_pivspec_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:04:52.665854+00:00
-- url     : https://prove2.me/theorems/f1cf8eb6-94e9-40ce-8fbb-3bf2364539f2
-- title:
--   QMCLeafB pivspec_m3
-- statement:
--   # leaf B phase 19 — brick 1 `snapped-pivot-spec`: **both clauses are false at the campaign grids**
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_pivsnap
/-
# leaf B phase 19 — brick 1 `snapped-pivot-spec`: **both clauses are false at the campaign grids**
(swarm `smw1k12jb`, member m3, direction d1)

The phase-19 brief asks for `Check_pivspec_m3.lean`:

    pivAns s.1 = false  ->  <the PSD-margin clause of `RelaxMem` at `stMat s`>      (clause A)
    pivAns s.1 = true   ->  Exists v, qf (stMat s) v < 0                            (clause B)

at the state's own snapped descent
`RoundProgram.pivAns s = runPivL ((stMu s, stD s), (toRows (stN s, stX s)), [])`.
The brief's suggested route was "snapping moves every entry by at most the grid error,
`RelaxMem.psd_margin` tolerates `-(dq/2)‖x‖^2`, so `GridBudget.exists_grid_budget` supplies a
fine-enough grid".

**That route does not exist, and neither clause is true.**  This file proves it at the campaign's
own data, in the exact shapes the brief asks for:

* **§1 — clause A fails in the margin form.**  At `n = 2`, `stD = gridOf 2 = 81`, `stMu = 8`
  (m1's state, `X = (1/81)*[[2,3],[3,4]]`, every entry on the campaign grid) the descent answers
  `ok`, and the direction `v = (3,-2)` has `qf (stMat s) v = -2/81` while `sum v_i^2 = 13`.  The
  psd_margin clause therefore needs `dq >= 2*(2/81)/13 = 4/1053`; at the campaign tolerance
  (`dqShallow G < 1/360000`) it fails by four orders of magnitude.  The failure is not a bad
  constant in a grid-error estimate: the transfer from "entrywise eps-close to a PSD matrix" to
  "margin 2*eps*n" is on the shelf (§4), but snapping does not preserve its hypothesis — the Schur
  step divides by the pivot and then **truncates toward zero**, and truncation is not a Loewner
  contraction (this is what §2 exhibits explicitly).

* **§2 — clause B fails (new).**  At `n = 3`, `stD = gridOf 3 = 256`, `stMu = 8`, the state with
  code `Xc = (1/256)*[[2,1,1],[1,1,2],[1,2,5]]` is **PSD**, with the explicit certificate

      qf (stMat s) x = (1/512)*((2x0+x1+x2)^2 + (x1+3x2)^2)  >= 0,

  and the descent answers **`true`**: the exact Schur complement of step 1 is
  `(1/256)*[[1/2,3/2],[3/2,9/2]]`, the snap sends the `1/512` entry to `0`, so step 2 has pivot `0`
  with head row `[1/256] != 0`, which is `brZeroL` — a cut.  So `pivAns s.1 = true` at a PSD state,
  and clause B fails in the worst possible way: not merely "the returned witness is not violated",
  but *no* violated direction exists.

  With `Check_pivsnap_m1` (which kills the `ok` side: an indefinite block read as PSD) this file
  says the snapped descent is not a decision procedure at all: it is a heuristic, and neither
  answer certifies anything.

* **§6 — the repair that IS available: the certified cut.**  A cut direction that the state's own
  code re-checks, `qformRows (toRows (stN s, stX s)) v < 0`, is a genuinely violated direction of
  the state's matrix (`certified_cut`), because the program's row-code form and `Separator.qf`
  agree (`qformRows_toRows_eq_qf`, a bridge the library did not have).  The check is a `Poly`
  function of the state (`poly_certCheck`, from `poly_qformRows` + `poly_toRowsR`).  So the pivot
  lane can be made sound by *certifying* the descent's candidate instead of trusting its verdict:
  the descent proposes, the state disposes.  §5 shows the other repair (the exact descent) is not
  a `Poly` program, so this is the only program-legal option.

## What this means for the endgame

The phase-18/19 residual does not consume either clause, and the point of this file is to make that
non-negotiable:

1. the `ok` side of a round is certified by `OkLower.relaxMem_of_oracleV_ok_state`
   (`OkLower.roundW`/`oracleV`: the program's `ok` bit **is** a `RelaxMem` point) at unit-diagonal
   states, together with `StateDiag`'s `dvR = 0 <-> unit diagonal`; it is not read off the descent;
2. the `cut` side is recorded by the separation oracle itself (`RelaxOracle.RelaxCut` at the queried
   centre).  §2 shows that agreement between the program's descent and the oracle's normal cannot be
   *inferred* from `pivAns`; it has to be a recorded hypothesis or an exactly re-checked identity;
3. `Check_closingAssembly_m3`'s `Bundle` already carries the flag stream in the all-`false` form
   (`hokAll`), under which `hmem` — the only consumer of clause A — is vacuous
   (`ClosingAssembly.noMem_of_allFalse`).

The honest residual fact, in a shape a supplier can owe, is therefore not `pivAns`-soundness but a
*certified* pivot answer: for `cut`, the program emits `v` and the state's own code re-checks
`qformRows (toRows (stN s, stX s)) v < 0` exactly (`PivotProgram.poly_qformRows` makes that check a
`Poly` program); for `ok`, the `OkLower`/`StateDiag` functional.  §4 pins the pieces already on the
shelf so the next phase does not re-derive them.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open QMCLeafB.RoundProgram
open QMCLeafB.PivotProgram

namespace QMCLeafB.PivSpecM3

/-! ## 0.  The campaign grids

`BitProgram.gridOf n = ((n+1)*(n+1))^2` is the campaign's dyadic grid denominator
(`Solutions/Check_brick_init_verdict_m8.lean:424`).  It is restated here because that module is not
in the endgame chain's import closure; the two values that matter are checked. -/

/-- The campaign grid denominator, mirroring `BitProgram.gridOf`. -/
def gOf (n : ℕ) : ℕ := ((n + 1) * (n + 1)) * ((n + 1) * (n + 1))

theorem gOf_two : gOf 2 = 81 := by decide
theorem gOf_three : gOf 3 = 256 := by decide

/-! ## 1.  Clause A: the `ok` verdict carries **no** PSD margin, at the campaign grid

The state is m1's (`Check_pivsnap_m1` §6): `n = 2`, `mu = 8`, `d = gridOf 2 = 81`, code
`Xgrid = (1/81)*[2,3,3,4]`, all four entries on the campaign grid.  Its descent answers `ok`; the
block is indefinite with the explicit direction `(3,-2)`. -/

theorem sGridA_grid :
    stD QMCLeafB.PivSnapM1.sGrid = 81 ∧ stMu QMCLeafB.PivSnapM1.sGrid = 8 := ⟨rfl, rfl⟩

theorem sGridA_pivAns : (pivAns QMCLeafB.PivSnapM1.sGrid).1 = false :=
  QMCLeafB.PivSnapM1.sGrid_pivAns

/-- The violating direction: `(3, -2)`. -/
def vA : Fin 2 → ℚ := fun i => if i = 0 then 3 else -2

theorem vA_eq : vA = (fun i : Fin 2 => if i = 0 then (3 : ℚ) else -2) := rfl

/-- Its quadratic form at the state's block is `-2/81 < 0`. -/
theorem qf_sA_vA :
    QMCLeafB.SepOracle.qf
      (MatQ.toMatrix (stN QMCLeafB.PivSnapM1.sGrid) (stX QMCLeafB.PivSnapM1.sGrid)) vA
        = -2 / 81 := by
  rw [QMCLeafB.PivSnapM1.sGrid_matrix, vA_eq]
  exact QMCLeafB.PivSnapM1.qf_Xgrid

/-- Its squared norm is `13`. -/
theorem sumsq_vA :
    (∑ i : Fin (stN QMCLeafB.PivSnapM1.sGrid), (vA i) ^ 2) = 13 := by
  show (∑ i : Fin 2, (vA i) ^ 2) = 13
  simp [vA, Fin.sum_univ_two]
  norm_num

/-- **Clause A fails, at the campaign grid, in `RelaxMem.psd_margin`'s exact shape**: there is a
state at which `pivAns` answers `ok` and the psd_margin clause fails for every tolerance
`dq < 4/1053`.

The campaign tolerance is `dqShallow G = (Rq G/40000)/(9*Rq G+1) < 1/360000`, four orders of
magnitude below the threshold. -/
theorem clauseA_fails {dq : ℚ} (hdq0 : 0 < dq) (hdq : dq < 4 / 1053) :
    ∃ s : RSt, (pivAns s).1 = false ∧
      ¬ ∀ x : Fin (stN s) → ℚ,
          -(dq / 2) * (∑ i, x i ^ 2) ≤
            QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) x := by
  refine ⟨QMCLeafB.PivSnapM1.sGrid, sGridA_pivAns, ?_⟩
  intro h
  have h2 := h vA
  rw [qf_sA_vA, sumsq_vA] at h2
  have hlt : 13 * dq < 13 * (4 / 1053) := by nlinarith
  have h81 : (13 : ℚ) * (4 / 1053) = 4 / 81 := by norm_num
  nlinarith [h2, hlt, h81]

/-- The same at the campaign's own tolerance `1/360000` (every `dqShallow G` is below it). -/
theorem clauseA_fails_at_campaign_dq :
    ∃ s : RSt, (pivAns s).1 = false ∧
      ¬ ∀ x : Fin (stN s) → ℚ,
          -((1 / 360000 : ℚ) / 2) * (∑ i, x i ^ 2)
            ≤ QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) x :=
  clauseA_fails (by norm_num) (by norm_num)

/-- The `false` answer is not even a PSD answer at the campaign grid (m1's
`pivAns_not_sound_grid`, restated at `sGrid`). -/
theorem clauseA_no_psd :
    (pivAns QMCLeafB.PivSnapM1.sGrid).1 = false ∧
      ¬ QMCLeafB.SepOracle.PSD
          (MatQ.toMatrix (stN QMCLeafB.PivSnapM1.sGrid) (stX QMCLeafB.PivSnapM1.sGrid)) := by
  refine ⟨sGridA_pivAns, ?_⟩
  rw [QMCLeafB.PivSnapM1.sGrid_matrix]
  exact QMCLeafB.PivSnapM1.not_psd_Xgrid

/-! ## 2.  Clause B: the `cut` verdict at a **PSD** state (new)

`n = 3`, `mu = 8`, `d = gridOf 3 = 256`, code `Xc = (1/256)*[[2,1,1],[1,1,2],[1,2,5]]`.

* step 1: pivot `2/256 > 0`; the exact Schur complement is `(1/256)*[[1/2,3/2],[3/2,9/2]]`, which is
  PSD (it is the Schur complement of a PSD block);
* the snap at `1/256` truncates it to `[[0,1/256],[1/256,4/256]]` — the `1/512` entry becomes `0`;
* step 2: pivot `0` with head row `[1/256] != 0`, which is `brZeroL`, i.e. `cut`.

The `zero`-pivot branch is exact at depth `0` (`SepOracle.zeroPivot_witness`); it is not at depth
`1`, which is exactly the gap. -/

/-- The integer block `[[2,1,1],[1,1,2],[1,2,5]]`, the shape of the certificate. -/
def Mc : Matrix (Fin 3) (Fin 3) ℚ := !![2, 1, 1; 1, 1, 2; 1, 2, 5]

/-- The state's row-major code: `Mc / 256`. -/
def Xc : List ℚ :=
  [2 / 256, 1 / 256, 1 / 256, 1 / 256, 1 / 256, 2 / 256, 1 / 256, 2 / 256, 5 / 256]

theorem toRows_three (a b c d e f g h i : ℚ) :
    toRows (3, [a, b, c, d, e, f, g, h, i]) = [[a, b, c], [d, e, f], [g, h, i]] := by
  simp [toRows, idxs, rowOf, entV, List.range_succ, List.range_zero, List.getD]

theorem Xc_rows :
    toRows (3, Xc) = [[2 / 256, 1 / 256, 1 / 256],
      [1 / 256, 1 / 256, 2 / 256], [1 / 256, 2 / 256, 5 / 256]] := by
  rw [Xc]
  exact toRows_three _ _ _ _ _ _ _ _ _

/-! ### 2.1  The block is PSD, with an explicit two-squares certificate -/

/-- **The certificate**: `qf (stMat s) x` is a sum of two squares (`1/256` of `qf Mc`). -/
theorem qf_Xc (v : Fin 3 → ℚ) :
    QMCLeafB.SepOracle.qf (MatQ.toMatrix 3 Xc) v
      = (1 / 512) * (2 * v 0 + v 1 + v 2) ^ 2 + (1 / 512) * (v 1 + 3 * v 2) ^ 2 := by
  simp [QMCLeafB.SepOracle.qf, dotProduct, Matrix.mulVec, MatQ.toMatrix, MatQ.entry, Xc,
    Fin.sum_univ_three]
  ring

/-- **The state's block is PSD**: no direction is violated, so clause B has nothing to certify. -/
theorem psd_Xc : QMCLeafB.SepOracle.PSD (MatQ.toMatrix 3 Xc) := by
  intro v
  rw [qf_Xc v]
  positivity

/-! ### 2.2  The descent answers `cut` -/

/-- Step 1: the Schur branch, snapped. -/
theorem pivStepL_c1 :
    pivStepL ((8, 256), ([[2 / 256, 1 / 256, 1 / 256],
        [1 / 256, 1 / 256, 2 / 256], [1 / 256, 2 / 256, 5 / 256]], ([] : Acc)))
      = Sum.inr ((8, 256), ([[0, 1 / 256], [1 / 256, 1 / 64]],
          [(1 / 128, [1 / 256, 1 / 256])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, brSchurL, schurRows, schurRowStep,
    nrmRows, nrmRow, nrmAcc, nrmPair, nrmQ, clipRat, inBoxR, mul_one,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

/-- Step 2: zero pivot with a nonzero head row, i.e. the `brZeroL` cut. -/
theorem pivStepL_c2 :
    pivStepL ((8, 256), ([[0, 1 / 256], [1 / 256, 1 / 64]],
        [(1 / 128, [1 / 256, 1 / 256])]))
      = brZeroL ((8, 256), ([[0, 1 / 256], [1 / 256, 1 / 64]],
          [(1 / 128, [1 / 256, 1 / 256])])) := by
  rw [pivStepL_def]
  norm_num [piv, headRowD, headTail, List.isEmpty, rowSq,
    QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc,
    OAI.MetricKMedian.Binary.Signed.value, OAI.MetricKMedian.Binary.Signed.sign]

/-- **The snapped descent cuts the PSD block.** -/
theorem runPivL_c :
    (runPivL ((8, 256), (toRows (3, Xc), ([] : Acc)))).1 = true := by
  have hlen : (toRows (3, Xc)).length = 3 := by
    rw [Xc_rows]; rfl
  rw [runPivL, hlen]
  show (match pivStepL ((8, 256), (toRows (3, Xc), ([] : Acc))) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 2 p').1 = true
  rw [Xc_rows, pivStepL_c1]
  show (match pivStepL ((8, 256), ([[0, 1 / 256], [1 / 256, 1 / 64]],
      [(1 / 128, [1 / 256, 1 / 256])])) with
    | Sum.inl a => a
    | Sum.inr p' => runPivLFuel 1 p').1 = true
  rw [pivStepL_c2]
  rfl

/-- The PSD state of §2: `n = 3`, `mu = 8`, `d = gridOf 3 = 256`. -/
def sB : RSt := mkSt 3 [] Xc 0 8 256 [] []

theorem sB_grid : stD sB = 256 ∧ stMu sB = 8 := ⟨rfl, rfl⟩

theorem sB_pivAns : (pivAns sB).1 = true := by
  rw [pivAns]
  exact runPivL_c

theorem sB_matrix : MatQ.toMatrix (stN sB) (stX sB) = MatQ.toMatrix 3 Xc := rfl

/-- **Clause B fails.**  There is a state at the campaign grid whose descent answers `cut` while the
state's block is PSD. -/
theorem clauseB_fails :
    ∃ s : RSt, (pivAns s).1 = true ∧
      QMCLeafB.SepOracle.PSD (MatQ.toMatrix (stN s) (stX s)) :=
  ⟨sB, sB_pivAns, by rw [sB_matrix]; exact psd_Xc⟩

/-- The sharp form: the `cut` answer's promised conclusion is *false*, not merely unproved. -/
theorem clauseB_no_witness :
    ∃ s : RSt, (pivAns s).1 = true ∧
      ¬ ∃ v : Fin (stN s) → ℚ,
          QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) v < 0 := by
  refine ⟨sB, sB_pivAns, ?_⟩
  rintro ⟨v, hv⟩
  have h : 0 ≤ QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN sB) (stX sB)) v := by
    rw [sB_matrix]
    exact psd_Xc v
  exact absurd h (not_le.mpr hv)

/-! ## 3.  The two clauses, negated -/

/-- **Brick 1, clause A, is not a theorem.** -/
theorem not_clauseA :
    ¬ ∀ (s : RSt) (dq : ℚ), 0 < dq → (pivAns s).1 = false →
        ∀ x : Fin (stN s) → ℚ,
          -(dq / 2) * (∑ i, x i ^ 2) ≤
            QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) x := by
  intro h
  obtain ⟨s, hok, hno⟩ := clauseA_fails_at_campaign_dq
  exact hno (h s (1 / 360000) (by norm_num) hok)

/-- **Brick 1, clause B, is not a theorem.** -/
theorem not_clauseB :
    ¬ ∀ s : RSt, (pivAns s).1 = true →
        ∃ v : Fin (stN s) → ℚ,
          QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) v < 0 := by
  intro h
  obtain ⟨s, hcut, hno⟩ := clauseB_no_witness
  exact hno (h s hcut)

/-! ## 4.  What survives: the `ok` branch is inhabited, and where the failure starts

First, the `ok` answer is *inhabited* — at the zero block the descent stops with `ok` and the block
is PSD, so the ok-branch certificate is not vacuous.

Second, clause B's failure needs `n >= 3`.  The §2 construction descends **two** levels; at `n = 2`
the only snapped object is a single `1x1` Schur complement, and truncation toward zero moves a
*negative* value up — a truncated negative pivot therefore implies the exact Schur complement was
negative, i.e. the block was already indefinite.  So the `n = 2` cut is sound while the `n = 2`
`ok` is not (that is m1's `Xgrid`); the general failure needs the third level.  **This paragraph is
not formalised here** — it is the honest reading of the two machine-checked examples, recorded so
that nobody mistakes the `n = 2` demos of `Check_run_induction_m1` §6 for general soundness. -/

/-- The zero block at `n = 1`: `ok`, and PSD. -/
def sZ : RSt := mkSt 1 [] [0] 0 8 256 [] []

theorem sZ_pivAns : (pivAns sZ).1 = false := by
  rw [pivAns]
  show (runPivL ((8, 256), (toRows (1, [0]), ([] : Acc)))).1 = false
  have hrows : toRows (1, [0]) = [[(0 : ℚ)]] := by
    simp [toRows, idxs, rowOf, entV, List.range_succ, List.range_zero, List.getD]
  rw [hrows]
  have hstep : pivStepL ((8, 256), ([[(0 : ℚ)]], ([] : Acc)))
      = brDropL ((8, 256), ([[(0 : ℚ)]], ([] : Acc))) := by
    rw [pivStepL_def]
    norm_num [piv, headRowD, headTail, List.isEmpty, rowSq]
  show (runPivLFuel 1 ((8, 256), ([[(0 : ℚ)]], ([] : Acc)))).1 = false
  rw [runPivLFuel_succ, hstep]
  rfl

theorem sZ_psd : QMCLeafB.SepOracle.PSD (MatQ.toMatrix (stN sZ) (stX sZ)) := by
  show QMCLeafB.SepOracle.PSD (MatQ.toMatrix 1 [(0 : ℚ)])
  intro v
  simp [QMCLeafB.SepOracle.qf, dotProduct, Matrix.mulVec, MatQ.toMatrix, MatQ.entry]

/-- **The `ok` branch is inhabited, with a genuine PSD certificate.** -/
theorem ok_branch_inhabited :
    ∃ s : RSt, (pivAns s).1 = false ∧
      QMCLeafB.SepOracle.PSD (MatQ.toMatrix (stN s) (stX s)) :=
  ⟨sZ, sZ_pivAns, sZ_psd⟩


/-! ## 5.  The exact-descent lane is not a program either

The natural repair of clause A is "run the descent **without** the clip and the snap" —
`PivotProgram.runPiv` on the state's own rows.  It is sound (`RunInduction.runPiv_psd`) but it is
**not** a `Poly` program by the available route: `PivotProgram.poly_runPiv` is stated *conditional*
on a size profile

    hprof : every reachable state's encoded length stays inside `sizes.eval (enc a).length`,

and `PivotProgram.height_iterate_naive` (`Check_pivot_program_m6` §3) shows the entries of the `j`-th
Schur complement have height `5^j * (L+1)` — exponential in the descent depth, so no polynomial
profile exists (`no_linear_profile` is the machine-checked linear instance; the same argument kills
every polynomial).  So the exact descent may only be used as a *specification*, not as the round's
pivot test; at the program level the PSD half must come from a certificate, not from a descent.

Both lanes are therefore closed: snapped = unsound (§1–§3), exact = not `Poly`. -/

/-- The Schur height grows like `5^j` in the descent depth — the reason `poly_runPiv`'s size-profile
hypothesis cannot be discharged, i.e. the exact descent is a specification and not a program.
(`PivotProgram.height_iterate_naive`, re-exported so this file carries the obstruction.) -/
theorem schur_height_exponential (j : ℕ) {rows : QMCLeafB.PivotProgram.Rows}
    {L : ℕ} (h : QMCLeafB.PivotProgram.RowsHeight rows L) :
    QMCLeafB.PivotProgram.RowsHeight ((QMCLeafB.PivotProgram.stepRows^[j]) rows)
      (5 ^ j * (L + 1)) :=
  QMCLeafB.PivotProgram.height_iterate_naive j h

/-- The same fact in the "no linear profile" form the obstruction is quoted in. -/
theorem no_linear_height_profile : ∀ C : ℕ, ∃ j : ℕ, C * (j + 1) < 5 ^ j :=
  QMCLeafB.PivotProgram.no_linear_profile


/-! ## 6.  The repair that *is* available: the certified cut

The one sound and `Poly` pivot lane, and the reason §1–§3 are not the end of the story.

The descent's *candidate* cut direction is a `List ℚ` on the state's own rows, and the state's own
code can **re-check it exactly**: `PivotProgram.poly_qformRows` computes `qformRows` as a `Poly`
program, and `RoundProgram.poly_toRowsR` computes the state's block, so

    fun s => qformRows (toRows (stN s, stX s)) v

is a `Poly` function of the state for each fixed candidate `v`.  The bridge below says that this
check is a check *of the state's matrix*: it is the identity

    qformRows (toRows (n, X)) v = qf (MatQ.toMatrix n X) (fun i => v.getD i 0)      (n <= X.length,
                                                                                    v.length = n)

between the program's row-code form and `SepOracle.qf`, which the library did not have
(`Check_schur_bridge` bridges `Code`/`toMat`, not `toRows`/`MatQ.toMatrix`).  With it, a cut carries
`qf < 0` *at the state* — certifying `RelaxOracle.RelaxCut`'s violated direction — with no grid
error, no oracle agreement and no descent soundness needed.  This is what the pivot program should
emit: the descent proposes `v`, the state disposes.
-/

theorem list_sum_range_map {α : Type} [AddCommMonoid α] (g : ℕ → α) :
    ∀ n : ℕ, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | (n + 1) => by
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
      have hmap : List.map g (List.map Nat.succ (List.range n))
          = (List.range n).map (fun i => g (i + 1)) := by
        rw [List.map_map]; rfl
      rw [hmap, list_sum_range_map (fun i => g (i + 1)) n, Finset.sum_range_succ']
      exact add_comm _ _

theorem zip_map_eq_range_map {α β γ : Type} (g : α → β → γ) (dα : α) (dβ : β)
    (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length) :
    (l₁.zip l₂).map (fun p => g p.1 p.2)
      = (List.range l₁.length).map (fun i => g (l₁.getD i dα) (l₂.getD i dβ)) := by
  induction l₁ generalizing l₂ with
  | nil =>
      have h2 : l₂ = [] := List.eq_nil_of_length_eq_zero h.symm
      subst h2
      rfl
  | cons x xs ih =>
      match l₂, h with
      | [], h => simp at h
      | y :: ys, h =>
          have h' : xs.length = ys.length := by simpa using h
          rw [List.zip_cons_cons, List.map_cons, List.length_cons, List.range_succ_eq_map,
            List.map_cons, ih ys h']
          simp [List.getD_cons_zero, List.getD_cons_succ]

theorem dotL_eq_sum {n : ℕ} {x y : List ℚ} (hx : x.length = n) (hy : y.length = n) :
    dotL x y = ∑ j : Fin n, x.getD j.1 0 * y.getD j.1 0 := by
  have h1 : dotL x y = ((List.range x.length).map (fun i => x.getD i 0 * y.getD i 0)).sum := by
    unfold dotL
    rw [zip_map_eq_range_map (fun a b => a * b) (0 : ℚ) (0 : ℚ) x y (by rw [hx, hy])]
  rw [h1, list_sum_range_map, hx]
  exact (Fin.sum_univ_eq_sum_range (fun i => x.getD i 0 * y.getD i 0) n).symm

theorem qformRows_eq_sum {n : ℕ} {rows : Rows} {b : List ℚ} (hr : rows.length = n)
    (hb : b.length = n) :
    qformRows rows b = ∑ i : Fin n, b.getD i.1 0 * dotL (rows.getD i.1 []) b := by
  have h1 : qformRows rows b
      = ((List.range rows.length).map
          (fun i => b.getD i 0 * dotL (rows.getD i []) b)).sum := by
    unfold qformRows
    rw [zip_map_eq_range_map (fun a c => c * dotL a b) ([] : List ℚ) (0 : ℚ) rows b
      (by rw [hr, hb])]
  rw [h1, list_sum_range_map, hr]
  exact (Fin.sum_univ_eq_sum_range (fun i => b.getD i 0 * dotL (rows.getD i []) b) n).symm


/-- `SepOracle.qf` as a double sum. -/
theorem qf_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf M w = ∑ i : Fin n, w i * ∑ j : Fin n, M i j * w j := by
  simp [QMCLeafB.SepOracle.qf, dotProduct, Matrix.mulVec]

theorem idxs_eq_range {n : ℕ} {X : List ℚ} (hX : n ≤ X.length) :
    idxs (n, X) = List.range n := by
  unfold idxs
  rw [List.length_take, Nat.min_eq_left hX]

theorem getD_map_getD {α β : Type} (f : α → β) (l : List α) (dβ : β) (dα : α) {i : ℕ}
    (h : i < l.length) : (l.map f).getD i dβ = f (l.getD i dα) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
  congr 1
  exact (List.getD_eq_getElem _ _ h).symm

theorem getD_range {n : ℕ} (d : ℕ) {i : ℕ} (h : i < n) : (List.range n).getD i d = i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  exact List.getElem_range _

theorem rowOf_length {n : ℕ} {X : List ℚ} (hX : n ≤ X.length) (i : ℕ) :
    (rowOf (n, X) i).length = n := by
  show ((idxs (n, X)).map (fun k => entV (n, X) i k)).length = n
  rw [List.length_map, idxs_eq_range hX, List.length_range]

theorem toRows_length {n : ℕ} {X : List ℚ} (hX : n ≤ X.length) :
    (toRows (n, X)).length = n := by
  show ((idxs (n, X)).map (rowOf (n, X))).length = n
  rw [List.length_map, idxs_eq_range hX, List.length_range]

theorem toRows_getD_row {n : ℕ} {X : List ℚ} (hX : n ≤ X.length) (i : Fin n) :
    (toRows (n, X)).getD i.1 [] = rowOf (n, X) i.1 := by
  show ((idxs (n, X)).map (rowOf (n, X))).getD i.1 [] = rowOf (n, X) i.1
  rw [idxs_eq_range hX]
  rw [getD_map_getD (rowOf (n, X)) (List.range n) [] 0 (by simpa using i.2),
    getD_range 0 i.2]

theorem rowOf_getD {n : ℕ} {X : List ℚ} (hX : n ≤ X.length) (i : ℕ) (j : Fin n) :
    (rowOf (n, X) i).getD j.1 0 = entV (n, X) i j.1 := by
  show ((idxs (n, X)).map (fun k => entV (n, X) i k)).getD j.1 0 = entV (n, X) i j.1
  rw [idxs_eq_range hX]
  rw [getD_map_getD (fun k => entV (n, X) i k) (List.range n) 0 0 (by simpa using j.2),
    getD_range 0 j.2]

theorem qformRows_toRows_eq_qf {n : ℕ} {X v : List ℚ} (hX : n ≤ X.length) (hv : v.length = n) :
    qformRows (toRows (n, X)) v
      = QMCLeafB.SepOracle.qf (MatQ.toMatrix n X) (fun i : Fin n => v.getD i.1 0) := by
  have hlen : (toRows (n, X)).length = n := toRows_length hX
  rw [qformRows_eq_sum hlen hv, qf_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [toRows_getD_row hX i, dotL_eq_sum (rowOf_length hX i.1) hv]
  refine congrArg _ (Finset.sum_congr rfl (fun j _ => ?_))
  rw [rowOf_getD hX i.1 j]
  rfl



/-- **The certified cut**: a candidate direction that passes the *exact* check on the state's own
code is a genuinely violated direction of the state's matrix.  This is the sound replacement for
brick 1's clause B, at every `n`, with no grid hypothesis. -/
theorem certified_cut {s : RSt} {v : List ℚ} (hX : stN s ≤ (stX s).length)
    (hv : v.length = stN s)
    (h : qformRows (toRows (stN s, stX s)) v < 0) :
    ∃ w : Fin (stN s) → ℚ,
      QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) w < 0 :=
  ⟨fun i => v.getD i.1 0, by
    rw [← qformRows_toRows_eq_qf hX hv]
    exact h⟩

/-- **The check is a `Poly` program** in the state, for each fixed candidate direction. -/
theorem poly_certCheck (v : List ℚ) :
    OAI.MetricKMedian.Binary.Automatic.Poly
      (fun s : RSt => qformRows (toRows (stN s, stX s)) v) :=
  OAI.MetricKMedian.Binary.Automatic.Poly.comp
    (f := fun p : Rows × List ℚ => qformRows p.1 p.2)
    (g := fun s : RSt => (toRows (stN s, stX s), v))
    poly_qformRows
    (OAI.MetricKMedian.Binary.Automatic.Poly.pair
      (f := fun s : RSt => toRows (stN s, stX s)) (g := fun _ : RSt => v)
      poly_toRowsR (OAI.MetricKMedian.Binary.Automatic.Poly.const v))

/-- **The descent's own witness, when it passes the check, is a certificate**: the composed pivot
lane `cut iff the emitted direction is exactly violated` is sound. -/
theorem certified_cut_of_pivAns {s : RSt} (hX : stN s ≤ (stX s).length)
    (hv : ((pivAns s).2).length = stN s)
    (h : qformRows (toRows (stN s, stX s)) (pivAns s).2 < 0) :
    ∃ w : Fin (stN s) → ℚ,
      QMCLeafB.SepOracle.qf (MatQ.toMatrix (stN s) (stX s)) w < 0 :=
  certified_cut hX hv h

end QMCLeafB.PivSpecM3

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.PivSpecM3.gOf_two
#print axioms QMCLeafB.PivSpecM3.gOf_three
#print axioms QMCLeafB.PivSpecM3.sGridA_grid
#print axioms QMCLeafB.PivSpecM3.sGridA_pivAns
#print axioms QMCLeafB.PivSpecM3.qf_sA_vA
#print axioms QMCLeafB.PivSpecM3.sumsq_vA
#print axioms QMCLeafB.PivSpecM3.clauseA_fails
#print axioms QMCLeafB.PivSpecM3.clauseA_fails_at_campaign_dq
#print axioms QMCLeafB.PivSpecM3.clauseA_no_psd
#print axioms QMCLeafB.PivSpecM3.toRows_three
#print axioms QMCLeafB.PivSpecM3.Xc_rows
#print axioms QMCLeafB.PivSpecM3.qf_Xc
#print axioms QMCLeafB.PivSpecM3.psd_Xc
#print axioms QMCLeafB.PivSpecM3.pivStepL_c1
#print axioms QMCLeafB.PivSpecM3.pivStepL_c2
#print axioms QMCLeafB.PivSpecM3.runPivL_c
#print axioms QMCLeafB.PivSpecM3.sB_grid
#print axioms QMCLeafB.PivSpecM3.sB_pivAns
#print axioms QMCLeafB.PivSpecM3.clauseB_fails
#print axioms QMCLeafB.PivSpecM3.clauseB_no_witness
#print axioms QMCLeafB.PivSpecM3.not_clauseA
#print axioms QMCLeafB.PivSpecM3.not_clauseB
#print axioms QMCLeafB.PivSpecM3.sZ_pivAns
#print axioms QMCLeafB.PivSpecM3.sZ_psd
#print axioms QMCLeafB.PivSpecM3.ok_branch_inhabited
#print axioms QMCLeafB.PivSpecM3.schur_height_exponential
#print axioms QMCLeafB.PivSpecM3.no_linear_height_profile
#print axioms QMCLeafB.PivSpecM3.list_sum_range_map
#print axioms QMCLeafB.PivSpecM3.zip_map_eq_range_map
#print axioms QMCLeafB.PivSpecM3.dotL_eq_sum
#print axioms QMCLeafB.PivSpecM3.qformRows_eq_sum
#print axioms QMCLeafB.PivSpecM3.qf_eq_sum
#print axioms QMCLeafB.PivSpecM3.qformRows_toRows_eq_qf
#print axioms QMCLeafB.PivSpecM3.certified_cut
#print axioms QMCLeafB.PivSpecM3.poly_certCheck
#print axioms QMCLeafB.PivSpecM3.certified_cut_of_pivAns

/-! ### Pointer audit for the shelf facts quoted above -/

#check @QMCLeafB.PivotProgram.poly_runPiv
#check @QMCLeafB.RoundProgram.poly_runPivL
#check @QMCLeafB.PivotProgram.poly_qformRows
#check @QMCLeafB.RunInduction.runPiv_psd
#check @QMCLeafB.RunInduction.runPiv_cut


