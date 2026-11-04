-- Prove2me | Definitions.Def_QMCLeafB_contract_m7
-- name    : QMCLeafB_contract_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:02:26.17119+00:00
-- url     : https://prove2.me/theorems/f896a973-8c56-45b8-a3af-51013d87a20a
-- title:
--   QMCLeafB contract_m7
-- statement:
--   # leaf B phase 19 — brick `contract-audit` (swarm `smw1k12jb`, member m7, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_closingAssembly_m3
import Definitions.Def_QMCLeafB_pivsnap
/-
# leaf B phase 19 — brick `contract-audit` (swarm `smw1k12jb`, member m7, direction d3)

The phase-19 task list hands the swarm two bricks (`snapped-pivot-spec`, `record-streams`) whose
job is to *supply* the residual

    `QMCLeafB.ClosingAssembly.Resid o Pfam`   -- one `Bundle` per interior `(G, t)`,

with `Bundle.hokAll` forcing **every round of the loop to be a cut round**.  This file is the
contract audit of that residual and of the snapped pivot test, and it reports two defects, both
machine-checked here, one of which is fatal to the residual as stated.

## 1.  The residual `Resid` is **unsatisfiable** at both wired parameter families

`Bundle` + `ClosingAssembly.runParts_of_bundle` produce a `FinalStroke.RunParts` whose flag stream is
all-`false`.  The refuted-branch soundness theorem `SimLoop.simulate_refuted_sound` then concludes

    `∀ Z, IsUnitDiagPSD Z → (t : ℝ) - εr ≤ tr (wMatrix G · Z)`,

i.e. **the relaxed body `{Z unit-diag PSD : tr (wMatrix G · Z) ≤ t - εr}` is empty**.  This file
proves that consequence *for an arbitrary witness* (`no_runParts_allFalse_of_body`): an all-`false`
run is impossible as soon as the relaxed body has **one** point strictly below the threshold.  At `(Gtwo, -1/2)` — the two-vertex
input of total weight `1/2`, `Rq = 1`, so the interior bracket is `-1 ≤ t < -1/40000` — the witness
`!![1, -1; -1, 1]` is unit-diagonal PSD with `tr (wMatrix Gtwo · Z) = -1 ≤ -1/2 - 1/40000`.  Hence

* `no_bundle_at`: there is **no** `Bundle` at `(Gtwo, -1/2)`, whatever the flag stream, hence
* `resid_kbc2_empty`  : `¬ Nonempty (Resid o UnionShallow.paramsKbc2)`   (the `round` stroke of phase 18), and
* `resid_shallow_empty`: `¬ Nonempty (Resid o LoopClose.paramsShallow)`   (the `roundGT` stroke).

So `ClosingAssembly.solution` / `solution_guardT` (and any assembler fed by `Resid`) remain true
implications with an **unsatisfiable hypothesis**: they do not close the leaf.  The repair is not to
*eliminate* the `ok`-round slot `hmem` but to *supply* it — the flag stream of the campaign's engine
is necessarily mixed, which is exactly the split `RunParts`/`RunData` already carries.

## 2.  The snapped pivot test certifies a PSD margin only above `4/(13·d)`

Brick 1 asks for `pivAns s = false ⇒ ∀ x, -(dq/2)·‖x‖² ≤ qf (stMat s) x`.  `Check_pivsnap_m1`
already shows the exact-PSD form of that clause is false at the campaign's own grid
(`d = gridOf 2 = 81`, `mu = 8`): the snapped descent truncates the Schur complement `-1/162` to `0`.
This file sharpens the refutation to the **margined** clause the `ok` branch actually needs:

* `tolerance_floor`: any `δ` that certifies the clause on `M` with a witness `v` (`qf M v = -η`)
  must satisfy `2η/‖v‖² ≤ δ` — the general mechanism, nothing about snapping in it;
* `not_pivPsdMargin_sGrid`: at `PivSnapM1.sGrid` (`d = 81`, `mu = 8`) the clause fails for every
  `δ < 4/1053  (= 2·(2/81)/13)`;
* `pivFSpec_false_campaign`: since `dqShallow G < 1/360000 < 4/1053` at every `Rq G > 0`, the
  snapped pivot test **cannot** certify the `ok`-branch `RelaxMem.psd_margin` at the campaign's
  tolerance — at the campaign's present grid.

Two corrections to the task text, both machine-checked here:

* `GridBudget.exists_grid_budget` (`Check_gridbudget_m6`) is **not** a pivot-grid statement: it
  concerns the reciprocal-sqrt bracket `invSqrtGe - invSqrtLe` of the *drift* budget, and says
  nothing about `nrmQ mu d`.  It cannot supply the pivot grid.
* `dqShallow` is smaller than `4/(13·d)` for every campaign grid `d = gridOf n` with `n` small:
  the snapped test is *coarse* relative to the campaign tolerance, so the pivot grid has to be
  re-chosen as a function of `dq` (a poly-sized `d ≳ n/dq`), not by `gridOf`.

Nothing here claims the leaf.  No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`;
`set_option autoImplicit false`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ContractM7

open QuantumMaxCutEnergy

/-! ## 0.  The two-vertex input, and the witness inside its relaxed body -/

/-- **`Gtwo`**: two vertices, the single edge of weight `1/2`, so `Rq Gtwo = 1`.  (`abbrev`, so that
`Fin Gtwo.n` is reducibly `Fin 2`.) -/
abbrev Gtwo : QuantumMaxCutEnergy.Input :=
  ⟨2, fun _ => (1 / 2 : ℚ≥0)⟩

theorem Gtwo_n : Gtwo.n = 2 := rfl

theorem Gtwo_hn : 2 ≤ Gtwo.n := by
  show 2 ≤ 2
  omega

/-- The edge set of two vertices is a singleton. -/
theorem univ_edge_two : (Finset.univ : Finset (Edge 2)) = {⟨(0, 1), by decide⟩} := by
  ext e
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  obtain ⟨⟨i, j⟩, h⟩ := e
  have hij : (i : ℕ) < (j : ℕ) := h
  have hi : (i : ℕ) < 2 := i.isLt
  have hj : (j : ℕ) < 2 := j.isLt
  refine Subtype.ext ?_
  show ((i, j) : Fin 2 × Fin 2) = ((0 : Fin 2), (1 : Fin 2))
  rw [Prod.mk.injEq]
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- **`Rq Gtwo = 1`**, so the interior bracket at `Gtwo` is `-1 ≤ t < -1/40000`. -/
theorem Rq_Gtwo : QMCLeafB.EngineRuntime.Rq Gtwo = 1 := by
  unfold QMCLeafB.EngineRuntime.Rq
  show 2 * (∑ e : Edge Gtwo.n, ((Gtwo.weights e : ℚ≥0) : ℚ)) = 1
  rw [univ_edge_two, Finset.sum_singleton]
  norm_num

/-- The witness `!![1, -1; -1, 1]`: unit diagonal, PSD, rank one. -/
def Ztwo : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

theorem Ztwo_unitDiagPSD : QMCLeafB.AnswerProducer.IsUnitDiagPSD Ztwo := by
  refine ⟨?_, fun i => ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Ztwo]
    · intro x
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Ztwo,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.of_apply, Matrix.empty_val', star_trivial]
      nlinarith [sq_nonneg (x 0 - x 1)]
  · fin_cases i <;> simp [Ztwo]

/-- **`tr (wMatrix Gtwo · Ztwo) = -1`** — the body point sits far below the interior threshold. -/
theorem trace_Gtwo_Ztwo : (QMCLeafB.wMatrix Gtwo * Ztwo).trace = -1 := by
  have e00 : QMCLeafB.wMatrix Gtwo (0 : Fin Gtwo.n) (0 : Fin Gtwo.n) = 0 :=
    QMCLeafB.wMatrix_apply_of_eq
  have e11 : QMCLeafB.wMatrix Gtwo (1 : Fin Gtwo.n) (1 : Fin Gtwo.n) = 0 :=
    QMCLeafB.wMatrix_apply_of_eq
  have e01 : QMCLeafB.wMatrix Gtwo (0 : Fin Gtwo.n) (1 : Fin Gtwo.n) = 1 / 2 := by
    unfold QMCLeafB.wMatrix
    norm_num [Gtwo]
  have e10 : QMCLeafB.wMatrix Gtwo (1 : Fin Gtwo.n) (0 : Fin Gtwo.n) = 1 / 2 := by
    unfold QMCLeafB.wMatrix
    norm_num [Gtwo]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, e00, e01, e10, e11,
    Ztwo]
  norm_num

/-! ## 1.  An all-`false` flag stream is impossible above a nonempty relaxed body

This is the *general* form of phase-19's `resid-refute`: not a statement about one threshold point,
but the mechanism — the refuted branch concludes `body = ∅`, so any point of the body kills it. -/

theorem anyOk_all_false (ok : ℕ → Bool) :
    ∀ N : ℕ, (∀ k, k < N → ok k = false) → QMCLeafB.SimLoop.anyOk ok N = false
  | 0, _ => rfl
  | (k + 1), h => by
      rw [QMCLeafB.SimLoop.anyOk_succ, h k (Nat.lt_succ_self k),
        anyOk_all_false ok k (fun j hj => h j (Nat.lt_succ_of_lt hj))]
      rfl

/-- **No all-`false` run above a nonempty relaxed body.**

If `Z` is a unit-diagonal PSD point with `tr (wMatrix G · Z) ≤ t - Rq G/40000`, then there is no
`RunParts o G t P` whose flag stream is all-`false`: the run's own refuted-branch soundness proves
the opposite inequality at `Z`.  (`hok` is exactly `ClosingAssembly.Bundle.hokAll`.) -/
theorem no_runParts_allFalse_of_body {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (P : QMCLeafB.FinalStroke.RunParams G) (R : QMCLeafB.FinalStroke.RunParts o G t P)
    (hn : 2 ≤ G.n)
    (hok : ∀ k, k < P.K * P.m → R.ok k = false)
    {Z : Matrix (Fin G.n) (Fin G.n) ℝ} (hZ : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z)
    (htr : (QMCLeafB.wMatrix G * Z).trace
        < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) : False := by
  set Rd := R.toRunData with hRd
  have hKm : Rd.K * Rd.m = P.K * P.m := rfl
  have hv : QMCLeafB.SimLoop.anyOk Rd.ok (Rd.K * Rd.m) = false := by
    rw [hKm]
    exact anyOk_all_false Rd.ok (P.K * P.m) (fun k hk => hok k hk)
  have hsound := QMCLeafB.SimLoop.simulate_refuted_sound (n := G.n) hn
    (QMCLeafB.wMatrix G) t (QMCLeafB.EngineRuntime.Rq G / 40000) Rd.dq Rd.cAq
    Rd.hdq Rd.hcAq Rd.hAsum Rd.ok Rd.cd Rd.hwit Rd.hrho Rd.hcne Rd.hdel0 Rd.hcheck
    Rd.hcut Rd.hrmax Rd.hle Rd.hhalve Rd.hbudget hv
  exact absurd (hsound Z hZ) (not_le.mpr htr)

#print axioms QMCLeafB.ContractM7.no_runParts_allFalse_of_body

/-- **No `Bundle` at `(Gtwo, -1/2)`** — `Bundle`'s flag stream forces a `RunParts` with an
all-`false` stream, and the body point `Ztwo` kills every such run.  This is the residual's own
shape, so this is the fatal statement. -/
theorem no_bundle_at (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : QMCLeafB.FinalStroke.RunParams Gtwo) (hn : 2 ≤ Gtwo.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ Gtwo) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps Gtwo ≤ QMCLeafB.RundataCert.eps Gtwo)
    (B : QMCLeafB.ClosingAssembly.Bundle o Gtwo (-(1 / 2)) P hn) : False := by
  refine no_runParts_allFalse_of_body P
    (QMCLeafB.ClosingAssembly.runParts_of_bundle o Gtwo (-(1 / 2)) P hn
      hrmaxPos hrmax1 hbudP B) hn B.hokAll Ztwo_unitDiagPSD ?_
  rw [trace_Gtwo_Ztwo, Rq_Gtwo]
  norm_num

#print axioms QMCLeafB.ContractM7.no_bundle_at

/-! ### 1a.  The bracket at `(Gtwo, -1/2)`, and `Rq Gtwo > 0` -/

theorem Rq_Gtwo_pos : 0 < QMCLeafB.EngineRuntime.Rq Gtwo := by
  rw [Rq_Gtwo]; norm_num

theorem Gtwo_bracket_lo : -QMCLeafB.EngineRuntime.Rq Gtwo ≤ -(1 / 2) := by
  rw [Rq_Gtwo]; norm_num

theorem Gtwo_bracket_hi :
    ((-(1 / 2) : ℚ) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq Gtwo / 40000 : ℚ)) : ℝ) := by
  rw [Rq_Gtwo]; norm_num

/-- **The residual is empty at the `round` stroke of phase 18.**  (`Resid` is a `Type` — the data of
the bundles — so emptiness is stated with `Nonempty`.) -/
theorem resid_kbc2_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ClosingAssembly.Resid o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨h⟩
  have hn : 2 ≤ Gtwo.n := Gtwo_hn
  have hbud := QMCLeafB.ClosingAssembly.budget_dqShallow Gtwo hn Rq_Gtwo_pos
  have hb := h Gtwo (-(1 / 2)) hn Gtwo_bracket_lo Gtwo_bracket_hi
  exact no_bundle_at o (QMCLeafB.UnionShallow.paramsKbc2 Gtwo) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos Gtwo hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one Gtwo hn) hbud hb

#print axioms QMCLeafB.ContractM7.resid_kbc2_empty

/-- **The residual is empty at the `roundGT` stroke of phase 18 as well.**  So the choice between
`round` and `roundGT` — which phase 18 wired twice precisely because it was not on the critical path
— does not help: both strokes consume the same unsatisfiable `Resid`. -/
theorem resid_shallow_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ClosingAssembly.Resid o QMCLeafB.LoopClose.paramsShallow) := by
  rintro ⟨h⟩
  have hn : 2 ≤ Gtwo.n := Gtwo_hn
  have hbud := QMCLeafB.ClosingAssembly.budget_dqShallow Gtwo hn Rq_Gtwo_pos
  have hb := h Gtwo (-(1 / 2)) hn Gtwo_bracket_lo Gtwo_bracket_hi
  exact no_bundle_at o (QMCLeafB.LoopClose.paramsShallow Gtwo) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos Gtwo hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one Gtwo hn) hbud hb

#print axioms QMCLeafB.ContractM7.resid_shallow_empty

/-! ## 2.  The snapped pivot test's tolerance floor: `4/(13·d)`

Brick 1 wants `pivAns s = false ⇒` the `-dq/2`-margined PSD clause at the state.  §2a records the
general mechanism (any certifier pays `2η/‖v‖²` for a witness of size `η`), §2b the campaign grid
instance, §2c the campaign tolerance instantiation. -/

/-- The PSD-margin clause of brick 1 at a state, at tolerance `δ` (the `RelaxMem.psd_margin` form). -/
def PivPsdMargin (s : QMCLeafB.RoundProgram.RSt) (δ : ℚ) : Prop :=
  ∀ x : Fin (QMCLeafB.RoundProgram.stN s) → ℚ,
    -(δ / 2) * (∑ i, x i ^ 2)
      ≤ QMCLeafB.SepOracle.qf
          (MatQ.toMatrix (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stX s)) x

/-- Brick 1's first clause, stated program-wide. -/
def PivFSpec (δ : ℚ) : Prop :=
  ∀ s : QMCLeafB.RoundProgram.RSt,
    (QMCLeafB.RoundProgram.pivAns s).1 = false → PivPsdMargin s δ

/-- **§2a.  The tolerance floor.**  A matrix with `qf M v = -η` at a witness of norm squared `N`
cannot satisfy the `-δ/2`-margined PSD clause for any `δ < 2η/N`.  Nothing here mentions snapping:
this is the price *any* certifier of the margin pays at a violating witness. -/
theorem tolerance_floor {k : ℕ} {M : Matrix (Fin k) (Fin k) ℚ} {v : Fin k → ℚ}
    {δ η N : ℚ} (hη : QMCLeafB.SepOracle.qf M v = -η)
    (hN : (∑ i, v i ^ 2) = N) (hNpos : 0 < N)
    (h : ∀ x : Fin k → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf M x) :
    2 * η / N ≤ δ := by
  have h0 := h v
  rw [hη, hN] at h0
  rw [div_le_iff₀ hNpos]
  nlinarith

#print axioms QMCLeafB.ContractM7.tolerance_floor

/-- §2b.  The witness `(3, -2)` of `PivSnapM1`'s grid state has norm squared `13`. -/
theorem sum_sq_witness : (∑ i : Fin 2, (if i = 0 then (3 : ℚ) else -2) ^ 2) = 13 := by
  rw [Fin.sum_univ_two]
  norm_num

/-- The `qf` value at the grid state's witness, in the index type of the *state* (where `0` is the
natural-number comparison, `Fin (stN s)` carrying no `OfNat` instance). -/
theorem qf_Xgrid_nat :
    QMCLeafB.SepOracle.qf (MatQ.toMatrix 2 QMCLeafB.PivSnapM1.Xgrid)
      (fun i : Fin 2 => if (i : ℕ) = 0 then (3 : ℚ) else -2) = -2 / 81 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, QMCLeafB.PivSnapM1.Xgrid_toMatrix]
  simp [Fin.sum_univ_two]
  norm_num

#print axioms QMCLeafB.ContractM7.qf_Xgrid_nat

/-- **§2b.  The margined clause fails at the campaign grid state.**

`PivSnapM1.sGrid` is the state `n = 2`, `mu = 8`, `d = gridOf 2 = 81` whose code is `PivSnapM1.Xgrid`
— every entry on the campaign's own `(1/81)ℤ`.  Its snapped descent answers `false`
(`PivSnapM1.sGrid_pivAns`), and the clause with any `δ < 4/1053` is false there
(`qf Xgrid (3,-2) = -2/81` at a witness of norm squared `13`). -/
theorem not_pivPsdMargin_sGrid {δ : ℚ} (h : δ < 4 / 1053) :
    ¬ PivPsdMargin QMCLeafB.PivSnapM1.sGrid δ := by
  intro hm
  have hN : QMCLeafB.RoundProgram.stN QMCLeafB.PivSnapM1.sGrid = 2 := rfl
  have h0 := hm (fun i : Fin (QMCLeafB.RoundProgram.stN QMCLeafB.PivSnapM1.sGrid) =>
    if (i : ℕ) = 0 then (3 : ℚ) else -2)
  have hs : (∑ i : Fin (QMCLeafB.RoundProgram.stN QMCLeafB.PivSnapM1.sGrid),
      (if (i : ℕ) = 0 then (3 : ℚ) else -2) ^ 2) = 13 := by
    rw [hN]
    rw [Fin.sum_univ_two]
    norm_num
  have hq : QMCLeafB.SepOracle.qf
      (MatQ.toMatrix (QMCLeafB.RoundProgram.stN QMCLeafB.PivSnapM1.sGrid)
        (QMCLeafB.RoundProgram.stX QMCLeafB.PivSnapM1.sGrid))
      (fun i : Fin (QMCLeafB.RoundProgram.stN QMCLeafB.PivSnapM1.sGrid) =>
        if (i : ℕ) = 0 then (3 : ℚ) else -2) = -2 / 81 := by
    rw [QMCLeafB.PivSnapM1.sGrid_matrix]
    exact qf_Xgrid_nat
  rw [hs, hq] at h0
  linarith

#print axioms QMCLeafB.ContractM7.not_pivPsdMargin_sGrid

/-- **§2b.  So brick 1's first clause is false as a program statement** at every `δ < 4/1053`: the
counterexample state is a state of the same program (`pivAns`), on the campaign's grid and box. -/
theorem pivFSpec_false {δ : ℚ} (h : δ < 4 / 1053) : ¬ PivFSpec δ := by
  intro hf
  exact not_pivPsdMargin_sGrid h
    (hf QMCLeafB.PivSnapM1.sGrid QMCLeafB.PivSnapM1.sGrid_pivAns)

#print axioms QMCLeafB.ContractM7.pivFSpec_false

/-- **§2c.  The campaign tolerance is far below the floor.**  For every input of positive total
weight, `dqShallow G = (Rq/40000)/(9·Rq + 1) < 1/360000`, while the campaign's grid state asks for
`δ ≥ 4/1053`. -/
theorem dqShallow_lt_floor {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G < 4 / 1053 := by
  have hne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRq
  have hdef : QMCLeafB.RundataParams.dqShallow G
      = QMCLeafB.RundataCert.eps G / (9 * QMCLeafB.EngineRuntime.Rq G + 1) := by
    unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
    rw [if_neg hne]
  rw [hdef]
  have heps : QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl
  rw [heps]
  have h9 : 0 < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  have hden : 40000 * (9 * QMCLeafB.EngineRuntime.Rq G + 1)
      ≥ 40000 * (9 * QMCLeafB.EngineRuntime.Rq G) := by linarith
  have hpos : 0 < QMCLeafB.EngineRuntime.Rq G / 40000 / (9 * QMCLeafB.EngineRuntime.Rq G + 1) :=
    by positivity
  have hstep : QMCLeafB.EngineRuntime.Rq G / 40000 / (9 * QMCLeafB.EngineRuntime.Rq G + 1)
      ≤ (1 : ℚ) / 360000 := by
    rw [div_le_iff₀ h9]
    have h2 : QMCLeafB.EngineRuntime.Rq G / 40000 ≤ (1 / 360000) * (9 * QMCLeafB.EngineRuntime.Rq G) := by
      have : (1 / 360000 : ℚ) * (9 * QMCLeafB.EngineRuntime.Rq G)
          = QMCLeafB.EngineRuntime.Rq G / 40000 := by ring
      rw [this]
    nlinarith [h2, h9, hRq]
  have hnum : (1 : ℚ) / 360000 < 4 / 1053 := by norm_num
  linarith

#print axioms QMCLeafB.ContractM7.dqShallow_lt_floor

/-- **§2c.  Brick 1's first clause, at the campaign's tolerance — false.**

`pivAns`'s `false` answer does not certify the `dqShallow`-margined PSD clause at the campaign's
grid.  This is the sharp negative answer to phase 19's brick 1 in the form the task states it; the
clause is only recoverable after re-choosing the pivot grid (`d ≳ n/dq`), which is a *free* poly
parameter of `RoundProgram.RSt` but is fixed to `gridOf n = (n+1)^4` by `InitVerdict.gridOf`. -/
theorem pivFSpec_false_campaign (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    ¬ PivFSpec (QMCLeafB.RundataParams.dqShallow G) :=
  pivFSpec_false (dqShallow_lt_floor hRq)

#print axioms QMCLeafB.ContractM7.pivFSpec_false_campaign

/-! ## 3.  Non-vacuity of the two refutations

Neither refutation is an artefact of an empty quantifier: the interior bracket at `Gtwo` is
inhabited at `t = -1/2` (§1a), the body point `Ztwo` is exhibited, and the pivot counterexample state
carries the campaign's own grid and box with a `false` answer from its own descent. -/

/-- The bracket point used in §1 lies in the interior bracket, and the relaxed body is nonempty
there: `Ztwo` is unit-diagonal PSD of trace `-1 ≤ -1/2 - 1/40000`. -/
theorem interior_point_is_above_a_body_point :
    -QMCLeafB.EngineRuntime.Rq Gtwo ≤ -(1 / 2)
      ∧ ((-(1 / 2) : ℚ) : ℝ) < -(((QMCLeafB.EngineRuntime.Rq Gtwo / 40000 : ℚ)) : ℝ)
      ∧ QMCLeafB.AnswerProducer.IsUnitDiagPSD Ztwo
      ∧ (QMCLeafB.wMatrix Gtwo * Ztwo).trace
          ≤ ((-(1 / 2) : ℚ) : ℝ)
            - (((QMCLeafB.EngineRuntime.Rq Gtwo / 40000 : ℚ)) : ℝ) := by
  refine ⟨Gtwo_bracket_lo, Gtwo_bracket_hi, Ztwo_unitDiagPSD, ?_⟩
  rw [trace_Gtwo_Ztwo, Rq_Gtwo]
  norm_num

#print axioms QMCLeafB.ContractM7.interior_point_is_above_a_body_point

/-- **The `ok` slot is inhabited exactly where the all-`false` stream is impossible.**  At
`(Gtwo, -1/2)` the `RunParts.hcert` slot is satisfiable: `Ztwo` is a unit-diagonal PSD point of trace
`-1 ≤ t + Rq/40000`.  So the repair cannot be "make the flag stream all-`false`" (that is refuted by
`no_bundle_at`); it has to *supply* the `ok` round's certificate, and that slot is not empty. -/
theorem hcert_slot_inhabited :
    ∃ X : Matrix (Fin Gtwo.n) (Fin Gtwo.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix Gtwo * X).trace
          ≤ ((-(1 / 2) : ℚ) : ℝ)
            + (((QMCLeafB.EngineRuntime.Rq Gtwo / 40000 : ℚ)) : ℝ) := by
  refine ⟨Ztwo, Ztwo_unitDiagPSD, ?_⟩
  rw [trace_Gtwo_Ztwo, Rq_Gtwo]
  norm_num

#print axioms QMCLeafB.ContractM7.hcert_slot_inhabited

/-- The pivot counterexample state: the campaign grid `81`, the campaign box `8`, and the descent's
own `false` answer (restated here from `PivSnapM1` so the audit is readable on its own). -/
theorem sGrid_is_campaign_grid_state :
    QMCLeafB.RoundProgram.stD QMCLeafB.PivSnapM1.sGrid = 81
      ∧ QMCLeafB.RoundProgram.stMu QMCLeafB.PivSnapM1.sGrid = 8
      ∧ (QMCLeafB.RoundProgram.pivAns QMCLeafB.PivSnapM1.sGrid).1 = false :=
  ⟨rfl, rfl, QMCLeafB.PivSnapM1.sGrid_pivAns⟩

#print axioms QMCLeafB.ContractM7.sGrid_is_campaign_grid_state

end QMCLeafB.ContractM7

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.ContractM7.univ_edge_two
#print axioms QMCLeafB.ContractM7.Rq_Gtwo
#print axioms QMCLeafB.ContractM7.Ztwo_unitDiagPSD
#print axioms QMCLeafB.ContractM7.trace_Gtwo_Ztwo
#print axioms QMCLeafB.ContractM7.anyOk_all_false
#print axioms QMCLeafB.ContractM7.no_runParts_allFalse_of_body
#print axioms QMCLeafB.ContractM7.no_bundle_at
#print axioms QMCLeafB.ContractM7.resid_kbc2_empty
#print axioms QMCLeafB.ContractM7.resid_shallow_empty
#print axioms QMCLeafB.ContractM7.tolerance_floor
#print axioms QMCLeafB.ContractM7.sum_sq_witness
#print axioms QMCLeafB.ContractM7.not_pivPsdMargin_sGrid
#print axioms QMCLeafB.ContractM7.pivFSpec_false
#print axioms QMCLeafB.ContractM7.dqShallow_lt_floor
#print axioms QMCLeafB.ContractM7.pivFSpec_false_campaign
#print axioms QMCLeafB.ContractM7.interior_point_is_above_a_body_point
#print axioms QMCLeafB.ContractM7.sGrid_is_campaign_grid_state
#print axioms QMCLeafB.ContractM7.hcert_slot_inhabited


