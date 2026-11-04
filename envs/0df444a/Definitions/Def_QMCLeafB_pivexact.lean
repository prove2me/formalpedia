-- Prove2me | Definitions.Def_QMCLeafB_pivexact
-- name    : QMCLeafB_pivexact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:44:24.546216+00:00
-- url     : https://prove2.me/theorems/644217a0-e33b-445d-9bd8-e4726b8984fe
-- title:
--   QMCLeafB pivexact
-- statement:
--   # leaf B phase 19 — brick `exact-pivot` (swarm `smw1k12jb`, member m8, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_run_induction_m1
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 19 — brick `exact-pivot` (swarm `smw1k12jb`, member m8, direction d9)

The phase-19 pivot brick (`d1`) is about `RoundProgram.pivAns`, i.e. the **snapped** descent
`runPivL`, whose Schur branch clips into a box and truncates onto a grid; `RunInduction.spec_runPiv`
is about the **exact** descent `PivotProgram.runPiv` and does not transfer to it (m1's
`Check_pivsnap_m1` exhibits `X = [[2,3],[3,4]]`, where `runPivL` answers `false` on an indefinite
block).  The `ok`-round certificate needs the opposite: from the state's own verdict *false*, the
state's block must be PSD up to the `RelaxMem.psd_margin` tolerance `-(dq/2)·‖x‖²`.

This file supplies that implication **for the exact descent on the state's own rows**, where it is
true with no grid-error hypothesis at all:

* §1 the row-major code of the state **is** a `RowCode` of the state's block
  (`rowCode_toRows`) — `RunInduction`'s side condition, previously only available for its hand-built
  examples (`bad2Rows`, …);
* §2 the exact descent's spec at the state: `false ⇒ PSD`, `true ⇒ ∃ v, qf v < 0`;
* §3 the `RelaxMem.psd_margin` clause — `∀ x, -(dq/2)·∑ xᵢ² ≤ qf (state block) x` for `0 ≤ dq` —
  i.e. exactly the `hpsd` slot of `StateDiag.relaxMem_of_oracleV_ok_state`
  (`Check_stateDiag_m2`), which is the `hmem` slot that `Check_residkill_m8` shows cannot be
  eliminated.

So the repair of the `ok` round is a program-level choice: run the descent on the state's rows
without the clip/snap (`runPiv` needs neither `mu` nor `d`), and the `ok` certificate's PSD half is
this file; keep `runPivL` and the PSD half must instead pay a grid error (the `d1` route).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.PivExact

open QuantumMaxCutEnergy

/-! ## 1.  The state's flat code is a `RowCode` of the state's block -/

/-- **The state's block**, read off the row-major code — the `StateDiag.stMat` of
`Check_stateDiag_m2`, repeated here so this brick depends only on the pivot modules. -/
abbrev matOf (n : ℕ) (X : List ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => QMCLeafB.RoundProgram.entV (n, X) i j

/-- The index list is `range n` once the code is long enough. -/
theorem idxs_eq {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) :
    QMCLeafB.RoundProgram.idxs (n, X) = List.range n := by
  unfold QMCLeafB.RoundProgram.idxs
  rw [List.length_take, Nat.min_eq_left hlen]

/-- **`getD` of a `map` over `range`.** -/
theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) {i n : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  have hlen : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem ((List.range n).map f) d hlen, List.getElem_map, List.getElem_range]

/-- `toRows` has exactly `n` rows. -/
theorem length_toRows {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) :
    (QMCLeafB.RoundProgram.toRows (n, X)).length = n := by
  simp only [QMCLeafB.RoundProgram.toRows, List.length_map, idxs_eq hlen, List.length_range]

/-- Row `i` of `toRows`, as a `getD`. -/
theorem getD_toRows {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) (i : Fin n) :
    (QMCLeafB.RoundProgram.toRows (n, X)).getD i.1 [] =
      QMCLeafB.RoundProgram.rowOf (n, X) i.1 := by
  simp only [QMCLeafB.RoundProgram.toRows, idxs_eq hlen]
  exact getD_map_range (QMCLeafB.RoundProgram.rowOf (n, X)) [] i.isLt

/-- Entry `j` of row `i` of `toRows` is the state's block entry. -/
theorem getD_rowOf {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) (i j : Fin n) :
    (QMCLeafB.RoundProgram.rowOf (n, X) i.1).getD j.1 0 = matOf n X i j := by
  simp only [QMCLeafB.RoundProgram.rowOf, idxs_eq hlen]
  exact getD_map_range (fun j => QMCLeafB.RoundProgram.entV (n, X) i.1 j) 0 j.isLt

/-- **The row-major code of the state is a `RowCode` of the state's block.**  This is the side
condition `RunInduction.spec_runPiv` asks for, at the state's own code. -/
theorem rowCode_toRows {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) :
    QMCLeafB.RunInduction.RowCode n (matOf n X) (QMCLeafB.RoundProgram.toRows (n, X)) := by
  refine ⟨length_toRows hlen, fun i => ?_, fun i j => ?_⟩
  · rw [getD_toRows hlen i]
    simp only [QMCLeafB.RoundProgram.rowOf, List.length_map, idxs_eq hlen, List.length_range]
  · rw [getD_toRows hlen i]
    exact getD_rowOf hlen i j

/-! ## 2.  The exact descent's spec at the state -/

/-- **The exact descent's spec at the state's block.** -/
theorem spec_at_state {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc}
    (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i) :
    QMCLeafB.RunInduction.Spec n (matOf n X)
      (QMCLeafB.PivotProgram.runPiv (QMCLeafB.RoundProgram.toRows (n, X), acc)) :=
  QMCLeafB.RunInduction.spec_runPiv (rowCode_toRows hlen) hsym

/-- **`false` at the state's block ⇒ the block is PSD** (no grid error, no clip). -/
theorem psd_of_false {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc}
    (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i)
    (h : (QMCLeafB.PivotProgram.runPiv (QMCLeafB.RoundProgram.toRows (n, X), acc)).1 = false) :
    QMCLeafB.SepOracle.PSD (matOf n X) :=
  (spec_at_state hlen hsym).1 h

/-- **`true` at the state's block ⇒ an explicit violated direction.** -/
theorem cut_of_true {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc}
    (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i)
    (h : (QMCLeafB.PivotProgram.runPiv (QMCLeafB.RoundProgram.toRows (n, X), acc)).1 = true) :
    ∃ v : Fin n → ℚ, QMCLeafB.SepOracle.qf (matOf n X) v < 0 :=
  (spec_at_state hlen hsym).2 h

/-! ## 2b.  Both branches of the state's oracle interface, at the exact descent

`RunInduction`'s consumer forms (`okReport_of_runPiv`, `goodCut_of_runPiv`, `response_of_runPiv`)
each begin with a `RowCode` side condition; §1 supplies it at the state, so the exact descent run on
the state's own rows **is** the separation oracle's response there — with no grid error, no clip and
no `mu`/`d`.  That is the cut-record half of the repaired residual as much as the `ok` half. -/

/-- **The `ok` branch at the state**: a PSD report from the descent's `false`. -/
def okReport_at_state {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc}
    {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i)
    (hdiag : QMCLeafB.SepOracle.unitDiag (matOf n X))
    (htr : t ≤ QMCLeafB.SepOracle.frob A (matOf n X))
    (h : (QMCLeafB.PivotProgram.runPiv (QMCLeafB.RoundProgram.toRows (n, X), acc)).1 = false) :
    QMCLeafB.SepOracle.OkReport n A t (matOf n X) :=
  QMCLeafB.RunInduction.okReport_of_runPiv (rowCode_toRows hlen) hsym hdiag htr h

/-- **The `cut` branch at the state**: a genuine separating cut from the descent's `true`. -/
noncomputable def goodCut_at_state {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc}
    {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i)
    (h : (QMCLeafB.PivotProgram.runPiv (QMCLeafB.RoundProgram.toRows (n, X), acc)).1 = true) :
    QMCLeafB.SepOracle.GoodCut A t (matOf n X) :=
  QMCLeafB.RunInduction.goodCut_of_runPiv (rowCode_toRows hlen) hsym h

/-- **The exact descent at the state is the separation oracle's `Response`.** -/
noncomputable def response_at_state {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc}
    {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i)
    (hdiag : QMCLeafB.SepOracle.unitDiag (matOf n X))
    (htr : t ≤ QMCLeafB.SepOracle.frob A (matOf n X)) :
    QMCLeafB.SepOracle.Response A t (matOf n X) :=
  QMCLeafB.RunInduction.response_of_runPiv (acc := acc) (rowCode_toRows hlen) hsym hdiag htr

/-! ## 3.  The `RelaxMem.psd_margin` clause — the `hpsd` slot of the `ok` branch -/

/-- **PSD implies the margin clause** `-(dq/2)·‖x‖² ≤ qf X x` for every `0 ≤ dq`. -/
theorem margin_of_psd {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ} (hdq : 0 ≤ dq)
    (hpsd : QMCLeafB.SepOracle.PSD M) :
    ∀ x : Fin n → ℚ, -(dq / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf M x := by
  intro x
  have hnn : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  have h1 : -(dq / 2) * (∑ i, x i ^ 2) ≤ 0 := by nlinarith
  linarith [hpsd x]

/-- **The `ok` round's PSD half, at the state, from the exact descent's `false` verdict** — this is
exactly the `hpsd` hypothesis of `QMCLeafB.StateDiag.relaxMem_of_oracleV_ok_state`. -/
theorem psd_margin_of_false {n : ℕ} {X : List ℚ} {acc : QMCLeafB.PivotProgram.Acc} {dq : ℚ}
    (hdq : 0 ≤ dq) (hlen : n ≤ X.length) (hsym : ∀ i j, matOf n X i j = matOf n X j i)
    (h : (QMCLeafB.PivotProgram.runPiv (QMCLeafB.RoundProgram.toRows (n, X), acc)).1 = false) :
    ∀ x : Fin n → ℚ, -(dq / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf (matOf n X) x :=
  margin_of_psd hdq (psd_of_false hlen hsym h)

end QMCLeafB.PivExact

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.PivExact.getD_map_range
#print axioms QMCLeafB.PivExact.idxs_eq
#print axioms QMCLeafB.PivExact.getD_toRows
#print axioms QMCLeafB.PivExact.getD_rowOf
#print axioms QMCLeafB.PivExact.rowCode_toRows
#print axioms QMCLeafB.PivExact.spec_at_state
#print axioms QMCLeafB.PivExact.psd_of_false
#print axioms QMCLeafB.PivExact.cut_of_true
#print axioms QMCLeafB.PivExact.okReport_at_state
#print axioms QMCLeafB.PivExact.goodCut_at_state
#print axioms QMCLeafB.PivExact.response_at_state
#print axioms QMCLeafB.PivExact.margin_of_psd
#print axioms QMCLeafB.PivExact.psd_margin_of_false


