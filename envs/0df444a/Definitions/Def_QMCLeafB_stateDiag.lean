-- Prove2me | Definitions.Def_QMCLeafB_stateDiag
-- name    : QMCLeafB_stateDiag
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:27:19.145685+00:00
-- url     : https://prove2.me/theorems/3648f17a-0fee-46ba-9427-c10449a497e1
-- title:
--   QMCLeafB stateDiag
-- statement:
--   # leaf B phase 18 — brick `state-diag` (swarm `smw1i2drp`, member m2, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_obstruction_m1
/-
# leaf B phase 18 — brick `state-diag` (swarm `smw1i2drp`, member m2, direction d3)

**The diagonal half of the per-round records, at the program's own state.**

`LoweredRecords` (`Check_lowerRecords_m2.lean`) asks, for every round `k`, for
`Q k =` the state's matrix, the three diagonal facts `hQsym`-companions `hunidiag`, `hdiag` and the
trace `htraceQ`.  Two of them are **not** orbit computations at all: they follow from the state's own
diagonal read-out.

* `dvR s = ∑ᵢ |Xᵢᵢ − 1|` (`RoundProgram.diagSumV`).  `dvR s = 0` is exactly `unitDiag` of the state's
  matrix (`stMat_diag_eq_one`) — a sum of non-negative rationals vanishing forces every term to
  vanish (`AuditM1.list_sum_zero_of_nonneg`).  This is the `dvR = 0` branch of `oracleV`/`oracleR`.
* Consequently `|(stMat s)ᵢᵢ − 1| ≤ dq/4` for every `dq ≥ 0` (`stMat_diag_abs_le`), i.e. the
  `RelaxMem.diag_near` clause at the state is free on the unit-diagonal branch;
* and `∑ᵢ (stMat s)ᵢᵢ ≤ n` (`stMat_trace_le`), i.e. the `htraceQ`/`htrc` slot at a unit-diagonal
  state is `n·1 = n`.
* `relaxMem_of_oracleV_ok_state` — `OkLower.relaxMem_of_oracleV_ok` with **three of its five
  hypotheses discharged**: `dvR = 0` (from the `ok` answer, `OkLower.oracleV_ok`) gives both the
  `diag_near` clause and unit-diagonality; only `fvR = frob A cX`, `0 < massV` and the PSD clause
  (the pivot test's half) are left.  `dq` is the state's own `dqOf`, which at the campaign state is
  `dqShallow` (`OkLower.dqOf_init0`).

Nothing here touches the pivot descent (`runPivL`), which is the remaining bridge for the `ok`
round's PSD clause; this file is the diagonal half only.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.StateDiag

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram

/-! ## 1.  The state's matrix, read off the row-major code -/

/-- **The state's matrix**: the `(i,j)` entry of the row-major code (`entV`).  `RowCode` of this
matrix against `toRows` is definitional (up to the `getD` plumbing), which is why the pivot answer can
be read as a statement about it. -/
def stMat (n : ℕ) (X : List ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => entV (n, X) i j

@[simp] theorem stMat_apply {n : ℕ} {X : List ℚ} (i j : Fin n) :
    stMat n X i j = X.getD (i.1 * n + j.1) 0 := rfl

/-- The index list is `range n` once the code is long enough. -/
theorem idxs_of_le {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) :
    idxs (n, X) = List.range n := by
  unfold QMCLeafB.RoundProgram.idxs
  simp only [List.length_take, Nat.min_eq_left hlen]

/-! ## 2.  `dvR = 0` is unit-diagonality -/

theorem list_sum_eq_zero_of_forall {l : List ℚ} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.sum_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      ring

theorem diagSumV_eq_zero_iff {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length) :
    diagSumV (n, X) = 0 ↔ ∀ i : Fin n, stMat n X i i = 1 := by
  constructor
  · intro h i
    have hsum : ((idxs (n, X)).map (fun k => absq (entV (n, X) k k - 1))).sum = 0 := h
    have hnn : ∀ x ∈ (idxs (n, X)).map (fun k => absq (entV (n, X) k k - 1)), 0 ≤ x := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      rw [QMCLeafB.RoundProgram.absq_eq]
      exact abs_nonneg _
    have hz := QMCLeafB.AuditM1.list_sum_zero_of_nonneg _ hnn hsum
    have hidx : i.1 ∈ idxs (n, X) := by
      rw [idxs_of_le hlen]
      exact List.mem_range.mpr i.2
    have hmem : absq (entV (n, X) i.1 i.1 - 1)
        ∈ (idxs (n, X)).map (fun k => absq (entV (n, X) k k - 1)) :=
      List.mem_map.mpr ⟨i.1, hidx, rfl⟩
    have h1 := hz _ hmem
    rw [QMCLeafB.RoundProgram.absq_eq, abs_eq_zero] at h1
    show entV (n, X) i.1 i.1 = 1
    linarith
  · intro h
    unfold QMCLeafB.RoundProgram.diagSumV
    have : ∀ k ∈ idxs (n, X), absq (entV (n, X) k k - 1) = 0 := by
      intro k hk
      rw [idxs_of_le hlen] at hk
      have hk' : k < n := List.mem_range.mp hk
      rw [QMCLeafB.RoundProgram.absq_eq, show entV (n, X) k k = stMat n X ⟨k, hk'⟩ ⟨k, hk'⟩ from rfl,
        h ⟨k, hk'⟩]
      simp
    refine list_sum_eq_zero_of_forall (fun x hx => ?_)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact this k hk

/-- **Unit diagonal at a zero diagonal read-out.** -/
theorem stMat_diag_eq_one {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length)
    (h : diagSumV (n, X) = 0) (i : Fin n) : stMat n X i i = 1 :=
  (diagSumV_eq_zero_iff hlen).mp h i

/-- **The `RelaxMem.diag_near` clause at the state** — free on the unit-diagonal branch. -/
theorem stMat_diag_abs_le {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length)
    (h : diagSumV (n, X) = 0) {dq : ℚ} (hdq : 0 ≤ dq) (i : Fin n) :
    |stMat n X i i - 1| ≤ dq / 4 := by
  rw [stMat_diag_eq_one hlen h i]
  simp only [sub_self, abs_zero]
  linarith

/-- **The trace slot at the state**: a unit-diagonal `n × n` state has trace `n`. -/
theorem stMat_trace_le {n : ℕ} {X : List ℚ} (hlen : n ≤ X.length)
    (h : diagSumV (n, X) = 0) : ∑ i, stMat n X i i ≤ (n : ℚ) := by
  have h1 : ∑ i, stMat n X i i = ∑ _i : Fin n, (1 : ℚ) :=
    Finset.sum_congr rfl (fun i _ => stMat_diag_eq_one hlen h i)
  rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## 3.  The `ok` branch at the state, with the diagonal slots discharged -/

/-- **`RelaxMem` at the state from an `ok` answer** — `OkLower.relaxMem_of_oracleV_ok` with the
`diag_near` clause and unit-diagonality supplied by `dvR = 0`, so only the PSD clause (the pivot
test) and the trace bridge `fvR = frob A cX` remain. -/
theorem relaxMem_of_oracleV_ok_state {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {s : RSt}
    (hN : stN s = n) (hlen : n ≤ (stX s).length)
    (hF : fvR s = QMCLeafB.SepOracle.frob A (stMat n (stX s)))
    (hok : (QMCLeafB.OkLower.oracleV s).1 = false) (hpos : 0 < QMCLeafB.RoundT.massV s)
    (hpsd : ∀ x : Fin n → ℚ,
      -(QMCLeafB.OkLower.dqOf s / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.SepOracle.qf (stMat n (stX s)) x) :
    QMCLeafB.RelaxOracle.RelaxMem A (stMat n (stX s))
      (stT s - QMCLeafB.RoundT.epsOf s) (QMCLeafB.OkLower.dqOf s) := by
  have hdv : dvR s = 0 := (QMCLeafB.OkLower.oracleV_ok s hok).1
  have hsum : diagSumV (n, (stX s)) = 0 := by
    rw [← hN]
    exact hdv
  have hdq0 : (0 : ℚ) ≤ QMCLeafB.OkLower.dqOf s := by
    unfold QMCLeafB.OkLower.dqOf
    have h1 : (0 : ℚ) < QMCLeafB.RoundT.epsOf s := by
      unfold QMCLeafB.RoundT.epsOf
      positivity
    have h2 : (0 : ℚ) < 9 * QMCLeafB.RoundT.massV s + 1 := by linarith
    positivity
  exact QMCLeafB.OkLower.relaxMem_of_oracleV_ok hF hok hpos hpsd
    (fun i => stMat_diag_abs_le hlen hsum hdq0 i)


/-! ## 4.  The trace bridge `fvR = frob A cX`: the coded bilinear form is the matrix one -/

theorem list_sum_map_range_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
        List.map_cons, List.sum_cons]
      simp

/-- **`frobV` is the matrix bilinear form at the state's matrix.**  This is the `hF` slot of
`OkLower.relaxMem_of_oracleV_ok`: the programme's own `fvR` is `frob` at `stMat`. -/
theorem frobV_eq_frob {n : ℕ} {A X : List ℚ} (hA : n ≤ A.length) (hX : n ≤ X.length) :
    frobV (n, (A, X)) = QMCLeafB.SepOracle.frob (stMat n A) (stMat n X) := by
  simp only [QMCLeafB.RoundProgram.frobV, idxs_of_le hX,
    QMCLeafB.SepOracle.frob, stMat_apply]
  rw [list_sum_map_range_eq]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ∑ j : Fin n, A.getD (i * n + (j : ℕ)) 0 * X.getD (i * n + (j : ℕ)) 0)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [list_sum_map_range_eq,
    Fin.sum_univ_eq_sum_range (fun j => A.getD (i * n + j) 0 * X.getD (i * n + j) 0)]

/-- **`fvR` at the state is `frob` there**, for a state whose weight code is `A`'s. -/
theorem fvR_eq_frob {n : ℕ} {s : RSt} (hN : stN s = n)
    (hA : n ≤ (stA s).length) (hX : n ≤ (stX s).length) :
    fvR s = QMCLeafB.SepOracle.frob (stMat n (stA s)) (stMat n (stX s)) := by
  show frobV (stN s, (stA s, stX s)) = _
  rw [hN]
  exact frobV_eq_frob hA hX

#print axioms QMCLeafB.StateDiag.frobV_eq_frob
#print axioms QMCLeafB.StateDiag.fvR_eq_frob

#print axioms QMCLeafB.StateDiag.stMat_diag_eq_one
#print axioms QMCLeafB.StateDiag.stMat_diag_abs_le
#print axioms QMCLeafB.StateDiag.stMat_trace_le
#print axioms QMCLeafB.StateDiag.relaxMem_of_oracleV_ok_state


