-- Prove2me | Definitions.Def_QMCLeafB_centre_adm_m1
-- name    : QMCLeafB_centre_adm_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:17:46.0024+00:00
-- url     : https://prove2.me/theorems/39a9e186-ab50-4238-920d-1d705a6b7f3d
-- title:
--   QMCLeafB centre_adm_m1
-- statement:
--   # leaf B phase 18 — centre-admissibility ledger for residual (A) (swarm `smw1i2drp`, m1, d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_obstruction_m1
/-
# leaf B phase 18 — centre-admissibility ledger for residual (A) (swarm `smw1i2drp`, m1, d6)

The phase-18 residual list names the two centre constructions for the `RunParts` records:

* `ok` rounds: `QMCLeafB.OkLower.relaxMem_of_oracleV_ok` at the queried centre;
* cut rounds: `QMCLeafB.AuditM1.relaxMem_boundary_smul` at the boundary `(1 − dq/4) • Q`.

Both are consumed at the *same* `cX k` by the conduit (`QMCLeafB.DriftExact.runParts_at_interior_exact`),
which asks simultaneously for

    hmem : RelaxMem (wMatrixQ G) (cX k) (t − eps) dq      -- at `ok k = true`
    hTrc : ∑ i, (cX k) i i ≤ n (1 − dq/4)                 -- at every k

(plus `hCsym`, `hcEq`, `hcn/hcne`, `hlam0..2`, and the two drift inequalities).  This file decides
which centres can carry that pair.  Nothing here assumes the run: every statement is at an arbitrary
rational matrix.

* **§1 The pinch in the conduit's own shape.**  Phase 17 proved the pinch from the *entrywise* band
  `hdiagc`; the conduit actually supplies the *sum* `hTrc`.  The sum version is just as sharp: `hTrc`
  plus `RelaxMem.diag_near` force `(cX k) i i = 1 − dq/4` for every `i`, hence the trace is exactly
  `n(1 − dq/4)`.  So the conduit's own hypothesis already contains the pinch.
* **§2 The raw state never works.**  A unit-diagonal centre has `∑ i, Q i i = n > n(1 − dq/4)` for
  `dq > 0`: `hTrc` is false.  An `ok` round is queried at a `dvR = 0` state, whose diagonal is
  exactly `1` (`QMCLeafB.AuditM1.diagSumV_eq_zero`), so the ok round cannot use its own state as the
  centre.
* **§3 The correction: `(1 − dq/4) • Q` is admissible iff `Q` is unit-diagonal.**  For an arbitrary
  base `Q`, the prescribed cut-round centre satisfies `diag_near` *and* `hTrc` **iff** `Q` is
  unit-diagonal.  The `⇐` half is phase 17's `boundary_scale_admissible`; the `⇒` half is new and is
  the load-bearing one.  At a diagonal-repair cut (`dvR ≠ 0`, so `Q` is *not* unit-diagonal) the
  prescribed centre violates the pair — so the cut-round centre cannot be a uniform rescaling of the
  state at all.
* **§4 The forced replacement.**  The unique diagonal profile that works for *every* base is
  `diagPinch Q dq` = `Q` with its diagonal overwritten by `1 − dq/4`.  It satisfies `diag_near` and
  `hTrc` with equality for arbitrary `Q`; it leaves `frob A ·` untouched whenever `A` has zero
  diagonal (`wMatrixQ` does), so `trace_le` is inherited; and its exact PSD cost is
  `∑ i, (Q i i − (1 − dq/4)) x i ^ 2`.  For a unit-diagonal base that cost is `(dq/4)‖x‖²`, so the
  centre is admissible as soon as the base has PSD margin `dq/2`: the `dq/4` spent on the diagonal
  and the `dq/4` left over are the same budget.

* **§5–§6 The ok branch, composed.**  An `ok` answer forces `dvR = 0` (`oracleR_ok_dvR_zero`), so the
  state is unit-diagonal and its own centre is excluded (§2).  At the pinched surrogate the `RelaxMem`
  certificate follows from three facts about the state alone: unit diagonal, **exact** PSD, and the
  programme's own `ok` test (`relaxMem_diagPinch`, `ok_round_centre_admissible`).  Exact PSD is what
  `RunInduction.runPiv_psd` supplies from the pivot descent's `false` answer — no tolerance accounting
  is needed anywhere, contrary to the natural worry that the pivot tolerance must sit below `dq/4`.
* **§7–§8 The costs, and the side conditions.**  `mass_shift_diagPinch`: the all-ones drift direction
  moves by exactly `∑ i, Q i i − n(1 − dq/4)` under the overwrite (so `n·dq/4` at an `ok` round, and
  `0` at an already-pinched centre), while `frob` does not move at all.  `dqShallow_le_four` discharges
  the `dq ≤ 4` side condition at the campaign's family.

Net message for the endgame: the centre stream is **not** `(1 − dq/4) • Q` — it is `diagPinch` of the
state, at every round.  The two agree exactly at `dvR = 0` rounds, which is where the phase-18 list
prescribed the scaled one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QMCLeafB.CentreAdm

variable {n : ℕ}

/-! ## 1.  The pinch in the conduit's own shape: `hTrc` (a sum), not `hdiagc` -/

/-- **`hTrc` plus `RelaxMem.diag_near` force the diagonal onto the boundary entry by entry.**  The
phase-17 pinch (`QMCLeafB.AuditM1.pinch_of_mem`) needs the entrywise band `hdiagc`; the conduit only
supplies the sum `hTrc`, and that is enough. -/
theorem pinch_of_trace {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A Q u dq)
    (htrc : ∑ i, Q i i ≤ (n : ℚ) * (1 - dq / 4)) (i : Fin n) :
    Q i i = 1 - dq / 4 := by
  have hlo : ∀ j : Fin n, 1 - dq / 4 ≤ Q j j := by
    intro j
    have h := (abs_le.mp (hmem.diag_near j)).1
    linarith
  have hsum : ∑ _j : Fin n, (1 - dq / 4) = (n : ℚ) * (1 - dq / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ Q j j - (1 - dq / 4) := by
    intro j _
    linarith [hlo j]
  have ht : ∑ j, Q j j ≤ (n : ℚ) * (1 - dq / 4) := htrc
  have htotal : ∑ j, (Q j j - (1 - dq / 4)) ≤ 0 := by
    have hsub : ∑ j, (Q j j - (1 - dq / 4)) = (∑ j, Q j j) - (n : ℚ) * (1 - dq / 4) := by
      rw [Finset.sum_sub_distrib, hsum]
    rw [hsub]
    linarith
  have herase : (Q i i - (1 - dq / 4))
      + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, (Q j j - (1 - dq / 4))
      = ∑ j, (Q j j - (1 - dq / 4)) :=
    Finset.add_sum_erase Finset.univ (fun j => Q j j - (1 - dq / 4)) (Finset.mem_univ i)
  have hrest : 0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, (Q j j - (1 - dq / 4)) :=
    Finset.sum_nonneg (fun j _ => hnonneg j (Finset.mem_univ j))
  have hle : Q i i - (1 - dq / 4) ≤ 0 := by linarith
  linarith [hlo i]

/-- The pinched centre's trace: `hTrc` holds there *with equality*. -/
theorem trace_eq_of_pinch {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A Q u dq)
    (htrc : ∑ i, Q i i ≤ (n : ℚ) * (1 - dq / 4)) :
    ∑ i, Q i i = (n : ℚ) * (1 - dq / 4) := by
  have h1 : ∑ i, Q i i = ∑ _i : Fin n, (1 - dq / 4) :=
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => pinch_of_trace hmem htrc i)
  rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 2.  A unit-diagonal centre never satisfies `hTrc` -/

/-- **The raw state is excluded.**  `dvR = 0` states have unit diagonal
(`QMCLeafB.AuditM1.diagSumV_eq_zero`), and `hTrc` is then false for `dq > 0`. -/
theorem unit_diag_breaks_trace (hn : 0 < n) {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hdq : 0 < dq) (hQ : ∀ i, Q i i = 1) :
    ¬ (∑ i, Q i i ≤ (n : ℚ) * (1 - dq / 4)) := by
  intro h
  have h1 : ∑ i, Q i i = (n : ℚ) := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hQ i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  rw [h1] at h
  nlinarith [h, hn', hdq]

/-! ## 3.  The prescribed cut-round centre `(1 − dq/4) • Q` is admissible iff `Q` is unit-diagonal -/

/-- **The `⇒` half (new, and the load-bearing one).**  A uniform boundary rescaling of an arbitrary
base satisfies the conduit's `diag_near` + `hTrc` pair only if the base was unit-diagonal already. -/
theorem full_scale_forces_unit_base (hn : 0 < n) {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq < 4)
    (hband : ∀ i, |(1 - dq / 4) * Q i i - 1| ≤ dq / 4)
    (htrc : ∑ i, (1 - dq / 4) * Q i i ≤ (n : ℚ) * (1 - dq / 4)) :
    ∀ i, Q i i = 1 := by
  have hpos : (0 : ℚ) < 1 - dq / 4 := by linarith
  have hge : ∀ j : Fin n, 1 ≤ Q j j := by
    intro j
    have h := (abs_le.mp (hband j)).1
    exact (mul_le_mul_iff_of_pos_left hpos).mp (by simpa using h)
  have hsum : ∑ _j : Fin n, (1 - dq / 4) = (n : ℚ) * (1 - dq / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (1 - dq / 4) * Q j j - (1 - dq / 4) := by
    intro j _
    have := (mul_le_mul_iff_of_pos_left hpos).mpr (hge j)
    linarith
  have ht : ∑ j, (1 - dq / 4) * Q j j ≤ (n : ℚ) * (1 - dq / 4) := htrc
  have htotal : ∑ j, ((1 - dq / 4) * Q j j - (1 - dq / 4)) ≤ 0 := by
    have hsub : ∑ j, ((1 - dq / 4) * Q j j - (1 - dq / 4))
        = (∑ j, (1 - dq / 4) * Q j j) - (n : ℚ) * (1 - dq / 4) := by
      rw [Finset.sum_sub_distrib, hsum]
    rw [hsub]
    linarith
  intro i
  have herase : ((1 - dq / 4) * Q i i - (1 - dq / 4))
      + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          ((1 - dq / 4) * Q j j - (1 - dq / 4))
      = ∑ j, ((1 - dq / 4) * Q j j - (1 - dq / 4)) :=
    Finset.add_sum_erase Finset.univ (fun j => (1 - dq / 4) * Q j j - (1 - dq / 4))
      (Finset.mem_univ i)
  have hrest : 0 ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      ((1 - dq / 4) * Q j j - (1 - dq / 4)) :=
    Finset.sum_nonneg (fun j _ => hnonneg j (Finset.mem_univ j))
  have hle : (1 - dq / 4) * Q i i - (1 - dq / 4) ≤ 0 := by linarith
  have hle' : (1 - dq / 4) * Q i i ≤ (1 - dq / 4) * 1 := by rw [mul_one]; linarith
  exact le_antisymm ((mul_le_mul_iff_of_pos_left hpos).mp hle') (hge i)

/-- **The admissible-scale dichotomy, in the conduit's shape.** -/
theorem smul_centre_admissible_iff (hn : 0 < n) {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq < 4) :
    ((∀ i, |((1 - dq / 4) • Q) i i - 1| ≤ dq / 4)
        ∧ (∑ i, ((1 - dq / 4) • Q) i i ≤ (n : ℚ) * (1 - dq / 4)))
      ↔ ∀ i, Q i i = 1 := by
  constructor
  · rintro ⟨hb, ht⟩
    refine full_scale_forces_unit_base hn hdq hdq4 (fun i => ?_) ?_
    · simpa only [Matrix.smul_apply, smul_eq_mul] using hb i
    · simpa only [Matrix.smul_apply, smul_eq_mul] using ht
  · intro hQ
    have hpos : (0 : ℚ) < 1 - dq / 4 := by linarith
    constructor
    · intro i
      rw [Matrix.smul_apply, smul_eq_mul, hQ i, mul_one, abs_le]
      constructor <;> linarith
    · have h1 : ∑ i, ((1 - dq / 4) • Q) i i = ∑ _i : Fin n, (1 - dq / 4) := by
        refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
        rw [Matrix.smul_apply, smul_eq_mul, hQ i, mul_one]
      rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 4.  The forced replacement: overwrite the diagonal, never rescale it -/

/-- `Q` with its diagonal replaced by `1 − dq/4`. -/
def diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if i = j then 1 - dq / 4 else Q i j

@[simp] theorem diagPinch_diag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) (i : Fin n) :
    diagPinch Q dq i i = 1 - dq / 4 := by
  simp [diagPinch]

theorem diagPinch_off {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ} {i j : Fin n}
    (h : i ≠ j) : diagPinch Q dq i j = Q i j := by
  simp [diagPinch, h]

/-- `diagPinch` satisfies the conduit's trace slot **for every base, with equality**. -/
theorem sum_diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) :
    ∑ i, diagPinch Q dq i i = (n : ℚ) * (1 - dq / 4) := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => diagPinch_diag Q dq i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `diagPinch` satisfies `RelaxMem.diag_near` **for every base**. -/
theorem abs_diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) {dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) (i : Fin n) :
    |diagPinch Q dq i i - 1| ≤ dq / 4 := by
  rw [diagPinch_diag, abs_le]
  constructor <;> linarith

/-- The diagonal overwrite is invisible to `frob` whenever the weight matrix has zero diagonal
(`wMatrixQ` does).  So `trace_le` is *inherited*, not paid for. -/
theorem frob_diagPinch {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hA : ∀ i, A i i = 0) :
    QMCLeafB.SepOracle.frob A (diagPinch Q dq) = QMCLeafB.SepOracle.frob A Q := by
  rw [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.frob]
  refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
  refine Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => ?_)
  by_cases h : i = j
  · subst h
    rw [diagPinch_diag, hA i]
    ring
  · rw [diagPinch_off h]

/-- The exact PSD cost of the diagonal overwrite. -/
theorem qf_diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (diagPinch Q dq) x
      = QMCLeafB.SepOracle.qf Q x + ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, QMCLeafB.SepOracle.qf_eq_sum]
  have hinner : ∀ i : Fin n, ∑ j, x i * (diagPinch Q dq i j * x j)
      = ∑ j, x i * (Q i j * x j) + ((1 - dq / 4) - Q i i) * x i ^ 2 := by
    intro i
    have hstep : ∑ j, x i * (diagPinch Q dq i j * x j)
        = ∑ j, (x i * (Q i j * x j)
            + (if j = i then ((1 - dq / 4) - Q i i) * x i ^ 2 else 0)) := by
      refine Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => ?_)
      by_cases h : j = i
      · subst h
        rw [diagPinch_diag]
        split_ifs with hh
        · ring
        · exact absurd rfl hh
      · rw [diagPinch_off (Ne.symm h)]
        simp only [if_neg h, add_zero]
    rw [hstep, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  calc ∑ i, ∑ j, x i * (diagPinch Q dq i j * x j)
      = ∑ i, (∑ j, x i * (Q i j * x j) + ((1 - dq / 4) - Q i i) * x i ^ 2) :=
        Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hinner i)
    _ = ∑ i, ∑ j, x i * (Q i j * x j) + ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2 :=
        Finset.sum_add_distrib


/-! ## 5.  The run-level instantiations: the `ok` round cannot query its own state -/

/-- An `ok` answer from the round's separation oracle forces `dvR = 0` (the diagonal-repair branch
answers `true`). -/
theorem oracleR_ok_dvR_zero {s : QMCLeafB.RoundProgram.RSt}
    (h : (QMCLeafB.RoundProgram.oracleR s).1 = false) :
    QMCLeafB.RoundProgram.dvR s = 0 := by
  by_cases hd : QMCLeafB.RoundProgram.dvR s = 0
  · exact hd
  · rw [QMCLeafB.RoundProgram.oracleR, if_neg hd] at h
    exact absurd h (by simp)

/-- `toMatrix`'s diagonal is `entV`'s diagonal — the bridge from the state's code to the matrix the
conduit's `cX k` lives in. -/
theorem toMatrix_diag_eq_entV (n : ℕ) (xs : List ℚ) (i : Fin n) :
    (MatQ.toMatrix n xs) i i
      = QMCLeafB.RoundProgram.entV (n, xs) (i : ℕ) (i : ℕ) := rfl


/-- **`dvR = 0` states are unit-diagonal, at the matrix level** — the `hQ` hypothesis of
`relaxMem_diagPinch` / `ok_round_centre_admissible`. -/
theorem unit_diag_of_dvR_zero {n : ℕ} {xs : List ℚ} (hlen : xs.length = n * n)
    (h0 : QMCLeafB.RoundProgram.diagSumV (n, xs) = 0) (i : Fin n) :
    (MatQ.toMatrix n xs) i i = 1 := by
  rw [toMatrix_diag_eq_entV]
  exact QMCLeafB.AuditM1.diagSumV_eq_zero hlen h0 i.isLt

/-- **A `dvR = 0` state never satisfies `hTrc`** — the raw-state centre of an `ok` round. -/
theorem dvR_zero_state_breaks_trace {n : ℕ} (hn : 0 < n) {xs : List ℚ}
    (hlen : xs.length = n * n) {dq : ℚ} (hdq : 0 < dq)
    (h0 : QMCLeafB.RoundProgram.diagSumV (n, xs) = 0) :
    ¬ (∑ i : Fin n, (MatQ.toMatrix n xs) i i ≤ (n : ℚ) * (1 - dq / 4)) := by
  refine unit_diag_breaks_trace hn hdq (fun i => ?_)
  rw [toMatrix_diag_eq_entV]
  exact QMCLeafB.AuditM1.diagSumV_eq_zero hlen h0 i.isLt

/-- **The `ok` round's own state is not an admissible centre.**  `ok` forces `dvR = 0`
(`oracleR_ok_dvR_zero`), the diagonal is then identically `1` (`AuditM1.diagSumV_eq_zero`), and
`hTrc` is false (`unit_diag_breaks_trace`).  So at an `ok` round the conduit's centre has to be a
surrogate: the smallest admissible one is `diagPinch` of the state (§4), whose diagonal shift is
invisible to `frob`. -/
theorem ok_round_state_not_admissible {s : QMCLeafB.RoundProgram.RSt}
    (hn : 0 < QMCLeafB.RoundProgram.stN s)
    (hlen : (QMCLeafB.RoundProgram.stX s).length
      = QMCLeafB.RoundProgram.stN s * QMCLeafB.RoundProgram.stN s)
    (hok : (QMCLeafB.RoundProgram.oracleR s).1 = false) {dq : ℚ} (hdq : 0 < dq) :
    ¬ (∑ i : Fin (QMCLeafB.RoundProgram.stN s),
        (MatQ.toMatrix (QMCLeafB.RoundProgram.stN s)
          (QMCLeafB.RoundProgram.stX s)) i i
        ≤ (QMCLeafB.RoundProgram.stN s : ℚ) * (1 - dq / 4)) :=
  dvR_zero_state_breaks_trace hn hlen hdq (oracleR_ok_dvR_zero hok)


/-! ## 6.  The ok branch, composed: exact PSD + unit diagonal ⟹ `RelaxMem` at `diagPinch` -/

/-- **The ok-round `RelaxMem`, assembled.**  Three facts about the *state* give the conduit's
`hmem` at the pinched surrogate:

* `hQ : ∀ i, Q i i = 1` — the state is unit-diagonal (`dvR = 0`, forced by an `ok` answer);
* `hpsd : ∀ x, 0 ≤ qf Q x` — the state is **exactly** PSD, which is what `runPiv_psd`
  (`QMCLeafB.RunInduction.runPiv_psd`) delivers from the pivot descent's `false` answer — no
  tolerance is involved;
* `htrace : frob A Q ≤ u + dq/2` — the programme's own `ok` test at level `u`
  (`QMCLeafB.OkLower.levelOf` supplies it).

The PSD margin at the pinched centre is then `dq/4`, half the allowed `dq/2`: the `dq/4` spent
lowering the diagonal is exactly the slack. -/
theorem relaxMem_diagPinch {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) (hA : ∀ i, A i i = 0) (hQ : ∀ i, Q i i = 1)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (diagPinch Q dq) u dq where
  δ_pos := hdq
  psd_margin := by
    intro x
    have hsimp : ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2 = (-(dq / 4)) * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
      rw [hQ i]
      ring
    rw [qf_diagPinch, hsimp]
    have hsum : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have hp := hpsd x
    nlinarith [hsum, hp, hdq]
  diag_near := abs_diagPinch Q hdq hdq4
  trace_le := by
    rw [frob_diagPinch hA]
    exact htrace


/-- `diagPinch` preserves symmetry — the conduit's `hCsym` slot is inherited from the state. -/
theorem diagPinch_symm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hQ : ∀ i j, Q i j = Q j i) (dq : ℚ) :
    ∀ i j, diagPinch Q dq i j = diagPinch Q dq j i := by
  intro i j
  by_cases h : i = j
  · subst h
    simp
  · rw [diagPinch_off (Ne.symm h), diagPinch_off h]
    exact (hQ j i).symm


/-! ## 7.  What the pinch costs in the drift ledger -/

/-- **The `hdriftd` cost of the diagonal overwrite.**  The all-ones direction `dOne` pairs with the
flattened centre as the *total mass* `∑ i j, cX i j`, so the drift inequality's left side moves by
exactly `∑ i, Q i i − n(1 − dq/4)` when the centre is pinched.  At a unit-diagonal base (an `ok`
round) that cost is `n·dq/4`, and it is `0` at a centre already pinched.  `frob` meanwhile does not
move at all (`frob_diagPinch`), so the `trace_le`/`hstated` frobenius half is free. -/
theorem mass_shift_diagPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) :
    ∑ i : Fin n, ∑ j : Fin n, (Q - diagPinch Q dq) i j
      = (∑ i : Fin n, Q i i) - (n : ℚ) * (1 - dq / 4) := by
  have hinner : ∀ i : Fin n, ∑ j : Fin n, (Q - diagPinch Q dq) i j = Q i i - (1 - dq / 4) := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.sub_apply, diagPinch_diag]
    · intro j _ hj
      rw [Matrix.sub_apply, diagPinch_off (Ne.symm hj), sub_self]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hinner i), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]


/-! ## 8.  The side condition `dq ≤ 4` is free at the campaign's family -/

/-- **`dqShallow G ≤ 4` with no hypothesis beyond positive weight.**  `dqShallow = ε/(9 Rq + 1)` with
`ε = Rq/40000`, so it is at most `1/360000`; this discharges the `dq ≤ 4` side condition of
`abs_diagPinch` / `relaxMem_diagPinch` / `relaxMem_boundary_smul` at `paramsKbc2`, where
`(paramsKbc2 G).dq = dqShallow G` (`QMCLeafB.UnionShallow.paramsKbc2_dq`). -/
theorem dqShallow_le_four (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G ≤ 4 := by
  rw [QMCLeafB.RundataParams.dqShallow, if_neg (ne_of_gt hRq),
    QMCLeafB.RundataParams.dqShallowCore]
  unfold QMCLeafB.RundataCert.eps
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith [hRq]


/-- **The one-stop citation for the `ok` round**: the `diagPinch` centre carries the conduit's two
centre slots at once — `RelaxMem` (the `ok`-round `hmem`) and `hTrc` (every round) — from the state's
unit diagonal, exact PSD, and the programme's own `ok` test. -/
theorem ok_round_centre_admissible {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) (hA : ∀ i, A i i = 0) (hQ : ∀ i, Q i i = 1)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (diagPinch Q dq) u dq
      ∧ (∑ i, diagPinch Q dq i i ≤ (n : ℚ) * (1 - dq / 4)) :=
  ⟨relaxMem_diagPinch hdq hdq4 hA hQ hpsd htrace, le_of_eq (sum_diagPinch Q dq)⟩

/-- **The cut round's centre**: `hmem` is vacuous there (`ok k = false`), so `hTrc` is the only centre
constraint the conduit imposes — and `diagPinch` meets it at *every* base, with equality. -/
theorem cut_round_centre_admissible (Q : Matrix (Fin n) (Fin n) ℚ) (dq : ℚ) :
    ∑ i, diagPinch Q dq i i ≤ (n : ℚ) * (1 - dq / 4) :=
  le_of_eq (sum_diagPinch Q dq)

end QMCLeafB.CentreAdm

#print axioms QMCLeafB.CentreAdm.pinch_of_trace
#print axioms QMCLeafB.CentreAdm.trace_eq_of_pinch
#print axioms QMCLeafB.CentreAdm.unit_diag_breaks_trace
#print axioms QMCLeafB.CentreAdm.full_scale_forces_unit_base
#print axioms QMCLeafB.CentreAdm.smul_centre_admissible_iff
#print axioms QMCLeafB.CentreAdm.diagPinch_off
#print axioms QMCLeafB.CentreAdm.toMatrix_diag_eq_entV
#print axioms QMCLeafB.CentreAdm.sum_diagPinch
#print axioms QMCLeafB.CentreAdm.abs_diagPinch
#print axioms QMCLeafB.CentreAdm.frob_diagPinch
#print axioms QMCLeafB.CentreAdm.qf_diagPinch
#print axioms QMCLeafB.CentreAdm.oracleR_ok_dvR_zero
#print axioms QMCLeafB.CentreAdm.unit_diag_of_dvR_zero
#print axioms QMCLeafB.CentreAdm.dvR_zero_state_breaks_trace
#print axioms QMCLeafB.CentreAdm.ok_round_state_not_admissible
#print axioms QMCLeafB.CentreAdm.relaxMem_diagPinch
#print axioms QMCLeafB.CentreAdm.diagPinch_symm
#print axioms QMCLeafB.CentreAdm.mass_shift_diagPinch
#print axioms QMCLeafB.CentreAdm.dqShallow_le_four
#print axioms QMCLeafB.CentreAdm.ok_round_centre_admissible
#print axioms QMCLeafB.CentreAdm.cut_round_centre_admissible


