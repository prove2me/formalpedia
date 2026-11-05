-- Prove2me | Definitions.Def_QMCLeafB_ldltcert2_m5
-- name    : QMCLeafB_ldltcert2_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:17:00.231909+00:00
-- url     : https://prove2.me/theorems/a6ddb1fd-56fe-4e88-a438-3df45ef1126e
-- title:
--   QMCLeafB ldltcert2_m5
-- statement:
--   # leaf B phase 20 — brick `interval-ldlt-psdmargin` (swarm `smw1kspvn`, member m5, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_pivexact
import Definitions.Def_QMCLeafB_contract_m7
/-
# leaf B phase 20 — brick `interval-ldlt-psdmargin` (swarm `smw1kspvn`, member m5, direction d1)

## What this file settles

Phase 19's contract audit (`Check_contract_m7`) proved three negative facts about brick 1 in the form
the task list states it:

* `pivAns_not_sound` / `not_pivPsdMargin_sGrid` / `pivFSpec_false`: at the campaign grid
  `d = gridOf 2 = 81`, `mu = 8`, every `δ < 4/1053` fails the margin clause — the snapped descent
  truncates the Schur complement `-1/162` to `0` and then answers `false` on an indefinite block;
* hence `(pivAns s).1 = false → PivPsdMargin s dq` is **not** available at the campaign tolerance
  `dqShallow < 1/360000` with the campaign grid;
* `tolerance_floor`: *any* certifier of the clause pays `2η/‖v‖²` at a violating witness.

This file supplies the **positive** half of the same story, i.e. the `d1` route (m8's
`Check_pivexact_m8` supplies the complementary exact-descent route): the snapped descent's `false`
answer does certify a PSD margin, but with the tolerance **the grid error it actually incurred**,
namely

    δ = 2·ε·n²  with  ε = 1/d   (d = the state's own grid denominator),

i.e. `δ = 2 n²/d`, which is the interval-LDLᵀ error propagation of the normalized (clipped +
snapped) Schur descent.  Consequences for the campaign are recorded at the end: the grid must be
refined to `d ≳ n²/dq` (at `Gtwo` that is `d ≳ 8·10⁴` against the current `81`, matching the
`~3000×` of the phase-19 note), and `dq ≥ 2n²/d` is exactly the exchange rate.

## The mathematical content

The descent `runPivL` (== `RoundProgram.pivAns`'s driver) is the exact rational LDLᵀ descent with
every continuation **re-normalized**: `nrmQ mu d q = snapDiv d (clipRat mu q)` clips into `[-mu,mu]`
and truncates onto `(1/d)ℤ`.  Write `X` for the current block and `S := schur X (X 0 0)` for the
exact Schur complement the program computes *before* normalizing it.

Two elementary transfers do all the work:

* `schur_step_radius`: if `X 0 0 > 0`, `X` symmetric, and `S'` is an entrywise `ε`-approximation of
  `S` whose quadratic form is bounded below by `-ε k² ‖y‖²` (`k = dim S`), then
  `qf X x ≥ -ε (k+1)² ‖x‖²`.  The identity used is the classical Schur decomposition
  `qf X x = X₀₀·(x₀ + b·y/X₀₀)² + qf (schur X X₀₀) y` (`schur_split_qf`).
* `drop_step_radius`: same statement in the zero-pivot/zero-row branch with `tail X` in place of
  `schur X X₀₀`.

Hence, with `k` decreasing by one each step and each step paying `ε·k`, the accumulated radius is
`∑_j ε·k_j ≤ ε·n²` — this is the tracked entrywise radius, and it is *outward*: the same estimate
covers truncation and ceiling rounding alike, because both err by at most `1/d` entrywise.  (It is
the *outward* direction that the snapped test loses: truncation toward zero turns `-1/162` into `0`,
and this file's estimate is what that truncation costs — `1/d` per entry — not what it saves.)

The radius hypothesis is stated as a predicate on the run, not on the state: `EvRun mu d ε N p`
says that *at every state the descent visits*, both continuations (`schurRows`, `dropRows`) are
`ε`-close to their own normalization.  `BoxRun mu N p` is the same tracker in the form the interval
routine would compute and check: at every visited state both continuations stay inside the clip box
`[-mu, mu]`, so the clip is the identity there and the sharp radius `ε = 1/d` follows
(`evRun_of_box`).  Both are finite checks along the same descent loop that `poly_runPivL` already
runs, and both are height-bounded: `hasHeight_nrmQ` (`Check_round_program_m3`) keeps every
normalized entry at height `L + D` when `mu` has height `L` and `d ≤ 2^D`, so the checker is
`Poly` by the same loop toolkit.  (The `Poly` *packaging* of the boolean tracker itself is not
re-proved here; the descent it walks over is `poly_runPivL`.)

## What is not claimed

* Nothing here revisits `d4`/`pivAns_not_sound`: the refuted statement stays refuted.  The margin
  produced is the grid's, and `pivFSpec_false` is consistent with it (`2·2²/81 = 8/81 > 4/1053`).
* The clip is *not* free: §8's crude corollary `pivPsdMargin_of_entryBound` shows that the clause
  is inhabited at `δ = 2μn` with no use of the descent at all — so the whole content of the sharp
  theorem is the exchange rate `2n²/d` replacing `2μn`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
`#print axioms` audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.LdltCertM5

open QMCLeafB.RoundProgram
open QMCLeafB.PivotProgram
open QMCLeafB.SepOracle
open QMCLeafB.RunInduction

/-! ## 1.  Elementary material: tails of sums of squares, and the split of `qf` -/

/-- The trailing coordinates contribute at most the whole sum of squares. -/
theorem sum_sq_tail_le {k : ℕ} (x : Fin (k + 1) → ℚ) :
    (∑ i : Fin k, x i.succ ^ 2) ≤ ∑ i : Fin (k + 1), x i ^ 2 := by
  rw [Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 0)]

/-- **The Schur split of the quadratic form**, in the shape the radius induction consumes: for a
symmetric block with positive corner, `qf X x` is `X₀₀·(x₀ + (b·y)/X₀₀)²` plus the Schur
complement's form at the tail.  (Complete the square; `SepOracle.qf_cons` + `SepOracle.qf_schur`.) -/
theorem schur_split_qf {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ}
    (hsym : ∀ i j, X i j = X j i) (ha0 : 0 < X 0 0) (x : Fin (k + 1) → ℚ) :
    qf X x = X 0 0 * (x 0 + (headRow X ⬝ᵥ Fin.tail x) / (X 0 0)) ^ 2
      + qf (schur X (X 0 0)) (Fin.tail x) := by
  have hA : qf X x = X 0 0 * (x 0) ^ 2 + 2 * (x 0) * (headRow X ⬝ᵥ Fin.tail x)
      + qf (tail X) (Fin.tail x) := by
    rw [show x = Fin.cons (x 0) (Fin.tail x) from (Fin.cons_self_tail x).symm]
    exact qf_cons X hsym _ _
  have hB : qf (schur X (X 0 0)) (Fin.tail x)
      = X 0 0 * (-(headRow X ⬝ᵥ Fin.tail x) / (X 0 0)) ^ 2
        + 2 * (-(headRow X ⬝ᵥ Fin.tail x) / (X 0 0)) * (headRow X ⬝ᵥ Fin.tail x)
        + qf (tail X) (Fin.tail x) := by
    rw [← qf_schur X hsym (rfl : X 0 0 = X 0 0) (ne_of_gt ha0) (Fin.tail x)]
    exact qf_cons X hsym _ _
  rw [hA, hB]
  have ha : X 0 0 ≠ 0 := ne_of_gt ha0
  field_simp
  ring

/-! ## 2.  The two one-step transfers: how a `k × k` radius becomes a `(k+1) × (k+1)` radius -/

/-- **Schur step.**  If `S'` approximates the exact Schur complement `schur X (X 0 0)` entrywise to
`ε`, and `S'`'s quadratic form is bounded below by `-ε k² ‖y‖²`, then `X`'s is bounded below by
`-ε (k+1)² ‖x‖²`.  This is the whole error propagation of the normalized descent: the completing
square is exact (`schur_split_qf`), so the only loss is the radius at the child. -/
theorem schur_step_radius {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ}
    (hsym : ∀ i j, X i j = X j i) (ha0 : 0 < X 0 0)
    {S' : Matrix (Fin k) (Fin k) ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    (hS : ∀ i j, |S' i j - schur X (X 0 0) i j| ≤ ε)
    (hchild : ∀ y : Fin k → ℚ, -(ε * (k : ℚ) * (k : ℚ)) * (∑ i, y i ^ 2) ≤ qf S' y) :
    ∀ x : Fin (k + 1) → ℚ,
      -(ε * ((k : ℚ) + 1) * ((k : ℚ) + 1)) * (∑ i, x i ^ 2) ≤ qf X x := by
  intro x
  have hsplit : qf (schur X (X 0 0)) (Fin.tail x) - qf S' (Fin.tail x)
      = qf (schur X (X 0 0) - S') (Fin.tail x) := by rw [qf_sub]
  have habs := abs_qf_le_of_entrywise_le (schur X (X 0 0) - S') (Fin.tail x)
    (ε := ε) (fun i j => by rw [Matrix.sub_apply, abs_sub_comm]; exact hS i j) hε
  have hstep : qf (schur X (X 0 0)) (Fin.tail x)
      ≥ qf S' (Fin.tail x) - ε * (k : ℚ) * (∑ i : Fin k, (Fin.tail x) i ^ 2) := by
    have hA : qf (schur X (X 0 0)) (Fin.tail x)
        = qf S' (Fin.tail x) + qf (schur X (X 0 0) - S') (Fin.tail x) := by
      rw [qf_sub]
      ring
    rw [hA]
    linarith [neg_abs_le (qf (schur X (X 0 0) - S') (Fin.tail x)), habs]
  have hy := hchild (Fin.tail x)
  have hmain : qf X x ≥ qf (schur X (X 0 0)) (Fin.tail x) := by
    rw [schur_split_qf hsym ha0 x]
    have hnn : 0 ≤ X 0 0 * (x 0 + (headRow X ⬝ᵥ Fin.tail x) / (X 0 0)) ^ 2 :=
      mul_nonneg (le_of_lt ha0) (sq_nonneg _)
    linarith
  have hsum_le : (∑ i : Fin k, (Fin.tail x) i ^ 2) ≤ ∑ i : Fin (k + 1), x i ^ 2 :=
    sum_sq_tail_le x
  have hnn : (0 : ℚ) ≤ ∑ i : Fin k, (Fin.tail x) i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hck : (0 : ℚ) ≤ ε * (k : ℚ) := mul_nonneg hε (by positivity)
  have hck1 : (0 : ℚ) ≤ ε * ((k : ℚ) + 1) * ((k : ℚ) + 1) := by positivity
  have hkey : ε * (k : ℚ) * (k : ℚ) + ε * (k : ℚ) ≤ ε * ((k : ℚ) + 1) * ((k : ℚ) + 1) := by
    nlinarith
  nlinarith [hstep, hy, hmain, hsum_le, hnn, hck, hck1, hkey]

/-- **Drop step.**  The zero-pivot / zero-first-row branch: `qf X x = qf (tail X) (Fin.tail x)`
exactly, so the same radius arithmetic applies with `tail X` in place of the Schur complement. -/
theorem drop_step_radius {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ}
    (hsym : ∀ i j, X i j = X j i) (h00 : X 0 0 = 0) (hrow : headRow X = 0)
    {S' : Matrix (Fin k) (Fin k) ℚ} {ε : ℚ} (hε : 0 ≤ ε)
    (hS : ∀ i j, |S' i j - tail X i j| ≤ ε)
    (hchild : ∀ y : Fin k → ℚ, -(ε * (k : ℚ) * (k : ℚ)) * (∑ i, y i ^ 2) ≤ qf S' y) :
    ∀ x : Fin (k + 1) → ℚ,
      -(ε * ((k : ℚ) + 1) * ((k : ℚ) + 1)) * (∑ i, x i ^ 2) ≤ qf X x := by
  intro x
  have hdrop : qf X x = qf (tail X) (Fin.tail x) := by
    rw [← Fin.cons_self_tail x, qf_cons X hsym (x 0) (Fin.tail x), h00, hrow]
    simp [dotProduct]
  have hsplit : qf (tail X) (Fin.tail x) - qf S' (Fin.tail x)
      = qf (tail X - S') (Fin.tail x) := by rw [qf_sub]
  have habs := abs_qf_le_of_entrywise_le (tail X - S') (Fin.tail x)
    (ε := ε) (fun i j => by rw [Matrix.sub_apply, abs_sub_comm]; exact hS i j) hε
  have hstep : qf (tail X) (Fin.tail x)
      ≥ qf S' (Fin.tail x) - ε * (k : ℚ) * (∑ i : Fin k, (Fin.tail x) i ^ 2) := by
    have hA : qf (tail X) (Fin.tail x)
        = qf S' (Fin.tail x) + qf (tail X - S') (Fin.tail x) := by
      rw [qf_sub]
      ring
    rw [hA]
    linarith [neg_abs_le (qf (tail X - S') (Fin.tail x)), habs]
  have hy := hchild (Fin.tail x)
  have hsum_le : (∑ i : Fin k, (Fin.tail x) i ^ 2) ≤ ∑ i : Fin (k + 1), x i ^ 2 :=
    sum_sq_tail_le x
  have hnn : (0 : ℚ) ≤ ∑ i : Fin k, (Fin.tail x) i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hck : (0 : ℚ) ≤ ε * (k : ℚ) := mul_nonneg hε (by positivity)
  have hck1 : (0 : ℚ) ≤ ε * ((k : ℚ) + 1) * ((k : ℚ) + 1) := by positivity
  have hkey : ε * (k : ℚ) * (k : ℚ) + ε * (k : ℚ) ≤ ε * ((k : ℚ) + 1) * ((k : ℚ) + 1) := by
    nlinarith
  nlinarith [hstep, hy, hsum_le, hnn, hck, hck1, hkey]

/-! ## 3.  The normalization's error: clip and snap, outward -/

/-- `nrmQ` fixes `0` (so it transports row codes, `RunInduction.rowCode_mapRows`). -/
theorem nrmQ_zero (mu : ℚ) (d : ℕ) : nrmQ mu d 0 = 0 := by
  unfold nrmQ clipRat
  by_cases hb : inBoxR mu 0 = true
  · rw [if_pos hb, QMCLeafB.RoundPolySnap.snapDiv_zero]
  · rw [if_neg hb, QMCLeafB.RoundPolySnap.snapDiv_zero]

/-- `nrmRows` is the entrywise map of `RunInduction.rowCode_mapRows`. -/
theorem nrmRows_eq_map (mu : ℚ) (d : ℕ) (rows : Rows) :
    nrmRows mu d rows = rows.map (List.map (nrmQ mu d)) := by
  simp [nrmRows, nrmRow]

/-- **The tracked radius, sharply**: inside the clip box the normalization is the snap, whose
entrywise error is at most one grid step `1/d`.  This is the local estimate the interval routine
checks at every step of the descent. -/
theorem nrmQ_error_of_box {mu q : ℚ} {d : ℕ} (hd : 0 < d) (hq : |q| ≤ mu) :
    |nrmQ mu d q - q| ≤ 1 / (d : ℚ) := by
  have hb : inBoxR mu q = true := by
    rw [inBoxR_iff]
    exact abs_le.mp hq
  unfold nrmQ
  rw [clipRat_of_inBox hb]
  exact QMCLeafB.RoundPolySnap.snapDiv_error d hd q

/-! ## 4.  The radius trackers

`NrmErrRows` / `EvOk` / `EvRun` are the *analytic* hypotheses the radius induction consumes: at
every state the descent visits, both continuations (`schurRows`, `dropRows`) are entrywise `ε`-close
to their normalization.  `NrmBox` / `BoxRun` are the same tracker in the form the interval routine
computes: both continuations stay inside the clip box, so the clip is inert and `ε = 1/d` follows.

Both are finite checks along the descent loop.  They are `Prop`-valued here because the analytic
theorem only consumes them; the boolean checker that produces them is `Poly` by the same loop
toolkit that carries `RoundProgram.poly_runPivL` (see `hasHeight_nrmQ` for the height ledger). -/

/-- Entrywise `ε`-closeness of a block to its own normalization. -/
def NrmErrRows (mu : ℚ) (d : ℕ) (ε : ℚ) (rows : Rows) : Prop :=
  ∀ i j : ℕ, |nrmQ mu d ((rows.getD i []).getD j 0) - (rows.getD i []).getD j 0| ≤ ε

/-- Both continuations of the descent step are `ε`-accurately normalized. -/
def EvOk (mu : ℚ) (d : ℕ) (ε : ℚ) (rows : Rows) : Prop :=
  NrmErrRows mu d ε (schurRows rows) ∧ NrmErrRows mu d ε (dropRows rows)

/-- The successor state of the descent (itself on a terminal branch). -/
def nextL (p : LSt) : LSt := match pivStepL p with
  | Sum.inl _ => p
  | Sum.inr q => q

/-- The radius tracker along the descent: it holds at every visited state. -/
def EvRun (mu : ℚ) (d : ℕ) (ε : ℚ) : ℕ → LSt → Prop
  | 0, _ => True
  | (j + 1), p => EvOk mu d ε p.2.1 ∧ EvRun mu d ε j (nextL p)

/-- Entrywise box membership of a block. -/
def NrmBox (mu : ℚ) (rows : Rows) : Prop :=
  ∀ i j : ℕ, |(rows.getD i []).getD j 0| ≤ mu

/-- The box tracker along the descent: the clip is inert at every visited state. -/
def BoxRun (mu : ℚ) : ℕ → LSt → Prop
  | 0, _ => True
  | (j + 1), p => NrmBox mu (schurRows p.2.1) ∧ NrmBox mu (dropRows p.2.1) ∧ BoxRun mu j (nextL p)

/-- **The box tracker buys the sharp radius `1/d`.** -/
theorem evRun_of_box {mu : ℚ} {d : ℕ} (hd : 0 < d) :
    ∀ (N : ℕ) (p : LSt), BoxRun mu N p → EvRun mu d (1 / (d : ℚ)) N p
  | 0, _, _ => trivial
  | (j + 1), p, hb =>
      ⟨⟨fun i j' => nrmQ_error_of_box hd (hb.1 i j'),
        fun i j' => nrmQ_error_of_box hd (hb.2.1 i j')⟩,
       evRun_of_box hd j (nextL p) hb.2.2⟩

/-! ### 4.1  The tracker as a boolean check

`BoxRun` is not an analytic hypothesis: it is a finite check on the run, and this section makes that
literal by giving the boolean checker and its soundness.  `BoxRunB` walks the same continuation
(`nextL` is `pivStepL`'s `inr` state) with the same fuel as `pivAns`'s driver, over the same
`schurRows`/`dropRows` operations, and `rowCode`-preserving entrywise maps — so `poly_runPivL`'s loop
toolkit (`Check_round_program_m3` §3-§4) is exactly what carries it, and `hasHeight_nrmQ` keeps every
checked entry at height `L + D`.  (The `Poly` term itself is not rebuilt here.)

Caveat worth recording for the campaign: at a *fine* grid the clip box has to grow with `d`.  For a
block with `|X i j| ≤ μ` and pivot `X 0 0 ≥ 1/d` the exact Schur complement obeys
`|schur X X₀₀ i j| ≤ μ + μ²·d`, so `μ` fixed while `d → ∞` makes `BoxRun` *harder*, not easier; the
box must be chosen from the run's actual (unit-diagonal, `O(1)`) values, which is what the checker
does. -/

/-- `|l.getD i 0| ≤ μ` from a `List.all` box check. -/
theorem getD_le_of_all {l : List ℚ} {mu : ℚ} (hmu : 0 ≤ mu)
    (h : l.all (fun q => decide (|q| ≤ mu)) = true) (i : ℕ) : |l.getD i 0| ≤ mu := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem l 0 hi]
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hi))
  · rw [List.getD_eq_default l 0 (by omega)]
    simpa using hmu

/-- The same at the level of a block of rows. -/
theorem box_le_of_all {rows : Rows} {mu : ℚ} (hmu : 0 ≤ mu)
    (h : rows.all (fun r => r.all (fun q => decide (|q| ≤ mu))) = true) (i j : ℕ) :
    |(rows.getD i []).getD j 0| ≤ mu := by
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem rows [] hi]
    exact getD_le_of_all hmu (List.all_eq_true.mp h _ (List.getElem_mem hi)) j
  · rw [List.getD_eq_default rows [] (by omega)]
    simp only [List.getD_nil]
    simpa using hmu

/-- Boolean form of `NrmBox`: every entry of the block lies in `[-mu, mu]`. -/
def NrmBoxB (mu : ℚ) (rows : Rows) : Bool :=
  rows.all (fun r => r.all (fun q => decide (|q| ≤ mu)))

theorem nrmBox_of_nrmBoxB {mu : ℚ} (hmu : 0 ≤ mu) {rows : Rows}
    (h : NrmBoxB mu rows = true) : NrmBox mu rows :=
  fun i j => box_le_of_all hmu h i j

/-- **The box tracker as a boolean check** (the form the interval routine computes). -/
def BoxRunB (mu : ℚ) : ℕ → LSt → Bool
  | 0, _ => true
  | (j + 1), p =>
      (NrmBoxB mu (schurRows p.2.1) && NrmBoxB mu (dropRows p.2.1)) && BoxRunB mu j (nextL p)

/-- **The boolean check implies the tracker**: `BoxRunB mu N p = true → BoxRun mu N p`.  So nothing
analytic is hidden in `BoxRun` — it is a finite check on the run, of the same shape as the descent
(`nextL` is `pivStepL`'s continuation), and `poly_runPivL`'s loop toolkit is what carries it. -/
theorem boxRun_of_boxRunB {mu : ℚ} (hmu : 0 ≤ mu) :
    ∀ (N : ℕ) (p : LSt), BoxRunB mu N p = true → BoxRun mu N p
  | 0, _, _ => trivial
  | (j + 1), p, h => by
      have h2 : (NrmBoxB mu (schurRows p.2.1) && NrmBoxB mu (dropRows p.2.1)) = true
          ∧ BoxRunB mu j (nextL p) = true := (Bool.and_eq_true _ _).mp h
      have h3 : NrmBoxB mu (schurRows p.2.1) = true
          ∧ NrmBoxB mu (dropRows p.2.1) = true := (Bool.and_eq_true _ _).mp h2.1
      exact ⟨nrmBox_of_nrmBoxB hmu h3.1, nrmBox_of_nrmBoxB hmu h3.2,
        boxRun_of_boxRunB hmu j (nextL p) h2.2⟩

/-- Boolean form of `NrmErrRows`: every entry of the block is normalized to within `ε`. -/
def NrmErrB (mu : ℚ) (d : ℕ) (ε : ℚ) (rows : Rows) : Bool :=
  rows.all (fun r => r.all (fun q => decide (|nrmQ mu d q - q| ≤ ε)))

/-- The radius tracker as a boolean check, at a *given* `ε`. -/
def EvRunB (mu : ℚ) (d : ℕ) (ε : ℚ) : ℕ → LSt → Bool
  | 0, _ => true
  | (j + 1), p =>
      (NrmErrB mu d ε (schurRows p.2.1) && NrmErrB mu d ε (dropRows p.2.1))
        && EvRunB mu d ε j (nextL p)

/-- `|l.getD i 0|`-style extraction for the radius check. -/
theorem getD_err_of_all {l : List ℚ} {mu : ℚ} {d : ℕ} {ε : ℚ} (hε : 0 ≤ ε)
    (h : l.all (fun q => decide (|nrmQ mu d q - q| ≤ ε)) = true) (i : ℕ) :
    |nrmQ mu d (l.getD i 0) - l.getD i 0| ≤ ε := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem l 0 hi]
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.getElem_mem hi))
  · rw [List.getD_eq_default l 0 (by omega)]
    rw [nrmQ_zero, sub_zero, abs_zero]
    exact hε

theorem errRows_of_all {rows : Rows} {mu : ℚ} {d : ℕ} {ε : ℚ} (hε : 0 ≤ ε)
    (h : rows.all (fun r => r.all (fun q => decide (|nrmQ mu d q - q| ≤ ε))) = true) :
    NrmErrRows mu d ε rows := by
  intro i j
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem rows [] hi]
    exact getD_err_of_all hε (List.all_eq_true.mp h _ (List.getElem_mem hi)) j
  · rw [List.getD_eq_default rows [] (by omega)]
    simp only [List.getD_nil]
    rw [nrmQ_zero, sub_zero, abs_zero]
    exact hε

/-- **The radius check implies the tracker**: `EvRunB mu d ε N p = true → EvRun mu d ε N p`.  So the
error budget `ε` of the descent is a *verifiable* number, not a modelled one: a checker walks the run
and confirms that each continuation is normalized to within `ε`. -/
theorem evRun_of_evRunB {mu : ℚ} {d : ℕ} {ε : ℚ} (hε : 0 ≤ ε) :
    ∀ (N : ℕ) (p : LSt), EvRunB mu d ε N p = true → EvRun mu d ε N p
  | 0, _, _ => trivial
  | (j + 1), p, h => by
      have h2 : (NrmErrB mu d ε (schurRows p.2.1) && NrmErrB mu d ε (dropRows p.2.1)) = true
          ∧ EvRunB mu d ε j (nextL p) = true := (Bool.and_eq_true _ _).mp h
      have h3 : NrmErrB mu d ε (schurRows p.2.1) = true
          ∧ NrmErrB mu d ε (dropRows p.2.1) = true := (Bool.and_eq_true _ _).mp h2.1
      exact ⟨⟨errRows_of_all hε h3.1, errRows_of_all hε h3.2⟩,
        evRun_of_evRunB hε j (nextL p) h2.2⟩

/-! ## 5.  The branch lemmas: what one step of the descent is -/

theorem pivStepL_empty (mu : ℚ) (d : ℕ) (rows : Rows) (acc : Acc)
    (h : List.isEmpty rows = true) :
    pivStepL ((mu, d), (rows, acc)) = Sum.inl ((false, []) : Ans) := by
  rw [pivStepL_def, if_pos h]
  rfl

theorem pivStepL_neg (mu : ℚ) (d : ℕ) (rows : Rows) (acc : Acc)
    (h1 : ¬ List.isEmpty rows = true) (h2 : piv rows < 0) :
    pivStepL ((mu, d), (rows, acc)) = Sum.inl ((true, negWitness rows) : Ans) := by
  rw [pivStepL_def, if_neg h1, if_pos h2]
  rfl

theorem pivStepL_zeroCut (mu : ℚ) (d : ℕ) (rows : Rows) (acc : Acc)
    (h1 : ¬ List.isEmpty rows = true) (h2 : ¬ piv rows < 0) (h3 : piv rows = 0)
    (h4 : ¬ rowSq (headTail rows) = 0) :
    pivStepL ((mu, d), (rows, acc)) = Sum.inl ((true, zeroWitness rows) : Ans) := by
  rw [pivStepL_def, if_neg h1, if_neg h2, if_pos h3, if_neg h4]
  rfl

theorem pivStepL_drop (mu : ℚ) (d : ℕ) (rows : Rows) (acc : Acc)
    (h1 : ¬ List.isEmpty rows = true) (h2 : ¬ piv rows < 0) (h3 : piv rows = 0)
    (h4 : rowSq (headTail rows) = 0) :
    pivStepL ((mu, d), (rows, acc))
      = Sum.inr ((mu, d), (nrmRows mu d (dropRows rows), nrmAcc mu d acc)) := by
  rw [pivStepL_def, if_neg h1, if_neg h2, if_pos h3, if_pos h4]
  rfl

theorem pivStepL_schur (mu : ℚ) (d : ℕ) (rows : Rows) (acc : Acc)
    (h1 : ¬ List.isEmpty rows = true) (h2 : ¬ piv rows < 0) (h3 : ¬ piv rows = 0) :
    pivStepL ((mu, d), (rows, acc))
      = Sum.inr ((mu, d),
          (nrmRows mu d (schurRows rows), nrmAcc mu d ((piv rows, headTail rows) :: acc))) := by
  rw [pivStepL_def, if_neg h1, if_neg h2, if_neg h3]
  rfl

/-- The fuel's answer on an `inl` step. -/
theorem runPivLFuel_inl (N : ℕ) (p : LSt) (a : Ans) (h : pivStepL p = Sum.inl a) :
    runPivLFuel (N + 1) p = a := by
  rw [runPivLFuel_succ, h]

/-- The fuel's answer on an `inr` step. -/
theorem runPivLFuel_inr (N : ℕ) (p : LSt) (q : LSt) (h : pivStepL p = Sum.inr q) :
    runPivLFuel (N + 1) p = runPivLFuel N q := by
  rw [runPivLFuel_succ, h]

/-- The successor state of the descent (itself on a terminal branch). -/
theorem nextL_inl (p : LSt) (a : Ans) (h : pivStepL p = Sum.inl a) : nextL p = p := by
  unfold nextL
  rw [h]

theorem nextL_inr (p : LSt) (q : LSt) (h : pivStepL p = Sum.inr q) : nextL p = q := by
  unfold nextL
  rw [h]

/-! ## 6.  The run induction: the answer `false` costs `ε·n²` in quadratic-form margin -/

/-- **What a `false` answer means at radius `ε`**: `qf X x ≥ -ε·k²·‖x‖²`. -/
def SpecR (k : ℕ) (X : Matrix (Fin k) (Fin k) ℚ) (ε : ℚ) (ans : Ans) : Prop :=
  ans.1 = false → ∀ x : Fin k → ℚ, -(ε * (k : ℚ) * (k : ℚ)) * (∑ i, x i ^ 2) ≤ qf X x

/-- **The run induction.**  Along any descent whose every visited state normalizes both of its
continuations to within `ε`, the answer `false` bounds the current block's quadratic form by
`-ε k² ‖x‖²`.  Note that the matrix, the dimension and the radius are all *determined* by the
descent's own state (`RowCode`), which is what makes the tracker `EvRun` a check on the run and not
on the statement. -/
theorem specR_runPivLFuel (N : ℕ) :
    ∀ (rows : Rows) (acc : Acc) (k : ℕ) (X : Matrix (Fin k) (Fin k) ℚ) (mu : ℚ) (d : ℕ)
      (ε : ℚ),
      rows.length ≤ N → RowCode k X rows → (∀ i j, X i j = X j i) → 0 ≤ ε →
      EvRun mu d ε N ((mu, d), (rows, acc)) →
      SpecR k X ε (runPivLFuel N ((mu, d), (rows, acc))) := by
  induction N with
  | zero =>
      intro rows acc k X mu d ε hlen hc hsym hε hev
      have hnil : rows = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hk : k = 0 := by rw [hnil] at hc; exact hc.1.symm
      subst hk
      intro _ x
      simp [qf, dotProduct]
  | succ N ih =>
      intro rows acc k X mu d ε hlen hc hsym hε hev
      obtain ⟨hevOk, hevRun⟩ := hev
      by_cases h1 : List.isEmpty rows = true
      · -- stop: the block is `0 × 0`
        rw [runPivLFuel_inl N _ _ (pivStepL_empty mu d rows acc h1)]
        intro _ x
        have hnil : rows = [] := List.isEmpty_iff.mp h1
        have hk : k = 0 := by rw [hnil] at hc; exact hc.1.symm
        subst hk
        simp [qf, dotProduct]
      · by_cases h2 : piv rows < 0
        · -- negative pivot: a cut, the implication is vacuous
          rw [runPivLFuel_inl N _ _ (pivStepL_neg mu d rows acc h1 h2)]
          intro hcut
          exact absurd hcut (by simp)
        · by_cases h3 : piv rows = 0
          · by_cases h4 : rowSq (headTail rows) = 0
            · -- zero pivot, zero row: drop
              have hne : rows.length ≠ 0 := by
                intro hz
                have hnil : rows = [] := List.eq_nil_of_length_eq_zero hz
                rw [hnil] at h1
                simp at h1
              obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
                Nat.exists_eq_succ_of_ne_zero (by rw [← hc.1]; exact hne)
              have hstep := pivStepL_drop mu d rows acc h1 h2 h3 h4
              rw [runPivLFuel_inr N _ _ hstep]
              have hnext : nextL ((mu, d), (rows, acc))
                  = ((mu, d), (nrmRows mu d (dropRows rows), nrmAcc mu d acc)) :=
                nextL_inr _ _ hstep
              rw [nrmRows_eq_map] at hnext ⊢
              -- the child
              have hrc : RowCode k' (fun i j => nrmQ mu d (tail X i j))
                  ((dropRows rows).map (List.map (nrmQ mu d))) :=
                rowCode_mapRows (rowCode_dropRows hc) (nrmQ mu d) (nrmQ_zero mu d)
              have hlen' : ((dropRows rows).map (List.map (nrmQ mu d))).length ≤ N := by
                rw [List.length_map, (rowCode_dropRows hc).1]
                have hN : k' + 1 ≤ N + 1 := by rw [← hc.1]; exact hlen
                omega
              have hsym' : ∀ i j, (fun i j => nrmQ mu d (tail X i j)) i j
                  = (fun i j => nrmQ mu d (tail X i j)) j i := by
                intro i j
                exact congrArg (fun q => nrmQ mu d q) (hsym i.succ j.succ)
              have hX00 : X 0 0 = 0 := by rw [← piv_eq_entry hc]; exact h3
              have hrow0 : headRow X = 0 := by
                funext j
                have h5 := rowSq_zero_getD (headTail rows) h4 j.1
                have h6 : (headTail rows).getD j.1 0 = X 0 j.succ := by
                  rw [headTail_getD]
                  exact hc.2.2 0 j.succ
                rw [h6] at h5
                simpa [headRow] using h5
              have hS : ∀ i j : Fin k', |nrmQ mu d (tail X i j) - tail X i j| ≤ ε := by
                intro i j
                have h7 : ((dropRows rows).getD i.1 []).getD j.1 0 = tail X i j := by
                  have hh := congrFun (congrFun (toMat_dropRows hc) i) j
                  simpa [toMat] using hh
                rw [← h7]
                exact hevOk.2 i.1 j.1
              intro hans x
              have hchild := ih ((dropRows rows).map (List.map (nrmQ mu d)))
                (nrmAcc mu d acc) k' (fun i j => nrmQ mu d (tail X i j)) mu d ε
                hlen' hrc hsym' hε (by rw [← hnext]; exact hevRun) hans
              have hfin := drop_step_radius hsym hX00 hrow0 hε hS hchild x
              simpa [Nat.cast_add, Nat.cast_one] using hfin
            · -- zero pivot with a nonzero row: a cut
              rw [runPivLFuel_inl N _ _ (pivStepL_zeroCut mu d rows acc h1 h2 h3 h4)]
              intro hcut
              exact absurd hcut (by simp)
          · -- positive pivot: Schur
            have hne : rows.length ≠ 0 := by
              intro hz
              have hnil : rows = [] := List.eq_nil_of_length_eq_zero hz
              rw [hnil] at h1
              simp at h1
            obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
              Nat.exists_eq_succ_of_ne_zero (by rw [← hc.1]; exact hne)
            have hstep := pivStepL_schur mu d rows acc h1 h2 h3
            rw [runPivLFuel_inr N _ _ hstep]
            have hnext : nextL ((mu, d), (rows, acc))
                = ((mu, d), (nrmRows mu d (schurRows rows),
                    nrmAcc mu d ((piv rows, headTail rows) :: acc))) :=
              nextL_inr _ _ hstep
            rw [nrmRows_eq_map] at hnext ⊢
            have hrc : RowCode k' (fun i j => nrmQ mu d (schur X (X 0 0) i j))
                ((schurRows rows).map (List.map (nrmQ mu d))) :=
              rowCode_mapRows (rowCode_schurRows hc) (nrmQ mu d) (nrmQ_zero mu d)
            have hlen' : ((schurRows rows).map (List.map (nrmQ mu d))).length ≤ N := by
              rw [List.length_map, (rowCode_schurRows hc).1]
              have hN : k' + 1 ≤ N + 1 := by rw [← hc.1]; exact hlen
              omega
            have hsym' : ∀ i j, (fun i j => nrmQ mu d (schur X (X 0 0) i j)) i j
                = (fun i j => nrmQ mu d (schur X (X 0 0) i j)) j i := by
              intro i j
              exact congrArg (fun q => nrmQ mu d q) (schur_symm X hsym (X 0 0) i j)
            have hpiv : 0 < X 0 0 := by
              rw [← piv_eq_entry hc]
              exact lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h3)
            have hS : ∀ i j : Fin k', |nrmQ mu d (schur X (X 0 0) i j)
                - schur X (X 0 0) i j| ≤ ε := by
              intro i j
              have h7 : ((schurRows rows).getD i.1 []).getD j.1 0 = schur X (X 0 0) i j := by
                have hh := congrFun (congrFun (toMat_schurRows hc) i) j
                simpa [toMat] using hh
              rw [← h7]
              exact hevOk.1 i.1 j.1
            intro hans x
            have hchild := ih ((schurRows rows).map (List.map (nrmQ mu d)))
              (nrmAcc mu d ((piv rows, headTail rows) :: acc)) k'
              (fun i j => nrmQ mu d (schur X (X 0 0) i j)) mu d ε
              hlen' hrc hsym' hε (by rw [← hnext]; exact hevRun) hans
            have hfin := schur_step_radius hsym hpiv hε hS hchild x
            simpa [Nat.cast_add, Nat.cast_one] using hfin

/-! ## 7.  At the state of the round program -/

/-- **The interval-LDLᵀ certificate, at the sharp radius.**  If the clipped/snapped descent's
normalizations are `1/d`-accurate along its own run (the tracker `EvRun` at `ε = 1/d`), then its
`false` answer bounds the *state's* block below by `-(n²/d)·‖x‖²`, i.e. certifies the
`RelaxMem.psd_margin` clause at `δ = 2n²/d`. -/
theorem qf_margin_of_false {n : ℕ} {Xs : List ℚ} {mu : ℚ} {d : ℕ}
    (hlen : n ≤ Xs.length) (hd : 0 < d)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf n Xs i j = QMCLeafB.PivExact.matOf n Xs j i)
    (hev : EvRun mu d (1 / (d : ℚ)) n ((mu, d), (toRows (n, Xs), ([] : Acc))))
    (h : (runPivL ((mu, d), (toRows (n, Xs), ([] : Acc)))).1 = false) :
    ∀ x : Fin n → ℚ,
      -(((n : ℚ) * (n : ℚ) / (d : ℚ))) * (∑ i, x i ^ 2)
        ≤ qf (QMCLeafB.PivExact.matOf n Xs) x := by
  have hspec := specR_runPivLFuel n (toRows (n, Xs)) ([] : Acc) n
    (QMCLeafB.PivExact.matOf n Xs) mu d (1 / (d : ℚ))
    (le_of_eq (QMCLeafB.PivExact.length_toRows hlen))
    (QMCLeafB.PivExact.rowCode_toRows hlen) hsym (by positivity) hev
  have hrun : runPivL ((mu, d), (toRows (n, Xs), ([] : Acc)))
      = runPivLFuel n ((mu, d), (toRows (n, Xs), ([] : Acc))) := by
    unfold runPivL
    rw [QMCLeafB.PivExact.length_toRows hlen]
  rw [hrun] at h
  intro x
  have hx := hspec h x
  have hnk : (n : ℚ) * (n : ℚ) / (d : ℚ) = (1 / (d : ℚ)) * (n : ℚ) * (n : ℚ) := by
    field_simp
  rw [hnk]
  exact hx

/-- **`PivPsdMargin` at the grid's own tolerance.**  This is brick 1's first clause with the
correct `δ`: `δ = 2n²/d`, not the campaign tolerance `dq`.  The grid is a *free* parameter of
`RoundProgram.RSt`; the campaign's `gridOf n = (n+1)^4` is what makes it insufficient (see
`sharp_needs_grid`). -/
theorem pivPsdMargin_of_boxRun (s : RSt)
    (hlen : stN s ≤ (stX s).length) (hd : 0 < stD s)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    (hbox : BoxRun (stMu s) (stN s)
      ((stMu s, stD s), (toRows (stN s, stX s), ([] : Acc))))
    (h : (pivAns s).1 = false) :
    QMCLeafB.ContractM7.PivPsdMargin s
      (2 * ((stN s : ℚ) * (stN s : ℚ) / (stD s : ℚ))) := by
  have hev := evRun_of_box hd (stN s) _ hbox
  have hmain := qf_margin_of_false hlen hd hsym hev h
  intro x
  have h2 := hmain x
  have he : (2 * ((stN s : ℚ) * (stN s : ℚ) / (stD s : ℚ))) / 2
      = (stN s : ℚ) * (stN s : ℚ) / (stD s : ℚ) := by ring
  rw [he]
  exact h2

/-! ## 7b.  The campaign tolerance from a *measured* radius — no grid condition

`EvRun mu d ε` with a free `ε` is the general form of the certificate: `ε` is the error the descent
actually incurred, not a bound derived from `d`.  `EvRunB` (§4.1) verifies it, so `ε` is a
certificate-checker's scalar.  The two corollaries below are the campaign-parameter interface:

* `pivPsdMargin_of_measured`: `PivPsdMargin s dq` for **any** `dq` the measured radius fits into,
  `2·n²·ε ≤ dq` — at the campaign grid `d = gridOf n = (n+1)^4` this is a *checkable* inequality on
  the run, not the unattainable `2n²/d ≤ dqShallow`;
* `pivPsdMargin_of_exactRun`: when the descent never rounds (`ε = 0`, i.e. `nrmQ` is the identity at
  every visited state — again a finite check), the answer `false` gives `PSD` **exactly**, hence
  `PivPsdMargin s dq` for **every** `dq ≥ 0` including `dqShallow`, with no grid condition at all. -/

/-- The margin at a measured radius `ε` (no positivity of `d` needed). -/
theorem qf_margin_of_false_eps {n : ℕ} {Xs : List ℚ} {mu : ℚ} {d : ℕ} {ε : ℚ}
    (hlen : n ≤ Xs.length) (hε : 0 ≤ ε)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf n Xs i j = QMCLeafB.PivExact.matOf n Xs j i)
    (hev : EvRun mu d ε n ((mu, d), (toRows (n, Xs), ([] : Acc))))
    (h : (runPivL ((mu, d), (toRows (n, Xs), ([] : Acc)))).1 = false) :
    ∀ x : Fin n → ℚ,
      -(ε * (n : ℚ) * (n : ℚ)) * (∑ i, x i ^ 2)
        ≤ qf (QMCLeafB.PivExact.matOf n Xs) x := by
  have hspec := specR_runPivLFuel n (toRows (n, Xs)) ([] : Acc) n
    (QMCLeafB.PivExact.matOf n Xs) mu d ε
    (le_of_eq (QMCLeafB.PivExact.length_toRows hlen))
    (QMCLeafB.PivExact.rowCode_toRows hlen) hsym hε hev
  have hrun : runPivL ((mu, d), (toRows (n, Xs), ([] : Acc)))
      = runPivLFuel n ((mu, d), (toRows (n, Xs), ([] : Acc))) := by
    unfold runPivL
    rw [QMCLeafB.PivExact.length_toRows hlen]
  rw [hrun] at h
  exact hspec h

/-- **Brick 1 at the campaign tolerance, from a measured radius.** -/
theorem pivPsdMargin_of_measured (s : RSt)
    (hlen : stN s ≤ (stX s).length)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    {ε : ℚ} (hε : 0 ≤ ε)
    (hev : EvRun (stMu s) (stD s) ε (stN s)
      ((stMu s, stD s), (toRows (stN s, stX s), ([] : Acc))))
    (h : (pivAns s).1 = false) {dq : ℚ}
    (hbud : 2 * ((stN s : ℚ) * (stN s : ℚ) * ε) ≤ dq) :
    QMCLeafB.ContractM7.PivPsdMargin s dq := by
  have hmain := qf_margin_of_false_eps hlen hε hsym hev h
  intro x
  have h2 := hmain x
  have hnn : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hbud' : ε * (stN s : ℚ) * (stN s : ℚ) ≤ dq / 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right (neg_le_neg hbud') hnn
  show -(dq / 2) * (∑ i, x i ^ 2)
    ≤ qf (QMCLeafB.PivExact.matOf (stN s) (stX s)) x
  linarith [h2, hmul]

/-- **The exact-run gate: no rounding anywhere on the run.**  `EvRun mu d 0` says the descent's own
normalizations were all the identity, so its trajectory *is* the exact rational LDLᵀ trajectory. -/
theorem psd_of_exactRun (s : RSt)
    (hlen : stN s ≤ (stX s).length)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    (hev : EvRun (stMu s) (stD s) 0 (stN s)
      ((stMu s, stD s), (toRows (stN s, stX s), ([] : Acc))))
    (h : (pivAns s).1 = false) :
    QMCLeafB.SepOracle.PSD (QMCLeafB.PivExact.matOf (stN s) (stX s)) := by
  intro x
  have h2 := qf_margin_of_false_eps hlen (le_refl (0 : ℚ)) hsym hev h x
  simpa using h2

/-- **The campaign tolerance, unconditionally in `dq`, on a rounding-free run.**  No grid bound, no
box bound: the certificate is the run-time check `EvRun mu d 0` (verifiable by `EvRunB`). -/
theorem pivPsdMargin_of_exactRun (s : RSt)
    (hlen : stN s ≤ (stX s).length)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    (hev : EvRun (stMu s) (stD s) 0 (stN s)
      ((stMu s, stD s), (toRows (stN s, stX s), ([] : Acc))))
    (h : (pivAns s).1 = false) {dq : ℚ} (hdq : 0 ≤ dq) :
    QMCLeafB.ContractM7.PivPsdMargin s dq :=
  QMCLeafB.PivExact.margin_of_psd hdq (psd_of_exactRun s hlen hsym hev h)

/-! ## 8.  Two consequences: the exchange rate, and the non-vacuity anchor

The second is deliberately crude — it uses no descent at all — and shows that the clause is
inhabited, so the interest of `pivPsdMargin_of_boxRun` is entirely the exchange rate `2n²/d` versus
the box scale `2μn`. -/

/-- **The grid requirement.**  The sharp tolerance `2n²/d` is below a target `dq` as soon as the
grid denominator dominates `2n²/dq`. -/
theorem sharp_needs_grid {n : ℕ} {d : ℕ} {dq : ℚ} (hd : 0 < d) (hdq : 0 < dq)
    (hgrid : 2 * (n : ℚ) * (n : ℚ) ≤ dq * (d : ℚ)) :
    2 * ((n : ℚ) * (n : ℚ) / (d : ℚ)) ≤ dq := by
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [show 2 * ((n : ℚ) * (n : ℚ) / (d : ℚ)) = 2 * (n : ℚ) * (n : ℚ) / (d : ℚ) by ring,
    div_le_iff₀ hd']
  linarith

/-- **Brick 1 at a target tolerance, with the grid condition explicit.**  This is the interface the
`records-zip` brick consumes: the snapped test certifies `PivPsdMargin s dq` as soon as the state's
grid dominates `2n²/dq`.  At the campaign's `dqShallow` and `gridOf n = (n+1)^4` that condition is
false — which is exactly `ContractM7.pivFSpec_false_campaign`; the repair is the grid. -/
theorem pivPsdMargin_of_tolerance (s : RSt)
    (hlen : stN s ≤ (stX s).length) (hd : 0 < stD s)
    (hsym : ∀ i j, QMCLeafB.PivExact.matOf (stN s) (stX s) i j
      = QMCLeafB.PivExact.matOf (stN s) (stX s) j i)
    (hbox : BoxRun (stMu s) (stN s)
      ((stMu s, stD s), (toRows (stN s, stX s), ([] : Acc))))
    (h : (pivAns s).1 = false) {dq : ℚ} (hdq : 0 < dq)
    (hgrid : 2 * (stN s : ℚ) * (stN s : ℚ) ≤ dq * (stD s : ℚ)) :
    QMCLeafB.ContractM7.PivPsdMargin s dq := by
  have hsharp := pivPsdMargin_of_boxRun s hlen hd hsym hbox h
  have hδ : 2 * ((stN s : ℚ) * (stN s : ℚ) / (stD s : ℚ)) ≤ dq :=
    sharp_needs_grid hd hdq hgrid
  intro x
  have h2 := hsharp x
  have hnn : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right (neg_le_neg (by linarith : 2 * ((stN s : ℚ) * (stN s : ℚ)
    / (stD s : ℚ)) / 2 ≤ dq / 2)) hnn
  linarith [h2, hmul]

/-- **The unconditional form is refuted** (banked: `ContractM7.pivFSpec_false`).  For every
`δ < 4/1053` there is a state of the campaign's own grid and box whose snapped descent answers `false`
although the block has a violated direction of size `2/81` at norm squared `13` — so no theorem of the
shape `∀ s, (pivAns s).1 = false → PivPsdMargin s δ` can close the campaign tolerance
`dqShallow < 1/360000`.  What *is* attainable is the conditional form: `pivPsdMargin_of_measured`
(measured radius) and `pivPsdMargin_of_exactRun` (round-free gate, every `δ ≥ 0`). -/
theorem no_unconditional_campaign_margin {dq : ℚ} (h : dq < 4 / 1053) :
    ¬ (∀ s : RSt, (pivAns s).1 = false → QMCLeafB.ContractM7.PivPsdMargin s dq) :=
  QMCLeafB.ContractM7.pivFSpec_false h

/-- **The crude anchor.**  With the state's block inside the box `[-μ, μ]`, the margin clause holds
at `δ = 2μn` with no use of the descent at all. -/
theorem pivPsdMargin_of_entryBound {n : ℕ} {Xs : List ℚ} {mu : ℚ}
    (hbox : ∀ i j : Fin n, |QMCLeafB.PivExact.matOf n Xs i j| ≤ mu) :
    ∀ x : Fin n → ℚ,
      -(mu * (n : ℚ)) * (∑ i, x i ^ 2)
        ≤ qf (QMCLeafB.PivExact.matOf n Xs) x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro x
    simp [qf, dotProduct]
  · have hmu : 0 ≤ mu := le_trans (abs_nonneg _) (hbox ⟨0, hn⟩ ⟨0, hn⟩)
    intro x
    have hb := abs_qf_le_of_entrywise_le (QMCLeafB.PivExact.matOf n Xs) x hbox hmu
    have hneg := neg_abs_le (qf (QMCLeafB.PivExact.matOf n Xs) x)
    linarith [hneg, hb]

/-! ## 9.  Non-vacuity: a concrete state where the whole hypothesis chain holds

The `BoxRun` tracker is not an empty hypothesis and the margin clause is not an empty conclusion:
at the `1 × 1` state `stX = [1]`, `mu = 2`, `d = 4` the descent's Schur continuation is the empty
block (so the tracker holds outright), its answer is `false`, and the theorem produces the margin at
`δ = 2·1²/4 = 1/2`.  (The matrix is `!![1]`, so the clause reads `-(1/4)·x₀² ≤ x₀²`.) -/

theorem toRows_one : toRows (1, [1]) = ([[1]] : Rows) := by
  simp [toRows, idxs, rowOf, entV]

theorem boxRun_one : BoxRun (2 : ℚ) 1 ((2, 4), ([[1]], ([] : Acc))) := by
  simp [BoxRun, NrmBox, schurRows, dropRows, headTail, headRowD]

theorem runPivL_one :
    (runPivL ((2, 4), (toRows (1, [1]), ([] : Acc)))).1 = false := by
  have htr : toRows (1, [1]) = ([[1]] : Rows) := toRows_one
  simp only [runPivL]
  rw [htr]
  rw [show ([[1]] : Rows).length = 1 from rfl]
  rw [runPivLFuel_succ]
  have h1 : ¬ List.isEmpty ([[1]] : Rows) = true := by simp
  have h2 : ¬ piv ([[1]] : Rows) < 0 := by simp [piv, headRowD]
  have h3 : ¬ piv ([[1]] : Rows) = 0 := by simp [piv, headRowD]
  rw [pivStepL_schur 2 4 ([[1]] : Rows) ([] : Acc) h1 h2 h3]
  rfl

/-- **The brick, instantiated.**  `PivPsdMargin` holds at the concrete state `stX = [1]`,
`mu = 2`, `d = 4`, at `δ = 1/2`. -/
theorem simpleState_margin :
    QMCLeafB.ContractM7.PivPsdMargin (mkSt 1 [1] [1] 0 2 4 [] []) (2 * ((1 : ℚ) * 1 / 4)) := by
  refine pivPsdMargin_of_boxRun (mkSt 1 [1] [1] 0 2 4 [] []) ?_ ?_ ?_ ?_ ?_
  · show 1 ≤ ([1] : List ℚ).length
    simp
  · show (0 : ℕ) < 4
    omega
  · show ∀ i j : Fin 1,
      QMCLeafB.PivExact.matOf 1 [1] i j = QMCLeafB.PivExact.matOf 1 [1] j i
    intro i j
    simp [QMCLeafB.PivExact.matOf, entV]
  · show BoxRun (2 : ℚ) 1 ((2, 4), (toRows (1, [1]), ([] : Acc)))
    rw [toRows_one]
    exact boxRun_one
  · show (runPivL ((2, 4), (toRows (1, [1]), ([] : Acc)))).1 = false
    exact runPivL_one

/-- **The campaign tolerance, on a concrete state, with no grid condition.**  The same state as
`simpleState_margin`, but through the rounding-free gate: `dq` is at the campaign's own scale
(`1/400000 ≈ dqShallow`), five orders of magnitude below the sharp grid tolerance `2n²/d = 1/2` of
`pivPsdMargin_of_boxRun` at `d = 4`.  The gate `EvRun 2 4 0` holds because the `1 × 1` block's only
Schur continuation is the empty block (`schurRows [[1]] = []`), i.e. the descent is round-free. -/
theorem simpleState_margin_campaign :
    QMCLeafB.ContractM7.PivPsdMargin (mkSt 1 [1] [1] 0 2 4 [] []) (1 / 400000) := by
  refine pivPsdMargin_of_exactRun (mkSt 1 [1] [1] 0 2 4 [] []) ?_ ?_ ?_ ?_ ?_
  · show 1 ≤ ([1] : List ℚ).length
    simp
  · show ∀ i j : Fin 1,
      QMCLeafB.PivExact.matOf 1 [1] i j = QMCLeafB.PivExact.matOf 1 [1] j i
    simp [QMCLeafB.PivExact.matOf, entV]
  · show EvRun (2 : ℚ) 4 0 1 ((2, 4), (toRows (1, [1]), ([] : Acc)))
    rw [toRows_one]
    simp [EvRun, EvOk, NrmErrRows, schurRows, dropRows, headTail, headRowD, nrmQ_zero]
  · show (runPivL ((2, 4), (toRows (1, [1]), ([] : Acc)))).1 = false
    exact runPivL_one
  · norm_num

end QMCLeafB.LdltCertM5

/-! ## 9.  Axiom audit -/

#print axioms QMCLeafB.LdltCertM5.sum_sq_tail_le
#print axioms QMCLeafB.LdltCertM5.schur_split_qf
#print axioms QMCLeafB.LdltCertM5.schur_step_radius
#print axioms QMCLeafB.LdltCertM5.drop_step_radius
#print axioms QMCLeafB.LdltCertM5.nrmQ_zero
#print axioms QMCLeafB.LdltCertM5.nrmRows_eq_map
#print axioms QMCLeafB.LdltCertM5.nrmQ_error_of_box
#print axioms QMCLeafB.LdltCertM5.evRun_of_box
#print axioms QMCLeafB.LdltCertM5.getD_le_of_all
#print axioms QMCLeafB.LdltCertM5.box_le_of_all
#print axioms QMCLeafB.LdltCertM5.nrmBox_of_nrmBoxB
#print axioms QMCLeafB.LdltCertM5.boxRun_of_boxRunB
#print axioms QMCLeafB.LdltCertM5.pivStepL_empty
#print axioms QMCLeafB.LdltCertM5.pivStepL_neg
#print axioms QMCLeafB.LdltCertM5.pivStepL_zeroCut
#print axioms QMCLeafB.LdltCertM5.pivStepL_drop
#print axioms QMCLeafB.LdltCertM5.pivStepL_schur
#print axioms QMCLeafB.LdltCertM5.runPivLFuel_inl
#print axioms QMCLeafB.LdltCertM5.runPivLFuel_inr
#print axioms QMCLeafB.LdltCertM5.nextL_inl
#print axioms QMCLeafB.LdltCertM5.nextL_inr
#print axioms QMCLeafB.LdltCertM5.specR_runPivLFuel
#print axioms QMCLeafB.LdltCertM5.qf_margin_of_false
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_boxRun
#print axioms QMCLeafB.LdltCertM5.sharp_needs_grid
#print axioms QMCLeafB.LdltCertM5.NrmErrB
#print axioms QMCLeafB.LdltCertM5.EvRunB
#print axioms QMCLeafB.LdltCertM5.getD_err_of_all
#print axioms QMCLeafB.LdltCertM5.errRows_of_all
#print axioms QMCLeafB.LdltCertM5.evRun_of_evRunB
#print axioms QMCLeafB.LdltCertM5.no_unconditional_campaign_margin
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance
#print axioms QMCLeafB.LdltCertM5.qf_margin_of_false_eps
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_measured
#print axioms QMCLeafB.LdltCertM5.psd_of_exactRun
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_exactRun
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_entryBound
#print axioms QMCLeafB.LdltCertM5.toRows_one
#print axioms QMCLeafB.LdltCertM5.boxRun_one
#print axioms QMCLeafB.LdltCertM5.runPivL_one
#print axioms QMCLeafB.LdltCertM5.simpleState_margin
#print axioms QMCLeafB.LdltCertM5.simpleState_margin_campaign


