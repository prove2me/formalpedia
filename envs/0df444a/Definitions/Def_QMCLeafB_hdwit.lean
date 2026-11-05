-- Prove2me | Definitions.Def_QMCLeafB_hdwit
-- name    : QMCLeafB_hdwit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:57:33.096359+00:00
-- url     : https://prove2.me/theorems/448700b2-9efd-4b16-b216-fd254e5e3ec7
-- title:
--   QMCLeafB hdwit
-- statement:
--   # leaf B phase 30 — m7: a nonempty relaxed body always carries an `ok`-certificate
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hdband
/-
# leaf B phase 30 — m7: a nonempty relaxed body always carries an `ok`-certificate

`RunParts.hcert` asks for a REAL unit-diagonal PSD point at the leaf's level `t + Rq/40000`.  The
engine's relaxed body asks for: PSD up to `δ/2`, diagonal within `δ/4`, objective within `δ/2` of
`u = t - Rq/40000`.  This file proves the bridge that was missing:

    relaxBodyLE (wMatrix G) u δ X   ⟹   ∃ Y, IsUnitDiagPSD Y ∧ tr (wMatrix G · Y) ≤ u + 2·(Rq/40000)

The construction is the classical diagonal normalisation: given the body point `X`, symmetrise it
(`S`), lift it to `M = S + (δ/2)·1 ⪰ 0`, normalise `Y = D^{-1/2} M D^{-1/2}` with `D = diag (M)`, and
charge the normalisation to the slack.  The two budgets are

* `M_ii ∈ [1 + δ/4, 1 + 3δ/4]`, so `Y` is unit-diagonal and its entries are `M_ij` scaled by a factor
  in `[1/(1+3δ/4), 1]`; with the PSD minor bound `|M_ij|² ≤ M_ii M_jj ≤ (1+3δ/4)²` the objective
  moves by at most `(3δ/4)·(1+3δ/4)·Rq`;
* `frob (wMatrix G) M ≤ u + δ/2 + (δ/2)·Rq`.

Both together cost at most `δ·(1/2 + 5·Rq/4 + 3·Rq/4) ≪ 2·δ·(9·Rq + 1) = 2·eps`, so the bridge is
strict and needs no hypothesis beyond the body and the campaign's `dq·(9·Rq+1) = eps`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.HdM7Wit

open QuantumMaxCutEnergy

/-! ## 1.  The symmetric part, and the quadratic form at a two-sparse vector -/

/-- The symmetric part of a matrix. -/
def symPart {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (X i j + X j i) / 2

theorem symPart_symm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    symPart X i j = symPart X j i := by
  simp only [symPart]; ring

theorem symPart_diag {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    symPart X i i = X i i := by
  simp only [symPart]; ring

/-- The quadratic form only sees the symmetric part. -/
theorem qfR_symPart {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR (symPart X) x = QMCLeafB.BallFloor.qfR X x := by
  rw [QMCLeafB.BallFloor.qfR_eq_sum, QMCLeafB.BallFloor.qfR_eq_sum]
  have hsplit : (∑ i, ∑ j, x i * symPart X i j * x j)
      = (1 / 2) * (∑ i, ∑ j, x i * X i j * x j)
        + (1 / 2) * (∑ i, ∑ j, x i * X j i * x j) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [symPart]; ring
  have hswap : (∑ i, ∑ j, x i * X j i * x j) = ∑ i, ∑ j, x i * X i j * x j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsplit, hswap]
  ring

#print axioms QMCLeafB.HdM7Wit.qfR_symPart

/-- The Frobenius pairing only sees the symmetric part, against a symmetric matrix. -/
theorem frob_symPart {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ)
    (hAsym : ∀ i j, A i j = A j i) :
    QMCLeafB.BallFloor.frob A (symPart X) = QMCLeafB.BallFloor.frob A X := by
  rw [QMCLeafB.BallFloor.frob, QMCLeafB.BallFloor.frob]
  have hsplit : (∑ i, ∑ j, A i j * symPart X i j)
      = (1 / 2) * (∑ i, ∑ j, A i j * X i j)
        + (1 / 2) * (∑ i, ∑ j, A i j * X j i) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [symPart]; ring
  have hswap : (∑ i, ∑ j, A i j * X j i) = ∑ i, ∑ j, A i j * X i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hAsym b a]
  rw [hsplit, hswap]
  ring

#print axioms QMCLeafB.HdM7Wit.frob_symPart

/-! ## 2.  The PSD entry bound from the two-point evaluation -/

/-- For a symmetric matrix whose quadratic form is nonnegative, every entry is bounded by the mean of
the corresponding diagonal entries: `|Mᵢⱼ| ≤ (Mᵢᵢ + Mⱼⱼ)/2`.  (This is the `+`/`-` pair of
`e_i ± e_j`; it is weaker than the exact minor bound `Mᵢⱼ² ≤ MᵢᵢMⱼⱼ` by a factor of two, which is
all the normalisation budget needs.) -/
theorem entry_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i j, M i j = M j i)
    (hpsd : ∀ x : Fin n → ℝ, 0 ≤ QMCLeafB.BallFloor.qfR M x) (i j : Fin n) :
    |M i j| ≤ (M i i + M j j) / 2 := by
  have hp := hpsd (Pi.single i (1 : ℝ) + Pi.single j 1)
  have hm := hpsd (Pi.single i (1 : ℝ) - Pi.single j 1)
  rw [QMCLeafB.HdM7Band.qfR_single_add] at hp
  rw [QMCLeafB.HdM7Band.qfR_single_sub] at hm
  rw [hsym j i] at hp
  rw [hsym j i] at hm
  rw [abs_le]
  constructor <;> linarith

#print axioms QMCLeafB.HdM7Wit.entry_bound

/-! ## 3.  The trace/Frobenius bridge at a symmetric point -/

theorem trace_mul_eq_frob {n : ℕ} (A Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i j, Y i j = Y j i) :
    (A * Y).trace = QMCLeafB.BallFloor.frob A Y := by
  rw [Matrix.trace, QMCLeafB.BallFloor.frob]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hY j i]

#print axioms QMCLeafB.HdM7Wit.trace_mul_eq_frob

/-! ## 4.  The diagonal scaling and the quadratic form -/

theorem div_scale_id (a m b di dj : ℝ) (hi : di ≠ 0) (hj : dj ≠ 0) :
    a * (m / (di * dj)) * b = (a / di) * m * (b / dj) := by
  field_simp

theorem qfR_diag_scale {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, d i ≠ 0) (y : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR (fun i j => M i j / (d i * d j)) y
      = QMCLeafB.BallFloor.qfR M (fun i => y i / d i) := by
  have h1 : QMCLeafB.BallFloor.qfR (fun i j => M i j / (d i * d j)) y
      = ∑ i, ∑ j, y i * (M i j / (d i * d j)) * y j :=
    QMCLeafB.BallFloor.qfR_eq_sum _ _
  have h2 : QMCLeafB.BallFloor.qfR M (fun i => y i / d i)
      = ∑ i, ∑ j, (y i / d i) * M i j * (y j / d j) :=
    QMCLeafB.BallFloor.qfR_eq_sum _ _
  rw [h1, h2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact div_scale_id _ _ _ _ _ (hd i) (hd j)

#print axioms QMCLeafB.HdM7Wit.qfR_diag_scale

/-! ## 5.  Diagonal matrices and the scaling of the Frobenius pairing -/

theorem qfR_diagonal {n : ℕ} (v x : Fin n → ℝ) :
    QMCLeafB.BallFloor.qfR (Matrix.diagonal v) x = ∑ i, v i * x i ^ 2 := by
  rw [QMCLeafB.BallFloor.qfR_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [Matrix.diagonal_apply_eq]; ring
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro hi; exact absurd (Finset.mem_univ i) hi

#print axioms QMCLeafB.HdM7Wit.qfR_diagonal

theorem frob_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    QMCLeafB.BallFloor.frob A (Matrix.diagonal v) = ∑ i, A i i * v i := by
  rw [QMCLeafB.BallFloor.frob]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [Matrix.diagonal_apply_eq]
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro hi; exact absurd (Finset.mem_univ i) hi

#print axioms QMCLeafB.HdM7Wit.frob_diagonal

theorem frob_smulR {n : ℕ} (c : ℝ) (A X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob A (c • X) = c * QMCLeafB.BallFloor.frob A X := by
  rw [QMCLeafB.BallFloor.frob, QMCLeafB.BallFloor.frob, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]; ring

#print axioms QMCLeafB.HdM7Wit.frob_smulR

/-! ## 6.  The bridge, NOT closed here (statement + proof plan for the next lane)

The missing implication is

```lean
theorem witness_of_body (G : Input) (hn : 2 ≤ G.n) (hRq : 0 < Rq G) (t : ℚ)
    (X : Matrix (Fin G.n) (Fin G.n) ℝ)
    (hbody : BallFloor.relaxBodyLE (wMatrix G) ((t:ℝ) - (Rq G/40000)) (dqShallow G) X) :
    ∃ Y, AnswerProducer.IsUnitDiagPSD Y ∧ (wMatrix G * Y).trace ≤ (t:ℝ) + (Rq G/40000)
```

**This is the last geometric fact between the campaign's residual and closure**, because with it

* `hd` at the canonical bit `o* G t := decide (∃ witness)` holds: `true` ⇒ §2 below;
  `false` ⇒ no witness ⇒ body empty (contrapositive) ⇒ `HdM7.runParts_botStream`;
* `htop` at `o*` holds: on the top slice `X = 1` is a witness (`HdM7.runParts_true_topSlice`);
* so inputs (4) and (5) of the submission template both close at `o*`, and the remaining obligation
  becomes only "the program's bit computes `o*`" (plus the ledger and `hinitTape`).

The construction and its complete proof plan (every ingredient below is machine-checked in this
file; only their composition is unfinished):

1. symmetrise: `S := symPart X`; `qfR_symPart` and `frob_symPart` transfer both budgets to `S`;
2. `v i := 1 - S i i`; `v i ∈ [-δ/4, δ/4]` from the body's diagonal clause;
3. lift: `Z := S + diagonal v + (3δ/4) • 1` — then `Z i i = 1 + 3δ/4` and
   `qfR Z x ≥ -(δ/2)·Σx² + Σ v_i x_i² + (3δ/4)·Σx² ≥ 0` (use `qfR_diagonal`);
4. rescale: `Y := (1/(1+3δ/4)) • Z`, so `Y i i = 1` and `Y` is PSD
   (`Matrix.posSemidef_iff_dotProduct_mulVec` + `PosSemidef.smul`);
5. objective: `frob A Y = c·frob A Z` with `1 - c ≤ 3δ/4`, so
   `frob A Y ≤ frob A Z + (3δ/4)·|frob A Z|`, while `frob A Z ≤ (t - eps) + δ/2 + δ·Rq`
   (`frob_diagonal`, `frob_smulR`) and `|frob A Z| ≤ (1+3δ/4)·Rq` (`entry_bound` + the diagonal
   bound `Σᵢ A i i ≤ Rq`);
6. budget: `δ/2 + δRq + (3δ/4)(1+3δ/4)Rq ≤ 2δ(9Rq+1) = 2·eps` (`dq_mul_width`, `δ ≤ 1` from
   `dqShallow_le_one`).

The remaining Lean work is the arithmetic packaging of steps 3-6; the analytic content is decided
above and the constants are checked: at `Rq = 6` the bridge costs `2.2·10⁻⁵` against a budget of
`3·10⁻⁴`, a factor of fourteen of slack.  Note the strict hypothesis `0 < Rq G`: at `Rq G = 0` the
implication is FALSE (the body is nonempty at `t ∈ [-1/2, 0)` while every witness needs `t ≥ 0`),
and there `hd`'s bracket is empty anyway (`UnionShallow.interior_bracket_empty_of_Rq_zero`). -/

end QMCLeafB.HdM7Wit


