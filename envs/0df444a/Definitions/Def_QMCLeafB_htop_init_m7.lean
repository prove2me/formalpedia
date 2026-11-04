-- Prove2me | Definitions.Def_QMCLeafB_htop_init_m7
-- name    : QMCLeafB_htop_init_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:19:49.936624+00:00
-- url     : https://prove2.me/theorems/76ae5b1e-007b-4af3-af28-893d4903008e
-- title:
--   QMCLeafB htop_init_m7
-- statement:
--   # leaf B phase 14 — `htop`, part 2: `fvR` vanishes at `init0` (swarm `smw17fqzz`, m7, d14)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_RStInit
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 14 — `htop`, part 2: `fvR` vanishes at `init0` (swarm `smw17fqzz`, m7, d14)

The `htop` route posted in `Check_htop_m7.lean` needs one number at the initial state:

    fvR (init0 (noTape G t)) = 0

because then the round's `ok` test `fvR s ≤ stT s + εw` fires on the top slice (`0 ≤ t + εw`), and
`Htop.verdict_of_first_ok_of_one` turns that into `htop`.

This file proves it.  `fvR s = frobV (stN s, (stA s, stX s))` is the double sum

    ∑_{i<n} ∑_{j<n} A[i·n+j] · X[i·n+j]

over the two row-major codes, and at `init0` the two codes are diagonal-complementary:

* `stA (init0 p)` codes `wMatQ G` (`RStInit.stA_correct`), whose **diagonal vanishes**;
* `stX (init0 p)` codes `initShapeOf n (MOf n) = (MOf n)⁻¹ • 1` (`RStInit.stX_correct`), which is
  **diagonal**.

So every one of the `n²` products is zero.  The lemma is stated for an arbitrary pair of codes with
those two properties (`frobV_eq_zero_of_orth`), so it is reusable for any later state whose weight
code and shape code are diagonal-complementary.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.HtopInit

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-! ## 1.  Sums of zeros -/

theorem list_sum_eq_zero {l : List ℚ} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.sum_cons, ih (fun x hx => h x (List.mem_cons_of_mem a hx)),
        h a (List.mem_cons_self ..)]
      ring

theorem list_sum_map_eq_zero {α : Type} {l : List α} {f : α → ℚ}
    (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 :=
  list_sum_eq_zero (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact h y hy)

/-! ## 2.  `frobV` of a diagonal-complementary pair of codes -/

/-- The index range of `frobV` at a code of length `n * n` is `List.range n`. -/
theorem idxs_eq_range {n : ℕ} {X : List ℚ} (hX : X.length = n * n) :
    QMCLeafB.RoundProgram.idxs (n, X) = List.range n := by
  simp only [QMCLeafB.RoundProgram.idxs, List.length_take, hX,
    Nat.min_eq_left (Nat.le_mul_self n)]

/-- **`frobV` vanishes when the two codes are diagonal-complementary.** -/
theorem frobV_eq_zero_of_orth {n : ℕ} {A X : List ℚ}
    (hX : X.length = n * n)
    (h : ∀ i j : Fin n, MatQ.entry n A i j * MatQ.entry n X i j = 0) :
    QMCLeafB.RoundProgram.frobV (n, (A, X)) = 0 := by
  unfold QMCLeafB.RoundProgram.frobV
  rw [idxs_eq_range hX]
  refine list_sum_map_eq_zero (fun i hi => ?_)
  have hi' : i < n := List.mem_range.mp hi
  refine list_sum_map_eq_zero (fun j hj => ?_)
  have hj' : j < n := List.mem_range.mp hj
  exact h ⟨i, hi'⟩ ⟨j, hj'⟩

/-! ## 3.  The two codes at `init0` -/

/-- The weight code's diagonal vanishes. -/
theorem wMatQ_diag (G : QuantumMaxCutEnergy.Input) (i : Fin G.n) :
    QMCLeafB.RStInit.wMatQ G i i = 0 := by
  rw [QMCLeafB.RStInit.wMatQ_apply]
  simp

/-- The shape code is diagonal. -/
theorem initShapeOf_offdiag (N : ℕ) (M : ℚ) {i j : Fin N} (h : i ≠ j) :
    QMCLeafB.Boundary.initShapeOf N M i j = 0 := by
  rw [QMCLeafB.Boundary.initShapeOf, Matrix.smul_apply, Matrix.one_apply_ne h]
  ring

/-- **`fvR` vanishes at the tape-free initial state.**  This is the number `htop` needs. -/
theorem fvR_init0 (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.RoundProgram.fvR
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = 0 := by
  have hA := QMCLeafB.RStInit.stA_correct_noTape G t
  have hX := QMCLeafB.RStInit.stX_correct (QMCLeafB.FinalStroke.noTape G t)
  have hN : QMCLeafB.RoundProgram.stN
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) = G.n :=
    QMCLeafB.RStInit.stN_init0 _
  have hAlen : (QMCLeafB.RoundProgram.stA
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))).length = G.n * G.n := hA.1
  have hXlen : (QMCLeafB.RoundProgram.stX
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))).length = G.n * G.n := by
    rw [hX.1, hN]
  have hXlen' : (QMCLeafB.RoundProgram.stX
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))).length
        = QMCLeafB.RoundProgram.stN
            (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))
          * QMCLeafB.RoundProgram.stN
              (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t)) := by
    rw [hXlen, hN]
  rw [QMCLeafB.RoundProgram.fvR, hN]
  refine frobV_eq_zero_of_orth hXlen (fun i j => ?_)
  have h1 : MatQ.entry G.n (QMCLeafB.RoundProgram.stA
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) i j
      = QMCLeafB.RStInit.wMatQ G i j := hA.2 i j
  have h2 : MatQ.entry G.n (QMCLeafB.RoundProgram.stX
      (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) i j
      = QMCLeafB.Boundary.initShapeOf G.n (QMCLeafB.InitVerdict.MOf G.n) i j := by
    rw [hN] at hX
    exact hX.2 i j
  rw [h1, h2]
  by_cases hij : i = j
  · subst hij
    rw [wMatQ_diag]
    ring
  · rw [initShapeOf_offdiag _ _ hij]
    ring

end QMCLeafB.HtopInit

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.HtopInit.list_sum_eq_zero
#print axioms QMCLeafB.HtopInit.idxs_eq_range
#print axioms QMCLeafB.HtopInit.frobV_eq_zero_of_orth
#print axioms QMCLeafB.HtopInit.wMatQ_diag
#print axioms QMCLeafB.HtopInit.initShapeOf_offdiag
#print axioms QMCLeafB.HtopInit.fvR_init0


