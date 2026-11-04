-- Prove2me | Definitions.Def_QMCLeafB_pinchbudget
-- name    : QMCLeafB_pinchbudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:22:17.193543+00:00
-- url     : https://prove2.me/theorems/69f23af2-a00f-4d0b-a634-fb0dba57ee9c
-- title:
--   QMCLeafB pinchbudget
-- statement:
--   # leaf B phase 18 — brick `pinchbudget` (swarm `smw1i2drp`, member m5, direction d5, round 2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_inhabit_m5
/-
# leaf B phase 18 — brick `pinchbudget` (swarm `smw1i2drp`, member m5, direction d5, round 2)

The judge's closing advice on direction d5 was to keep the pinch's per-round cost
`(dq/4)·|c ⪝ p_j|` charged inside the state/trace budget, "the budget survives since the body's
trace is bounded regardless".  This file does exactly that bookkeeping and, in doing it, tells the
swarm which slot of the residual is *bookkeeping* and which is *analysis*:

* §1 `flat_castMat_smul` — `flat` is linear in the centre, so the drift block sees the lowering.
* §2 `drift_shift` (ℚ and ℝ) — **the charge identity**.  At the boundary-lowered centre
  `(1 − δ/4) • Q` the drift pairing is the drift at `Q` plus exactly `(δ/4)·(c ⪝ Q)`:

      c ⪝ (Cat − flat ((1−δ/4)•Q)) = c ⪝ (Cat − flat Q) + (δ/4)·(c ⪝ flat Q).

  So a drift inequality at the pinch costs `(δ/4)·|c ⪝ flat Q|` against the inequality at the body
  point — the per-round charge the work notes ask to carry in `hstatec`/`hTrc`.
* §3 `trace_smul_diag` — the trace ledger of the lowering: `trace ((1−δ/4)•Q) = (1−δ/4)·trace Q`.
* §4 `hTrc_of_pinch_diag` — **`hTrc` is not independent analysis**: it is implied by the pointwise
  pinch `∀ i, (cX k)ᵢᵢ = 1 − dq/4` (the equality that `hdiagc` + `RelaxMem.diag_near` forces,
  phase-17 `Check_obstruction_m1`).  So item 2's trace slot is discharged by the banked pinch.
* §5 `hTrc_not_from_diag_near` — the honest limit, recorded so nobody re-derives a false shortcut:
  `RelaxMem.diag_near` at the *lowered* centre does NOT imply `hTrc` (the identity witness misses
  by `n·δ/4`).  Only the pinch equality buys the budget.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; axiom audits at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.PinchBudgetM5

open QuantumMaxCutEnergy

/-! ## 1.  `flat` is linear in the centre -/

theorem flat_castMat_smul {n : ℕ} (c : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (c • Q))
      = ((c : ℚ) : ℝ) • QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q) := by
  funext k
  simp [QMCLeafB.AnswerProducer.flat, QMCLeafB.SepOracle.castMat, Matrix.smul_apply, smul_eq_mul]

/-! ## 2.  The charge identity for the boundary lowering -/

theorem drift_shift {N : ℕ} (c Cat Qf : Fin N → ℚ) (δ : ℚ) :
    c ⬝ᵥ (Cat - (1 - δ / 4) • Qf) = c ⬝ᵥ (Cat - Qf) + (δ / 4) * (c ⬝ᵥ Qf) := by
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem drift_shift_real {N : ℕ} (c Cat Qf : Fin N → ℝ) (δ : ℝ) :
    c ⬝ᵥ (Cat - (1 - δ / 4) • Qf) = c ⬝ᵥ (Cat - Qf) + (δ / 4) * (c ⬝ᵥ Qf) := by
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The same charge, in the form of an implication: a drift inequality at the body point, paid the
pinch's `(δ/4)(c ⪝ Q)`, gives the drift inequality at the lowered centre. -/
theorem drift_at_pinch {N : ℕ} (c Cat Qf : Fin N → ℚ) (δ b : ℚ)
    (h : c ⬝ᵥ (Cat - Qf) + (δ / 4) * (c ⬝ᵥ Qf) ≤ b) :
    c ⬝ᵥ (Cat - (1 - δ / 4) • Qf) ≤ b := by
  rw [drift_shift]
  exact h

/-! ## 3.  The trace ledger of the lowering -/

theorem trace_smul_diag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) :
    ∑ i, (c • Q) i i = c * ∑ i, Q i i := by
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-! ## 4.  `hTrc` is the pinch diagonal, not independent analysis -/

theorem hTrc_of_pinch_diag {n : ℕ} (cX : Matrix (Fin n) (Fin n) ℚ) {δ : ℚ}
    (hdiag : ∀ i, cX i i = 1 - δ / 4) :
    ∑ i, cX i i ≤ (n : ℚ) * (1 - δ / 4) := by
  have h : ∑ i, cX i i = (n : ℚ) * (1 - δ / 4) := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h]

/-- The pointwise pinch is exactly what `hdiagc` plus `RelaxMem.diag_near` delivers (the phase-17
obstruction): with the diagonal pinned at the boundary, `hTrc` and equality coincide. -/
theorem hTrc_of_pinch_diag_eq {n : ℕ} (cX : Matrix (Fin n) (Fin n) ℚ) {δ : ℚ}
    (hdiag : ∀ i, cX i i = 1 - δ / 4) :
    ∑ i, cX i i = (n : ℚ) * (1 - δ / 4) := by
  simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 5.  The honest limit: `diag_near` does not buy the trace budget

The unit matrix has `|(1)ᵢᵢ − 1| = 0 ≤ δ/4` — the certificate's `diag_near` is satisfied at the
*lowered* centre for any `δ > 0` — yet its trace is `n > n(1 − δ/4)`.  So no argument can derive
`hTrc` from `diag_near`; the pinch equality of §4 is the only route, and the deficit it closes is
`n·δ/4`. -/

theorem hTrc_not_from_diag_near {n : ℕ} (hn : 0 < n) {δ : ℚ} (hδ : 0 < δ) :
    ¬ ∑ i, (1 : Matrix (Fin n) (Fin n) ℚ) i i ≤ (n : ℚ) * (1 - δ / 4) := by
  have hone : ∑ i, (1 : Matrix (Fin n) (Fin n) ℚ) i i = (n : ℚ) := by
    simp only [Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hcard : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  rw [hone]
  intro h
  nlinarith

end QMCLeafB.PinchBudgetM5

/-! ## Axiom audit -/

#print axioms QMCLeafB.PinchBudgetM5.flat_castMat_smul
#print axioms QMCLeafB.PinchBudgetM5.drift_shift
#print axioms QMCLeafB.PinchBudgetM5.drift_shift_real
#print axioms QMCLeafB.PinchBudgetM5.drift_at_pinch
#print axioms QMCLeafB.PinchBudgetM5.trace_smul_diag
#print axioms QMCLeafB.PinchBudgetM5.hTrc_of_pinch_diag
#print axioms QMCLeafB.PinchBudgetM5.hTrc_not_from_diag_near


