-- Prove2me | Definitions.Def_QMCLeafB_traceBudget_m8
-- name    : QMCLeafB_traceBudget_m8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:23:52.61789+00:00
-- url     : https://prove2.me/theorems/b384b788-cd06-41bf-b47e-807a86dbfa3c
-- title:
--   QMCLeafB traceBudget_m8
-- statement:
--   # leaf B phase 18 — brick `trace-budget` (swarm `smw1i2drp`, member m8, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_obstruction_m1
import Definitions.Def_QMCLeafB_centreCore
/-
# leaf B phase 18 — brick `trace-budget` (swarm `smw1i2drp`, member m8, direction d2)

Residual 2 of the endgame is, verbatim from `QMCLeafB.DriftExact.runParts_at_interior_exact`:

    hTrc    : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 − P.dq / 4)
    hdriftc : ∀ k, ok k = false → c_k ⪝ (Cat k − flat (cX k)) ≤ marg_k / 2
    hdriftd : ∀ k, ok k = false → dOne ⪝ (Cat k − flat (cX k)) ≤ 0

This file pins that slot at the **pinch-consistent centre** `cX k = (1 − dq/4) • Q_k`, the only
admissible boundary lowering (`AuditM1.abs_boundary_smul_sub_one` needs `Q_ii ≥ 1`; `(1 − dq/2)` is
the wrong scale, `CentreClosure.relaxMem_scaled_false`).

## What is proved here (compiled, axiom-audited)

* **§1** the diagonal-sum algebra and the *equivalence*
  `hTrc` at the boundary centre ⟺ `∑ i (Q k) i i ≤ n` (`hTrc_boundary_iff`).
* **§2** a machine-checked counterexample showing that `hTrc` is **not** a consequence of the
  ok-branch certificate: at `n = 2`, `dq = 1`, `Q = (5/4)•1` is a legitimate `RelaxMem` point at
  `A = 0`, `u = 0` (its diagonal sits at the very top of `diag_near`'s band), yet its boundary
  lowering has trace `15/8 > 3/2 = n(1 − dq/4)` (`diag_near_not_hTrc`).  `RelaxMem.diag_near` only
  gives `Q_ii ≤ 1 + dq/4`, so the base stream needs its own trace budget `tr Q ≤ n`.
* **§3** the pinch at the boundary centre: `hdiagc` there forces `Q_ii ≤ 1`, and `RelaxMem.diag_near`
  at the same lowered centre forces `Q_ii ≥ 1`; together `Q_ii = 1`, hence
  `((1 − dq/4)•Q) i i = 1 − dq/4` exactly and `hTrc` holds **with equality**
  (`pinch_forces_unitDiag`, `hTrc_eq_of_pinch`).  So the two slots are consistent only at the
  boundary, and consistency *is* unit diagonal of the base point.  In particular `hTrc` is redundant
  once `hdiagc` holds at the boundary centre (`hTrc_of_hdiagc_boundary`).
* **§4** the two drift conditions at the boundary centre, with their **exact** shift:
  `dOne ⪝ (Cat − flat ((1 − s)•Q)) = dOne ⪝ (Cat − flat Q) + s · tr Q` and
  `c ⪝ (Cat − flat ((1 − s)•Q)) = c ⪝ (Cat − flat Q) + s · (c ⪝ flat Q)`.
  The lowering *loosens* `hdriftd` by `s · tr Q` (so the trace budget tightens) and shifts `hdriftc`
  by `s · (c ⪝ flat Q)`, which is `≤ 0` for a violated direction (`hdriftc_boundary_of_base`).
  Consequently `hdriftd` at the boundary ⟺ `diagSum (Cat k) ≤ (1 − dq/4) · tr (Q k)`
  (`hdriftd_boundary_iff`): the surviving content of the drift slot is the single scalar
  engine-centre trace budget.
* **§5** the slot, assembled: `hmem` / `hCsym` / `hTrc` discharged from base-stream data and the
  two drift conditions reduced (`trace_budget_slot`).  Residual 2 becomes

      htrcQ : ∀ k, ∑ i, (Q k) i i ≤ n                          -- base-stream trace budget
      hbud  : ∀ k, diagSum (Cat k) ≤ (1 − dq/4) · tr (Q k)     -- engine-centre trace budget
      hcut  : ∀ k, c_k ⪝ (Cat k − flat Q_k) + (dq/4)·(c_k ⪝ flat Q_k) ≤ marg_k/2

  with the two trace budgets collapsing into one scalar inequality at a unit-diagonal base stream
  (`hdriftd_boundary_of_unitDiag`: `diagSum (Cat k) ≤ n·(1 − dq/4)`).
  `trace_budget_slot_paramsKbc2` instantiates the slot at the campaign family
  `UnionShallow.paramsKbc2` (with `dqShallow_lt_four` supplying `dq < 4`), so the three outputs are
  the `hTrc` / `hdriftc` / `hdriftd` arguments of `runParts_at_interior_exact` verbatim.
* **§6** `reduced_residual_inhabited`: the three reduced antecedents are simultaneously satisfiable
  (`n = 2`, `dq = 1/2`, zero engine centre, unit-diagonal base stream) — the reduction is not
  vacuous.

**Not proved here, and not implied by anything above**: `htrcQ`, `hbud` and `hcut`.  These are the
genuine obligations of residual 2 and they are statements about the actual run (the trace of the
accumulated engine centre `Cat k = ∑_{j<k} λ_j • p_j` against the base stream's trace).  §2 shows
`hTrc` does not follow from the ok-branch certificate, so a closing assembly must supply them.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TraceBudgetM8

open QuantumMaxCutEnergy
open QMCLeafB.DriftExact (diagSum)
open QMCLeafB.RunPartsStream (dOne)

/-! ## 1.  Diagonal-sum algebra and the trace bound at the boundary centre -/

theorem diag_sum_smul_rat {n : ℕ} (a : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ) :
    (∑ i, (a • Q) i i) = a * ∑ i, Q i i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.smul_apply, smul_eq_mul]

theorem diag_sum_one_diag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (h : ∀ i, Q i i = 1) :
    (∑ i, Q i i) = (n : ℚ) := by
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The boundary scale `1 − dq/4` is positive exactly when `dq < 4`. -/
theorem boundary_pos {dq : ℚ} (h0 : 0 < dq) (h4 : dq < 4) : (0 : ℚ) < 1 - dq / 4 := by
  rw [sub_pos, div_lt_one (by norm_num : (0 : ℚ) < 4)]
  exact h4

/-- **The trace bound at the boundary centre is exactly a bound on the base point's trace.** -/
theorem hTrc_boundary_iff {n : ℕ} {dq : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    (Q : Matrix (Fin n) (Fin n) ℚ) :
    (∑ i, ((1 - dq / 4) • Q) i i ≤ (n : ℚ) * (1 - dq / 4))
      ↔ (∑ i, Q i i ≤ (n : ℚ)) := by
  rw [diag_sum_smul_rat]
  have hp : (0 : ℚ) < 1 - dq / 4 := boundary_pos h0 h4
  have hkey : (1 - dq / 4) * (n : ℚ) = (n : ℚ) * (1 - dq / 4) := by ring
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h2 := mul_lt_mul_of_pos_left hc hp
    linarith [h2, hkey]
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hp)
    linarith [h2, hkey]

/-- The direction the residual actually consumes. -/
theorem hTrc_boundary_of_trace {n : ℕ} {dq : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    {Q : Matrix (Fin n) (Fin n) ℚ} (h : ∑ i, Q i i ≤ (n : ℚ)) :
    ∑ i, ((1 - dq / 4) • Q) i i ≤ (n : ℚ) * (1 - dq / 4) :=
  (hTrc_boundary_iff h0 h4 Q).2 h

/-- A unit-diagonal base point hits the trace bound **with equality**. -/
theorem hTrc_boundary_eq_of_unitDiag {n : ℕ} {dq : ℚ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i, Q i i = 1) :
    ∑ i, ((1 - dq / 4) • Q) i i = (n : ℚ) * (1 - dq / 4) := by
  rw [diag_sum_smul_rat, diag_sum_one_diag Q h]
  ring

/-! ## 2.  The gap is real: `RelaxMem` does *not* give the trace budget

`Q = (1 + dq/4) • 1` sits at the top of `RelaxMem.diag_near`'s band and is a perfectly good
certificate at `A = 0`, `u = 0`; its boundary lowering is exactly `dq²/16` above the budget. -/

theorem qf_one_eq {n : ℕ} (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (1 : Matrix (Fin n) (Fin n) ℚ) x = ∑ i, x i ^ 2 := by
  simp [QMCLeafB.SepOracle.qf, dotProduct, sq]

theorem relaxMem_top_of_band (n : ℕ) {dq : ℚ} (h0 : 0 < dq) :
    QMCLeafB.RelaxOracle.RelaxMem (0 : Matrix (Fin n) (Fin n) ℚ)
      ((1 + dq / 4) • (1 : Matrix (Fin n) (Fin n) ℚ)) 0 dq where
  δ_pos := h0
  psd_margin := by
    intro x
    rw [QMCLeafB.SepOracle.qf_smulQ, qf_one_eq]
    have h2 : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h3 : (0 : ℚ) < 1 + dq / 4 := by linarith
    nlinarith
  diag_near := by
    intro i
    have hii : ((1 + dq / 4) • (1 : Matrix (Fin n) (Fin n) ℚ)) i i = 1 + dq / 4 := by
      simp [Matrix.smul_apply]
    rw [hii, show (1 : ℚ) + dq / 4 - 1 = dq / 4 by ring, abs_of_nonneg (by linarith)]
  trace_le := by
    have hz : QMCLeafB.SepOracle.frob (0 : Matrix (Fin n) (Fin n) ℚ)
        ((1 + dq / 4) • (1 : Matrix (Fin n) (Fin n) ℚ)) = 0 := by
      simp [QMCLeafB.SepOracle.frob]
    rw [hz]
    linarith

/-- **At `n = 2`, `dq = 1` the boundary lowering of a legal `RelaxMem` point busts the trace
budget**: `15/8 > 3/2`. -/
theorem not_hTrc_two :
    ¬ (∑ i, ((1 - (1 : ℚ) / 4) •
          ((1 + (1 : ℚ) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℚ))) i i ≤ (2 : ℚ) * (1 - 1 / 4)) := by
  rw [diag_sum_smul_rat, diag_sum_smul_rat, diag_sum_one_diag _ (fun _ => by simp)]
  norm_num

/-- **The `hTrc` slot is not implied by the ok-branch certificate.** -/
theorem diag_near_not_hTrc :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (0 : Matrix (Fin 2) (Fin 2) ℚ) Q 0 1 ∧
        ¬ (∑ i, ((1 - (1 : ℚ) / 4) • Q) i i ≤ (2 : ℚ) * (1 - 1 / 4)) := by
  exact ⟨(1 + (1 : ℚ) / 4) • (1 : Matrix (Fin 2) (Fin 2) ℚ),
    relaxMem_top_of_band 2 (by norm_num), not_hTrc_two⟩

/-! ## 3.  The pinch, and why it is exactly unit diagonal -/

theorem le_one_of_mul_le {a b : ℚ} (ha : 0 < a) (h : a * b ≤ a) : b ≤ 1 := by
  by_contra hc
  push Not at hc
  have h2 := mul_lt_mul_of_pos_left hc ha
  linarith

theorem one_le_of_le_mul {a b : ℚ} (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b := by
  by_contra hc
  push Not at hc
  have h2 := mul_lt_mul_of_pos_left hc ha
  linarith

theorem diag_le_one_of_boundary {n : ℕ} {dq : ℚ} (hp : (0 : ℚ) < 1 - dq / 4)
    {Q : Matrix (Fin n) (Fin n) ℚ}
    (h : ∀ i, ((1 - dq / 4) • Q) i i ≤ 1 - dq / 4) : ∀ i, Q i i ≤ 1 := by
  intro i
  have h' := h i
  rw [Matrix.smul_apply, smul_eq_mul] at h'
  exact le_one_of_mul_le hp h'

theorem one_le_of_boundary_near {n : ℕ} {dq u : ℚ} (hp : (0 : ℚ) < 1 - dq / 4)
    {A : Matrix (Fin n) (Fin n) ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A ((1 - dq / 4) • Q) u dq) : ∀ i, 1 ≤ Q i i := by
  intro i
  have hn := hmem.diag_near i
  rw [Matrix.smul_apply, smul_eq_mul] at hn
  have h1 : (1 - dq / 4) ≤ (1 - dq / 4) * Q i i := by
    have h2 := (abs_le.mp hn).1
    linarith
  exact one_le_of_le_mul hp h1

/-- **The pinch forces unit diagonal.** -/
theorem pinch_forces_unitDiag {n : ℕ} {dq u : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    {A : Matrix (Fin n) (Fin n) ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A ((1 - dq / 4) • Q) u dq)
    (hdiag : ∀ i, ((1 - dq / 4) • Q) i i ≤ 1 - dq / 4) : ∀ i, Q i i = 1 := by
  have hp := boundary_pos h0 h4
  have hup := diag_le_one_of_boundary hp hdiag
  have hlo := one_le_of_boundary_near (u := u) hp hmem
  intro i
  have h1 := hup i
  have h2 := hlo i
  linarith

/-- **`hTrc` is redundant given `hdiagc` at the boundary centre.** -/
theorem hTrc_of_hdiagc_boundary {n : ℕ} {dq : ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hdiag : ∀ i, ((1 - dq / 4) • Q) i i ≤ 1 - dq / 4) :
    ∑ i, ((1 - dq / 4) • Q) i i ≤ (n : ℚ) * (1 - dq / 4) := by
  have h : (∑ i, ((1 - dq / 4) • Q) i i) ≤ ∑ _i : Fin n, (1 - dq / 4) :=
    Finset.sum_le_sum fun i _ => hdiag i
  have h2 : (∑ _i : Fin n, (1 - dq / 4)) = (n : ℚ) * (1 - dq / 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [h, h2]

/-- The trace bound at the pinch, **with equality**. -/
theorem hTrc_eq_of_pinch {n : ℕ} {dq u : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    {A : Matrix (Fin n) (Fin n) ℚ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A ((1 - dq / 4) • Q) u dq)
    (hdiag : ∀ i, ((1 - dq / 4) • Q) i i ≤ 1 - dq / 4) :
    ∑ i, ((1 - dq / 4) • Q) i i = (n : ℚ) * (1 - dq / 4) :=
  hTrc_boundary_eq_of_unitDiag Q (pinch_forces_unitDiag h0 h4 hmem hdiag)

/-! ## 4.  The drift pair at the boundary centre, with its exact shift -/

theorem hcast_dq {dq : ℚ} : (1 : ℝ) - ((1 - dq / 4 : ℚ) : ℝ) = (dq : ℝ) / 4 := by
  push_cast
  ring

theorem boundary_centre_shift {n : ℕ} (a : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ)
    (Cat : Fin (n * n) → ℝ) :
    Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (a • Q))
      = (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
        + ((1 : ℝ) - (a : ℝ)) • QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat Q) :=
  QMCLeafB.CentreClosure.centre_shift a Q Cat

/-- **`hdriftd`'s shift**: the identity direction sees the lowering as `+ s · tr Q`. -/
theorem driftd_boundary_shift {n : ℕ} (a : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ)
    (Cat : Fin (n * n) → ℝ) :
    dOne n ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (a • Q)))
      = dOne n ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
        + ((1 : ℝ) - (a : ℝ)) * (∑ i, ((Q i i : ℚ) : ℝ)) := by
  rw [boundary_centre_shift, dotProduct_add, dotProduct_smul, smul_eq_mul,
    QMCLeafB.CentreClosure.dOne_dot_flat_eq_trace]

theorem diagSum_flat_castMat {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) :
    diagSum (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
      = ∑ i, ((Q i i : ℚ) : ℝ) := by
  simp [diagSum, QMCLeafB.DriftExact.flat_finProdFinEquiv, QMCLeafB.SepOracle.castMat_apply]

theorem dOne_dot_sub_flat {n : ℕ} (Cat : Fin (n * n) → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℚ) :
    dOne n ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
      = diagSum Cat - (∑ i, ((Q i i : ℚ) : ℝ)) := by
  have h1 : diagSum (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
      = diagSum Cat - diagSum (QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat Q)) := by
    simp only [diagSum, Pi.sub_apply, Finset.sum_sub_distrib]
  rw [QMCLeafB.DriftExact.dOne_dot, h1, diagSum_flat_castMat]

/-- **`hdriftd` at the boundary centre is the engine-centre trace budget.** -/
theorem hdriftd_boundary_iff {n : ℕ} {dq : ℚ} (Cat : Fin (n * n) → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℚ) :
    dOne n ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) ≤ 0
      ↔ diagSum Cat ≤ ((1 - dq / 4 : ℚ) : ℝ) * (∑ i, ((Q i i : ℚ) : ℝ)) := by
  have hcast' : ((1 - dq / 4 : ℚ) : ℝ) = 1 - (dq : ℝ) / 4 := by
    push_cast
    ring
  rw [driftd_boundary_shift (1 - dq / 4) Q Cat, dOne_dot_sub_flat, hcast_dq, hcast']
  constructor <;> intro h <;> linarith

/-- **`hdriftc`'s shift**: the lowering moves the pairing by exactly `s · (c ⪝ flat Q)`. -/
theorem driftc_boundary_shift {n : ℕ} (a : ℚ) (Q : Matrix (Fin n) (Fin n) ℚ)
    (Cat c : Fin (n * n) → ℝ) :
    c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (a • Q)))
      = c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
        + ((1 : ℝ) - (a : ℝ)) *
            (c ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) := by
  rw [boundary_centre_shift, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- **`hdriftc` at the boundary centre from the base point**, when the cut normal is non-positive on
the base point — the case for a violated direction of the separation oracle. -/
theorem hdriftc_boundary_of_base {n : ℕ} {dq : ℚ} (h0 : 0 ≤ dq)
    (Q : Matrix (Fin n) (Fin n) ℚ) (Cat c : Fin (n * n) → ℝ) (m : ℚ)
    (hbase : c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat Q)) ≤ ((m : ℚ) : ℝ) / 2)
    (hnonpos : c ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q) ≤ 0) :
    c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) ≤ ((m : ℚ) : ℝ) / 2 := by
  rw [driftc_boundary_shift (1 - dq / 4) Q Cat c, hcast_dq]
  have hs : (0 : ℝ) ≤ (dq : ℝ) / 4 :=
    div_nonneg (by exact_mod_cast h0) (by norm_num)
  have h3 : (dq : ℝ) / 4 *
      (c ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs hnonpos
  linarith

/-- The sharpened `hdriftc` residual at the base point. -/
theorem hdriftc_boundary_of_shifted {n : ℕ} {dq : ℚ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (Cat c : Fin (n * n) → ℝ) (m : ℚ)
    (h : c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
        + ((dq : ℝ) / 4) * (c ⬝ᵥ QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat Q)) ≤ ((m : ℚ) : ℝ) / 2) :
    c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q))) ≤ ((m : ℚ) : ℝ) / 2 := by
  rw [driftc_boundary_shift (1 - dq / 4) Q Cat c, hcast_dq]
  exact h

/-! ## 5.  The slot, assembled -/

/-- The ok-branch membership at the boundary centre (`AuditM1.relaxMem_boundary_smul`, at a stream). -/
theorem hmem_boundary {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u u' dq : ℚ}
    (h0 : 0 < dq) (h4 : dq ≤ 4) (Q : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (hQ1 : ∀ k i, 1 ≤ Q k i i) (hraw : ∀ k, QMCLeafB.RelaxOracle.RelaxMem A (Q k) u' dq)
    (hu : (1 - dq / 4) * (u' + dq / 2) ≤ u + dq / 2) :
    ∀ k, QMCLeafB.RelaxOracle.RelaxMem A ((1 - dq / 4) • Q k) u dq :=
  fun k => QMCLeafB.AuditM1.relaxMem_boundary_smul (hraw k) h0 h4 (hQ1 k) hu

/-- Symmetry is stable under the boundary lowering. -/
theorem hCsym_boundary {n : ℕ} {dq : ℚ} (Q : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ k, (Q k)ᵀ = Q k) : ∀ k, ((1 - dq / 4) • Q k)ᵀ = (1 - dq / 4) • Q k := by
  intro k
  rw [Matrix.transpose_smul, h k]

/-- **The trace budget at the boundary centre**, from the base stream's trace budget. -/
theorem hTrc_boundary {n : ℕ} {dq : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    (Q : ℕ → Matrix (Fin n) (Fin n) ℚ) (h : ∀ k, ∑ i, Q k i i ≤ (n : ℚ)) :
    ∀ k, ∑ i, ((1 - dq / 4) • Q k) i i ≤ (n : ℚ) * (1 - dq / 4) :=
  fun k => hTrc_boundary_of_trace h0 h4 (h k)

/-- **`hdriftd` at the boundary centre**, restated at a stream. -/
theorem hdriftd_boundary {n : ℕ} {dq : ℚ} (Cat : ℕ → Fin (n * n) → ℝ)
    (Q : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (hbud : ∀ k, diagSum (Cat k)
      ≤ ((1 - dq / 4 : ℚ) : ℝ) * (∑ i, ((Q k i i : ℚ) : ℝ))) :
    ∀ k, dOne n ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q k))) ≤ 0 :=
  fun k => (hdriftd_boundary_iff (Cat k) (Q k)).2 (hbud k)

/-- At a unit-diagonal base stream the engine-centre trace budget is the single scalar inequality
`diagSum (Cat k) ≤ n·(1 − dq/4)`. -/
theorem hdriftd_boundary_of_unitDiag {n : ℕ} {dq : ℚ} (Cat : ℕ → Fin (n * n) → ℝ)
    (Q : ℕ → Matrix (Fin n) (Fin n) ℚ) (hunit : ∀ k i, Q k i i = 1)
    (hbud : ∀ k, diagSum (Cat k) ≤ (((n : ℚ) * (1 - dq / 4) : ℚ) : ℝ)) :
    ∀ k, dOne n ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q k))) ≤ 0 := by
  refine hdriftd_boundary Cat Q (fun k => ?_)
  have htr : (∑ i, ((Q k i i : ℚ) : ℝ)) = ((n : ℚ) : ℝ) := by
    have hzero : ∀ i : Fin n, ((Q k i i : ℚ) : ℝ) = 1 := by
      intro i
      rw [hunit k i]
      norm_num
    rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  rw [htr]
  have hcast : ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ)
      = (((n : ℚ) * (1 - dq / 4) : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  exact hbud k

/-- **The trace-budget slot of residual 2, in one line.**  Given the base stream's trace budget, the
engine centre's trace budget and the shifted cut-normal pairing, the three residual conditions of
`DriftExact.runParts_at_interior_exact` hold at the boundary-lowered centre
`cX k = (1 − dq/4) • Q k`. -/
theorem trace_budget_slot {n : ℕ} {dq : ℚ} (h0 : 0 < dq) (h4 : dq < 4)
    (Cat : ℕ → Fin (n * n) → ℝ) (Q : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (c : ℕ → Fin (n * n) → ℝ) (marg : ℕ → ℚ)
    (htrcQ : ∀ k, ∑ i, Q k i i ≤ (n : ℚ))
    (hbud : ∀ k, diagSum (Cat k)
      ≤ ((1 - dq / 4 : ℚ) : ℝ) * (∑ i, ((Q k i i : ℚ) : ℝ)))
    (hcut : ∀ k, c k ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat (Q k)))
        + ((dq : ℝ) / 4) * (c k ⬝ᵥ QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat (Q k))) ≤ ((marg k : ℚ) : ℝ) / 2) :
    (∀ k, ∑ i, ((1 - dq / 4) • Q k) i i ≤ (n : ℚ) * (1 - dq / 4))
      ∧ (∀ k, dOne n ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q k))) ≤ 0)
      ∧ (∀ k, c k ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat ((1 - dq / 4) • Q k))) ≤ ((marg k : ℚ) : ℝ) / 2) :=
  ⟨hTrc_boundary h0 h4 Q htrcQ,
   hdriftd_boundary Cat Q hbud,
   fun k => hdriftc_boundary_of_shifted (Q k) (Cat k) (c k) (marg k) (hcut k)⟩


/-- The campaign tolerance is well inside the boundary scale's range: `dqShallow G < 4`. -/
theorem dqShallow_lt_four (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.RundataParams.dqShallow G < 4 := by
  have hRq0 := QMCLeafB.RundataArith.Rq_nonneg G
  unfold QMCLeafB.RundataParams.dqShallow
  split_ifs with h
  · norm_num
  · unfold QMCLeafB.RundataParams.dqShallowCore QMCLeafB.RundataCert.eps
    have hpos : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G := by
      rcases lt_or_eq_of_le hRq0 with h1 | h1
      · exact h1
      · exact absurd h1.symm h
    have hden : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
    rw [div_lt_iff₀ hden]
    nlinarith

/-- **The trace-budget slot at the campaign family `paramsKbc2`.**  This is the drop-in for the
`hTrc` / `hdriftc` / `hdriftd` arguments of `DriftExact.runParts_at_interior_exact` (take `.1`,
`.2.1`, `.2.2`), with `cX k := (1 − (paramsKbc2 G).dq / 4) • Q k`. -/
theorem trace_budget_slot_paramsKbc2 (G : QuantumMaxCutEnergy.Input)
    (Cat : ℕ → Fin (G.n * G.n) → ℝ) (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (c : ℕ → Fin (G.n * G.n) → ℝ) (marg : ℕ → ℚ)
    (htrcQ : ∀ k, ∑ i, Q k i i ≤ (G.n : ℚ))
    (hbud : ∀ k, diagSum (Cat k)
      ≤ ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4 : ℚ) : ℝ)
          * (∑ i, ((Q k i i : ℚ) : ℝ)))
    (hcut : ∀ k, c k ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
        (QMCLeafB.SepOracle.castMat (Q k)))
        + (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℝ) / 4)
          * (c k ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (Q k)))
        ≤ ((marg k : ℚ) : ℝ) / 2) :
    (∀ k, ∑ i, ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k) i i
        ≤ (G.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4))
      ∧ (∀ k, dOne G.n ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat
            ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k))) ≤ 0)
      ∧ (∀ k, c k ⬝ᵥ (Cat k - QMCLeafB.AnswerProducer.flat
          (QMCLeafB.SepOracle.castMat
            ((1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) • Q k)))
          ≤ ((marg k : ℚ) : ℝ) / 2) := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq] at hbud hcut ⊢
  exact trace_budget_slot (QMCLeafB.RundataParams.dqShallow_pos G) (dqShallow_lt_four G)
    Cat Q c marg htrcQ hbud hcut


/-- The diagonal read-out of the rational identity, cast to `ℝ`. -/
theorem sum_diag_one_cast (n : ℕ) :
    (∑ i, (((1 : Matrix (Fin n) (Fin n) ℚ) i i : ℚ) : ℝ)) = (n : ℝ) := by
  simp

/-- **The reduced residual is not vacuous.**  A concrete instance at `n = 2`, `dq = 1/2` in which all
three antecedents of `trace_budget_slot` hold simultaneously: the unit-diagonal base stream, the zero
engine centre, the identity cut normal and margin `1` (`−2 + 1/4 ≤ 1/2`).  So the reduction of §5
cannot fire only on an inconsistent premise.  This is a consistency check on the *reduction*, not a
model of the run. -/
theorem reduced_residual_inhabited :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℚ) (Cat : Fin (2 * 2) → ℝ) (c : Fin (2 * 2) → ℝ) (marg : ℚ),
      (∑ i, Q i i ≤ (2 : ℚ))
        ∧ diagSum Cat ≤ ((1 - (1 : ℚ) / 2 / 4 : ℚ) : ℝ) * (∑ i, ((Q i i : ℚ) : ℝ))
        ∧ c ⬝ᵥ (Cat - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
            + (((1 : ℚ) / 2 : ℚ) : ℝ) / 4
              * (c ⬝ᵥ QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
            ≤ ((marg : ℚ) : ℝ) / 2 := by
  refine ⟨1, 0, dOne 2, 1, ?_, ?_, ?_⟩
  · have h : (∑ i, (1 : Matrix (Fin 2) (Fin 2) ℚ) i i) = (2 : ℚ) := by
      simp
    rw [h]
  · rw [show diagSum (0 : Fin (2 * 2) → ℝ) = 0 by simp [diagSum],
      sum_diag_one_cast 2]
    norm_num
  · rw [dOne_dot_sub_flat, QMCLeafB.CentreClosure.dOne_dot_flat_eq_trace,
      show diagSum (0 : Fin (2 * 2) → ℝ) = 0 by simp [diagSum], sum_diag_one_cast 2]
    norm_num

end QMCLeafB.TraceBudgetM8

/-! ## Axiom audit -/

#print axioms QMCLeafB.TraceBudgetM8.diag_sum_smul_rat
#print axioms QMCLeafB.TraceBudgetM8.diag_sum_one_diag
#print axioms QMCLeafB.TraceBudgetM8.boundary_pos
#print axioms QMCLeafB.TraceBudgetM8.hTrc_boundary_iff
#print axioms QMCLeafB.TraceBudgetM8.hTrc_boundary_of_trace
#print axioms QMCLeafB.TraceBudgetM8.hTrc_boundary_eq_of_unitDiag
#print axioms QMCLeafB.TraceBudgetM8.qf_one_eq
#print axioms QMCLeafB.TraceBudgetM8.relaxMem_top_of_band
#print axioms QMCLeafB.TraceBudgetM8.not_hTrc_two
#print axioms QMCLeafB.TraceBudgetM8.diag_near_not_hTrc
#print axioms QMCLeafB.TraceBudgetM8.pinch_forces_unitDiag
#print axioms QMCLeafB.TraceBudgetM8.hTrc_of_hdiagc_boundary
#print axioms QMCLeafB.TraceBudgetM8.hTrc_eq_of_pinch
#print axioms QMCLeafB.TraceBudgetM8.driftd_boundary_shift
#print axioms QMCLeafB.TraceBudgetM8.diagSum_flat_castMat
#print axioms QMCLeafB.TraceBudgetM8.dOne_dot_sub_flat
#print axioms QMCLeafB.TraceBudgetM8.hdriftd_boundary_iff
#print axioms QMCLeafB.TraceBudgetM8.driftc_boundary_shift
#print axioms QMCLeafB.TraceBudgetM8.hdriftc_boundary_of_base
#print axioms QMCLeafB.TraceBudgetM8.hdriftc_boundary_of_shifted
#print axioms QMCLeafB.TraceBudgetM8.hmem_boundary
#print axioms QMCLeafB.TraceBudgetM8.hCsym_boundary
#print axioms QMCLeafB.TraceBudgetM8.hTrc_boundary
#print axioms QMCLeafB.TraceBudgetM8.hdriftd_boundary
#print axioms QMCLeafB.TraceBudgetM8.hdriftd_boundary_of_unitDiag
#print axioms QMCLeafB.TraceBudgetM8.trace_budget_slot
#print axioms QMCLeafB.TraceBudgetM8.dqShallow_lt_four
#print axioms QMCLeafB.TraceBudgetM8.trace_budget_slot_paramsKbc2
#print axioms QMCLeafB.TraceBudgetM8.reduced_residual_inhabited


