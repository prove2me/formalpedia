-- Prove2me | Definitions.Def_QMCLeafB_pinchrec
-- name    : QMCLeafB_pinchrec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:08:00.032813+00:00
-- url     : https://prove2.me/theorems/6eb8f64b-a20d-4f70-a2ca-fccb5c8b5e33
-- title:
--   QMCLeafB pinchrec
-- statement:
--   # leaf B phase 19 — brick `pinch-records` (swarm `smw1k12jb`, member m8, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_centre_adm_m1
import Definitions.Def_QMCLeafB_traceBudget2_m8
import Definitions.Def_QMCLeafB_bundleFull
/-
# leaf B phase 19 — brick `pinch-records` (swarm `smw1k12jb`, member m8, direction d9)

`Check_centre_adm_m1` fixes the centre stream: the record centre is `diagPinch Q dq` (the state's
block with its diagonal overwritten by `1 − dq/4`), not `(1 − dq/4) • Q` — the scale forces the base
to be unit-diagonal (`full_scale_forces_unit_base`), which cut rounds are not.  The phase-19 judge
named the two things still owed at that centre: the **record streams** (the `RelaxCut` records, which
`Check_pinchLower_m2` only transports to the *scaled* centre) and the **single scalar**

    ∑_{j<k} λ_j · diagSum (p_j) ≤ n · (1 − dq/4).

This file delivers both at the pinched centre:

* §1 **the cut record at the pinch is free**: at `diagPinch Q dq` the coordinate normal
  `δ_i δ_iᵀ` has margin `dq/4` and separates the relaxed body for *every* base `Q` — because the
  body's own `diag_near` band puts `X i i ≥ 1 − dq/4`, which is the centre's diagonal exactly.  So
  `BundleFull.C` never inherits a cost from the pinch (`hfrob (δ_iδ_iᵀ) (diagPinch Q dq) = 1 − dq/4`);
* §2 **the scalar is exactly `hdriftd` at the pinch**, with **no** unit-diagonal side condition:
  `dOne ⬝ (Cat k − flat (diagPinch Q dq)) ≤ 0 ⟺ ∑_{j<k} λ_j diagSum p_j ≤ (1 − dq/4)·n`
  (`hdriftd_pinch_iff`).  The phase-18 form (`TraceBudgetM8.hdriftd_linear_iff`) needed
  `∀ i, Q i i = 1`; the pinch's trace equality (`CentreAdm.sum_diagPinch`) removes it.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.PinchRec

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle
open QMCLeafB.RelaxOracle
open QMCLeafB.CentreAdm
open QMCLeafB.DriftExact

/-! ## 1.  The cut record at the pinched centre is free -/

/-- **The diagonal read-out of the coordinate normal**: `frob (δ_i δ_iᵀ) Y = Y i i`. -/
theorem frob_deltaDelta {n : ℕ} (i : Fin n) (Y : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i))) Y
      = Y i i := by
  rw [castMat_vecMulVec]
  rw [← QMCLeafB.SepOracle.qf_eq_frob Y (fun k => ((delta (K := ℚ) i) k : ℝ))]
  have h : (fun k => ((delta (K := ℚ) i) k : ℝ)) = delta (K := ℝ) i := by
    funext k
    by_cases hk : k = i <;> simp [delta, hk]
  rw [h, qf_delta]

/-- **A separating cut at the pinched centre, for every base `Q`.**  The coordinate normal needs no
information about the round: the body's diagonal band is centred on `1` with radius `dq/4`, and the
pinched centre sits at its lower edge. -/
noncomputable def relaxCut_pinch {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℚ) (u dq : ℚ)
    (hdq : 0 < dq) (i : Fin n) :
    QMCLeafB.RelaxOracle.RelaxCut A (diagPinch Q dq) u dq where
  normal := vecMulVec (delta i) (delta i)
  margin := dq / 4
  margin_pos := by linarith
  separates := by
    intro X hX
    obtain ⟨-, hdiag, -⟩ := hX
    have h1 : QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i))) X
        = X i i := frob_deltaDelta i X
    have h2 : QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (vecMulVec (delta (K := ℚ) i) (delta (K := ℚ) i)))
        (QMCLeafB.SepOracle.castMat (diagPinch Q dq)) = ((1 - dq / 4 : ℚ) : ℝ) := by
      rw [frob_deltaDelta, QMCLeafB.SepOracle.castMat_apply, diagPinch_diag]
    rw [QMCLeafB.SepOracle.frob_sub, h1, h2]
    have hb := hdiag i
    rw [abs_le] at hb
    push_cast
    linarith [hb.1]

/-- **The cut record exists at the pinched centre** (Proposition form, the audit target). -/
theorem nonempty_relaxCut_pinch {n : ℕ} (A Q : Matrix (Fin n) (Fin n) ℚ) (u dq : ℚ)
    (hdq : 0 < dq) (i : Fin n) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut A (diagPinch Q dq) u dq) :=
  ⟨relaxCut_pinch A Q u dq hdq i⟩

/-! ## 2.  `hdriftd` at the pinched centre is the single scalar -/

/-- **The scalar budget, exactly.**  At the pinched centre the cumulative diagonal drift is the
engine's own sum of increments, and the centre's trace is `n(1 − dq/4)` for **every** base `Q`. -/
theorem hdriftd_pinch_iff {n : ℕ} {dq : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    QMCLeafB.RunPartsStream.dOne n ⬝ᵥ
      (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
        - QMCLeafB.AnswerProducer.flat
            (QMCLeafB.SepOracle.castMat (diagPinch Q dq))) ≤ 0
      ↔ (∑ j ∈ Finset.range k,
          engLam (n * n) cd j
            * diagSum (QMCLeafB.EngineIterates.cutPR cd j))
        ≤ ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
  rw [QMCLeafB.DriftExact.stated_iff_trace, QMCLeafB.DriftExact.diagSum_cat]
  have h : (∑ i : Fin n, ((diagPinch Q dq) i i : ℝ))
      = ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
    rw [← Rat.cast_sum, sum_diagPinch]
    push_cast
    ring
  rw [h]

/-- **The centre-level slots at the pinched centre, together.**  `hTrc` holds with equality for
every base, `hCsym` is inherited from the base's symmetry, and the cut record and the scalar are §1
and §2.  So the pinch bookkeeping is entirely removed from the record streams. -/
theorem pinch_centre_slots {n : ℕ} {dq : ℚ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (hsym : ∀ i j, Q i j = Q j i) (hdq : 0 < dq) :
    (∑ i, (diagPinch Q dq) i i = (n : ℚ) * (1 - dq / 4))
      ∧ (diagPinch Q dq)ᵀ = diagPinch Q dq :=
  ⟨sum_diagPinch Q dq, Matrix.ext (fun i j => diagPinch_symm hsym dq j i)⟩

end QMCLeafB.PinchRec

/-! ## 3.  Axiom audit -/

#print axioms QMCLeafB.PinchRec.frob_deltaDelta
#print axioms QMCLeafB.PinchRec.relaxCut_pinch
#print axioms QMCLeafB.PinchRec.nonempty_relaxCut_pinch
#print axioms QMCLeafB.PinchRec.hdriftd_pinch_iff
#print axioms QMCLeafB.PinchRec.pinch_centre_slots


