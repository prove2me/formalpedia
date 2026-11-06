-- Prove2me | Definitions.Def_QMCLeafB_fa35
-- name    : QMCLeafB_fa35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:42:03.838586+00:00
-- url     : https://prove2.me/theorems/24958e15-100a-474d-9e84-673b54955894
-- title:
--   QMCLeafB fa35
-- statement:
--   # `Check_fa35_m3` — phase 35, member m3, direction `falsify35`: AUDIT OF THE REDUCTION
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
/-
# `Check_fa35_m3` — phase 35, member m3, direction `falsify35`: AUDIT OF THE REDUCTION

The campaign's last obligation is `ThinRec34M4.ShallowCut` at a bit-`false` point of the ball-free
nonempty thin stratum (m4/ph34-d5).  This file audits the *reduction* rather than the ledger: it asks
whether `runParts_false_iff_bodyRec` / `hfalse_thin_residual` / `encl_of_bodyRec` have a hypothesis a
real record could exploit, and whether the obligation they name is the true one.

## Findings (all machine-checked below)

**F1 — `hfalse_thin_residual` is airtight.**  `RunParts.hverdict` is the only field mentioning the
bit, and `anyOk_eq_false_iff` turns `o G t = false` into `ok ≡ false`; both directions are
field-by-field rebuilds (m4's `runParts_false_iff_bodyRec`).  No gap, no extra hypothesis: the
all-false record class is program-free.  Nothing to exploit.

**F2 — `encl_of_bodyRec` is airtight, and its `σ ≤ 0` case is VACUOUS.**  m4's `del_le_rmax_sqrt`
splits on `σ ≥ 0` / `σ < 0`; at a genuine cut round `σ_k = c_k ⬝ p_k > 0` always
(`sigmaQ_NormalCut_pos`: `A_k p_k = c_k`, `A_k` positive definite, `c_k ≠ 0`).  So the ledger is
*exactly* `del_k ≤ rmax·√σ_k` and no record can make the cap vacuous.

**F3 — THE OBLIGATION IS FALSE OUTSIDE THE BALL-FREE STRATUM.**  `not_shallowCut_of_ball`: a
body bearing the campaign ball carries no `ShallowCut` (it would give `BodyRec`, which m4's
`not_bodyRec_of_ball` refutes).  Consequently the *family* strokes of m4 (`hfalse_family_of_shallowCut`,
`hfalse_of_shallowCut`) as stated are unsatisfiable whenever the program reads `false` at a
ball-bearing body: the duty must be stated **stratum-scoped** (`no_hfalse_at_ball` is the sharp form).
This is not a defect of the record, it is the ball volume obstruction showing up in the reduction.

**F4 — THE LEDGER IS NOT THE OBSTRUCTION: `del ≡ 0` IS ALWAYS AVAILABLE FROM A SUPPORTING CUT.**
`shallowCut_of_support`: if the canonical transcript's own cuts are SUPPORTING at the accumulated
centre — `0 ≤ c_k ⬝ (z − Cat_k)` for every `z` in the relaxation, i.e. `Cat_k` is not interior to
the relaxation — then `ShallowCut` holds with `del ≡ 0` and `ρ ≡ rmax`.  So `ShallowCut` never needs
a strictly positive margin, and `rmax` (which enters only through `del² ≤ rmax²σ`) does not bind on
that branch: **the whole obligation reduces to keeping the accumulated centre out of the relaxation
at every round below the horizon.**  `bodyRec_of_support` and `hfalse_of_support` are the record
strokes in that form.

**F5 — the horizon is what gives the obligation its content.**  `shallowCut_of_horizon_zero`: at
`K·m = 0` every slot of the record and of `ShallowCut` is vacuous (all guarded by `k < K·m`) except
the free `del`-cap, so `ShallowCut` holds trivially.  Hence no structural refutation of `ShallowCut`
is possible: any refutation must consume `0 < K·m` rounds of the chain.  At `paramsKbc2` the horizon
is `K·m ≥ 1` (and `rmax = 1/16`), so the residual is genuinely non-vacuous there.

Discipline: `set_option autoImplicit false`; no proof placeholders, no extra axioms, no native
evaluation, nothing outside the safe fragment; `#print axioms` after every theorem.  Imports: `Mathlib` + the published mirror
`Definitions.Def_QMCLeafB_thinrec34` (which carries `ShallowCut`, `NormalCut`, `BodyRec`,
`not_bodyRec_of_ball`, `bodyRec_of_shallowCut`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Falsify35M3

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4

/-- `2 ≤ n` gives `2 ≤ n·n` (the engine's dimension is `n·n`). -/
theorem two_le_sq (n : ℕ) (hn : 2 ≤ n) : 2 ≤ n * n := by
  have h := Nat.mul_le_mul hn hn
  omega

variable {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}

/-- The engine's initial shape at `P`, in the form the canonical transcript is stated over. -/
abbrev A0 (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)

/-- The canonical transcript's witness relation, in the `initShapeOf` form. -/
theorem witOf_normalCut (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ∀ k, Aat (G.n * G.n) (A0 G P) (NormalCut G P hn c hc) k
        *ᵥ ((NormalCut G P hn c hc k).p) = (NormalCut G P hn c hc k).c := by
  intro k
  have h := QMCLeafB.RunPartsDilate.runCut_wit G P hn c hc k
  rw [QMCLeafB.ThinRec34M4.initShape_eq G P] at h
  exact h

#print axioms QMCLeafB.Falsify35M3.witOf_normalCut

/-- **F2.**  At EVERY round of the canonical transcript the ledger's `σ_k = c_k ⬝ p_k` is strictly
positive: the engine's iterate `A_k` is positive definite, `A_k p_k = c_k` and `c_k ≠ 0`.  So m4's
`σ ≤ 0` case of `del_le_rmax_sqrt` never occurs at a cut round — the cap `del_k ≤ rmax·√σ_k` is
always a genuine inequality. -/
theorem sigmaQ_NormalCut_pos (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    0 < sigmaQ (c k) ((NormalCut G P hn c hc k).p) := by
  have hN : 2 ≤ G.n * G.n := two_le_sq G.n hn
  have hwit := witOf_normalCut (P := P) hn c hc
  have hA0 : (castM (A0 G P)).PosDef := by
    have h := QMCLeafB.RunPartsDilate.A0P_posDef G P
    rw [QMCLeafB.ThinRec34M4.initShape_eq G P] at h
    exact h
  have hρ : ∀ k, 0 ≤ (NormalCut G P hn c hc k).rho := by
    intro k
    have hr : (NormalCut G P hn c hc k).rho = P.rmax := rfl
    rw [hr]
    exact P.hrmax
  have hcne : ∀ k, (NormalCut G P hn c hc k).c ≠ 0 := by
    intro k
    have hcc : (NormalCut G P hn c hc k).c = c k := rfl
    rw [hcc]
    exact hc k
  have hpos := Aat_cast_posDef hN hA0 hwit hρ hcne k
  have hcR : cutCR (NormalCut G P hn c hc) k ≠ 0 := cast_normal_ne (hcne k)
  have hσR : 0 < sigmaR (cutCR (NormalCut G P hn c hc) k) (cutPR (NormalCut G P hn c hc) k) :=
    sigmaR_pos hpos (cast_witness hwit k) hcR
  have hcd : (NormalCut G P hn c hc k).c = c k := rfl
  have hcast : ((sigmaQ (c k) ((NormalCut G P hn c hc k).p) : ℚ) : ℝ)
      = sigmaR (cutCR (NormalCut G P hn c hc) k) (cutPR (NormalCut G P hn c hc) k) := by
    simp only [NormalCut, QMCLeafB.RunPartsDilate.runCut, cutCR, cutPR, sigmaQ, sigmaR,
      dotProduct, Rat.cast_sum, Rat.cast_mul]
  have : (0 : ℝ) < ((sigmaQ (c k) ((NormalCut G P hn c hc k).p) : ℚ) : ℝ) := by
    rw [hcast]; exact hσR
  exact Rat.cast_pos.mp this

#print axioms QMCLeafB.Falsify35M3.sigmaQ_NormalCut_pos

/-- **F4 (the structural reduction).**  If the canonical transcript's cuts are SUPPORTING at their
own accumulated centres — `0 ≤ c_k ⬝ (z − Cat_k)` for every `z` in the relaxation, i.e. the centre
is never interior to the relaxation — then `ShallowCut` holds, with `del ≡ 0`.

So the ledger `del_k² ≤ rmax²·σ_k` is not an obstruction on this branch: the whole content of
`ShallowCut` is the CENTRE-AVOIDANCE of the accumulation, which is a property of the ellipsoid chain
alone. -/
theorem shallowCut_of_support (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsupp : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      0 ≤ cutCR (NormalCut G P hn c hc) k
          ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k)) :
    ShallowCut G t P hn := by
  refine ⟨c, hc, fun _ => 0, ?_, ?_, ?_⟩
  · intro k _
    norm_num
  · intro k
    have hσ := sigmaQ_NormalCut_pos (P := P) hn c hc k
    have hr2 : (0 : ℚ) ≤ P.rmax ^ 2 := by
      have := P.hrmax
      nlinarith
    have := mul_nonneg hr2 hσ.le
    simpa using this
  · intro k hk z hz
    have h := hsupp k hk z hz
    rw [dotProduct_sub] at h
    have h0 : ((fun x => (0 : ℚ)) k : ℚ) = 0 := rfl
    rw [h0, Rat.cast_zero]
    linarith

#print axioms QMCLeafB.Falsify35M3.shallowCut_of_support

/-- **F4, record form.**  A supporting (zero-margin) stream gives the all-false record directly. -/
theorem bodyRec_of_support (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsupp : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      0 ≤ cutCR (NormalCut G P hn c hc) k
          ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k)) :
    BodyRec G t P :=
  bodyRec_of_shallowCut hn (shallowCut_of_support (P := P) hn c hc hsupp)

#print axioms QMCLeafB.Falsify35M3.bodyRec_of_support

/-- **F4, leaf form (HORN 1, repaired).**  `hfalse` follows from a supporting stream at every
bit-`false` point — no emptiness case analysis, no emptiness hypothesis. -/
noncomputable def hfalse_of_support (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsupp : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
      0 ≤ cutCR (NormalCut G P hn c hc) k
          ⬝ᵥ (z - Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k))
    (hbit : o G t = false) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  Classical.choice ((runParts_false_iff_bodyRec hbit).2
    (bodyRec_of_shallowCut hn (shallowCut_of_support (P := P) hn c hc hsupp)))

#print axioms QMCLeafB.Falsify35M3.hfalse_of_support

/-- **F3 (sharp).**  `ShallowCut` is FALSE at any body bearing the campaign ball: it would produce
`BodyRec`, and m4's `not_bodyRec_of_ball` refutes that.  Hence the obligation is meaningful only off
the ball-bearing stratum, and m4's family strokes must be stratum-scoped. -/
theorem not_shallowCut_of_ball (hn : 2 ≤ G.n) {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) :
    ¬ ShallowCut G t P hn :=
  fun H => QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball (bodyRec_of_shallowCut hn H)

#print axioms QMCLeafB.Falsify35M3.not_shallowCut_of_ball

/-- **F3, `hfalse` form (the audit's sharpest negative).**  At a bit-`false` point whose body bears
the campaign ball there is NO record at all — `hfalse` is false there.  So the leaf's `hfalse` owes
the record only on the ball-free stratum, exactly as phase-24/25's ball decision said; the repaired
stroke below is the one that is inhabited there. -/
theorem no_hfalse_at_ball (o : QuantumMaxCutEnergy.Input → ℚ → Bool) {hn : 2 ≤ G.n}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P)
    (hbit : o G t = false) :
    ¬ Nonempty (QMCLeafB.FinalStroke.RunParts o G t P) :=
  fun ⟨B⟩ => not_bodyRec_of_ball hn hball ((runParts_false_iff_bodyRec hbit).1 ⟨B⟩)

#print axioms QMCLeafB.Falsify35M3.no_hfalse_at_ball

/-- **F5.**  With an empty horizon every guarded slot is vacuous, so `ShallowCut` holds for ANY
nonzero stream with `del ≡ 0`: no structural refutation of `ShallowCut` can exist.  (The unguarded
`del`-cap is free because `σ_k > 0`; the unguarded `c_k ≠ 0` is a choice.)  Hence any refutation of
the obligation must consume `0 < K·m` rounds of the ellipsoid chain. -/
theorem shallowCut_of_horizon_zero (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (hhor : P.K * P.m = 0) :
    ShallowCut G t P hn := by
  refine shallowCut_of_support (P := P) hn c hc ?_
  intro k hk
  rw [hhor] at hk
  exact absurd hk (Nat.not_lt_zero k)

#print axioms QMCLeafB.Falsify35M3.shallowCut_of_horizon_zero

/-- **F5, record form.**  Same statement for the record class. -/
theorem bodyRec_of_horizon_zero (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (hhor : P.K * P.m = 0) :
    BodyRec G t P :=
  bodyRec_of_shallowCut hn (shallowCut_of_horizon_zero (P := P) hn c hc hhor)

#print axioms QMCLeafB.Falsify35M3.bodyRec_of_horizon_zero

end QMCLeafB.Falsify35M3


