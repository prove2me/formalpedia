-- Prove2me | Definitions.Def_QMCLeafB_bh35
-- name    : QMCLeafB_bh35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:50:56.847105+00:00
-- url     : https://prove2.me/theorems/f571f7ea-ce7a-4381-88f5-1108dfbad1bb
-- title:
--   QMCLeafB bh35
-- statement:
--   # `Check_bh35_m5` — phase 35, member m5, direction d5 (`bit-horn`): the pinched-candidate barrier
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_fal34b
import Definitions.Def_QMCLeafB_sim_loop_m6
/-
# `Check_bh35_m5` — phase 35, member m5, direction d5 (`bit-horn`): the pinched-candidate barrier

## The question

The leaf's last obligation (`Check_thinrec34_m4`, `hfalse_thin_residual`) sits at bit-`false`
points of the ball-free nonempty thin stratum (`Check_dreg_m6`'s band at `G₁`).  Two horns:

* **record horn** — build the all-`false` `RunParts` there, whose content is `ShallowCut`;
* **bit horn** (this direction) — make the bit read `true` there (`hcomplete`), which by
  `ThinRec34M4.hfalse_of_bit_complete` frees the whole duty and leaves only the banked
  `round_member`/`relaxMem_witness` ok lane.

The phase-33/34 record shipped the **released gate** `dvR s ≤ dqOf s / 4` as the `ok` test and
`CentreAdm.diagPinch` (diagonal overwritten to `1 − δ/4`) as the member it certifies
(`Fal34B.relaxMem_diagPinch_of_releasedGate`).  `hcomplete` at that programme is *open*
(`Check_hcb32_m3` split it off; `Check_refute32_m4` refuted only the **exact** gate, at
`(G₀, −1/2)`, by the `dvR ≠ 0` mechanism).

## The answer this file machine-checks

**The bit horn is DEAD at the dreg band for the whole pinched-candidate class — trajectory-free.**
The released gate's conclusion is not "some member exists": it is a member whose diagonal is the
programme's pinch `1 − δ/4` (`diagPinch` overwrites the diagonal).  At the band
`DregM6.not_pinchFeasible` says *no* such member exists, for every `Δ < δ`.  Hence **no state
whatsoever** — no trajectory, no round programme, no horizon — can pass the released gate at a band
point, so the bit reads `false` there for every orbit.  `hcomplete` at the band is refuted at the
released gate, and the `ok` lane cannot be used to escape the record.

**And the repair is pinned exactly.**  The band's own rational member (`§4`, NEW: the band has a
RATIONAL member, not merely a real one — `DregM6.not_bodyEmpty` was real-only) sits at the *top* of
the diagonal band `1 + δ/4`, not at the pinch.  Machine-checked here:

* `§3 diag_sum_ge` + `diag_le_top` — every rational member at the band obeys
  `2 + δ/2 − Δ ≤ Q₀₀ + Q₁₁ ≤ 2 + δ/2`: the diagonal is pinned to the TOP edge;
* `§3 sum_gate_rejects_dreg_member` — at `Δ = 0` every member has `dsum = δ/2 > δ/4`, so the sum
  gate `dvR ≤ δ/4` **rejects every member at the band** — the gate itself must be re-pointed, not
  just the pinch;
* `§8 segment_member`/`offdiag_sum_eq_zero` — at `Δ = 0` the band's rational body is EXACTLY the
  segment `{Q : Qᵢᵢ = 1 + δ/4, Q₀₁ + Q₁₀ = −(2 + 3δ/2)}`, and every member is strictly non-PSD
  (`qf Q 1 = −δ < 0`): the band is invisible to every exact-PSD candidate semantics;
* `§4 topGate_iff_mem` — the repaired test `TopGate` (per-coordinate gate `|Qᵢᵢ − 1| ≤ δ/4`, certified
  relaxed-PSD margin, level test, candidate = the state's own matrix `topPinch`-ed to the top edge)
  satisfies `(∃ cX, RelaxMem A cX u δ) ↔ (∃ Q, TopGate A u δ Q)`: it is sound AND accepts every
  member.  It is non-vacuous at the band (`dreg_topGate_inhabited`).

So the bit horn's exact remaining cost is **one reach theorem**: the orbit must visit a matrix
satisfying `TopGate` at every nonempty-body point — i.e. land on the body, which at the dreg band is
a single point (ball-free, `dreg_band`).  The banked volume/cube machinery cannot supply it
(`BallM2.no_runParts_of_ball`, `AlcutM3.no_cube_of_allFalse` need positive content), and the
phase-22 analysis already recorded that thin bodies are volume-invisible to any poly-time ellipsoid
in `K·m` rounds.  Recommendation (docstring, end): land the record horn.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration; published `Definitions.Def_QMCLeafB_*` imports only.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.BH35M5

open QuantumMaxCutEnergy

/-- The band's reference tolerance `δ = P₁.dq = 1/380000`. -/
abbrev d0 : ℚ := 1 / 380000

/-! ## 0.  The pinched-candidate class, and the trajectory-free barrier

`RunParts`' `ok` register is a `Bool` stream; the bit is its `anyOk`.  The phase-33/34 programme
certifies, at an `ok` round, a member whose diagonal is the programme's **pinch** `1 − δ/4`
(`Fal34B.relaxMem_diagPinch_of_releasedGate`, witness `CentreAdm.diagPinch`).  This section turns
that into the barrier: if no pinched member exists, the register is identically `false`, hence the
bit is `false` — with NO reference to the orbit, the round function, or the horizon. -/

/-- **The pinched-candidate body**: a rational `RelaxMem` member whose diagonal is the programme's
pinch `1 − δ/4` in every coordinate.  This is exactly the conclusion of the released-gate consumer
(`Fal34B.relaxMem_diagPinch_of_releasedGate`) and of every `cXst`-normalised centre in the shelf
(`RecordsM2.cXst = diagPinch`). -/
def PinchMem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) : Prop :=
  ∃ Q : Matrix (Fin n) (Fin n) ℚ,
    QMCLeafB.RelaxOracle.RelaxMem A Q u δ ∧ ∀ i, Q i i = 1 - δ / 4

/-- `PinchMem` is `ThriceM3.PinchFeasible`, definitionally — the stratum predicate of phases 24/25
is *exactly* membership in the pinched-candidate class. -/
theorem pinchMem_iff_pinchFeasible (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    PinchMem (QMCLeafB.Finalization.wMatrixQ G) (t - QMCLeafB.RundataCert.eps G) P.dq
      ↔ QMCLeafB.ThriceM3.PinchFeasible G t P :=
  Iff.rfl

#print axioms QMCLeafB.BH35M5.pinchMem_iff_pinchFeasible

/-- **THE BARRIER.**  A `Bool` register stream that is *pinched-sound* (every `true` supplies a
pinched member) is identically `false` wherever no pinched member exists — so its `anyOk` is
`false`, at every horizon `T`.  No trajectory enters the statement. -/
theorem anyOk_false_of_pinched_sound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {flag : ℕ → Bool} (hsound : ∀ k, flag k = true → PinchMem A u δ)
    (hno : ¬ PinchMem A u δ) (T : ℕ) :
    QMCLeafB.SimLoop.anyOk flag T = false := by
  rcases h : QMCLeafB.SimLoop.anyOk flag T with _ | _
  · rfl
  · obtain ⟨k, _hk, hk⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff flag T).1 h
    exact absurd (hsound k hk) hno

#print axioms QMCLeafB.BH35M5.anyOk_false_of_pinched_sound

/-- The same barrier at the leaf's own stratum predicate (`ThriceM3.PinchFeasible`). -/
theorem anyOk_false_of_pinchFeasible_sound {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {flag : ℕ → Bool}
    (hsound : ∀ k, flag k = true →
      QMCLeafB.ThriceM3.PinchFeasible G t P)
    (hno : ¬ QMCLeafB.ThriceM3.PinchFeasible G t P) (T : ℕ) :
    QMCLeafB.SimLoop.anyOk flag T = false := by
  rcases h : QMCLeafB.SimLoop.anyOk flag T with _ | _
  · rfl
  · obtain ⟨k, _hk, hk⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff flag T).1 h
    exact absurd (hsound k hk) hno

#print axioms QMCLeafB.BH35M5.anyOk_false_of_pinchFeasible_sound

/-! ## 1.  The released gate IS a pinched-candidate test

`Fal34B.relaxMem_diagPinch_of_releasedGate` proves that a gate-passing engine state yields a member
`cX` which is *definitionally* the state's own pinch `diagPinch (stMat n (stX s)) dq` (its
`RelaxMem` comes from `relaxMem_diagPinch_of_dsumGate`, whose conclusion literally displays
`diagPinch`).  Here that witness is exposed as `PinchMem`, with the two campaign-coherence slots
`stT s − epsOf s = u`, `dqOf s = dq` passed through unchanged. -/

/-- `dsum` on the state's own square code, from the gate register. -/
theorem dsum_of_gate {n : ℕ} {s : QMCLeafB.RoundProgram.RSt}
    (hN : QMCLeafB.RoundProgram.stN s = n)
    (hlenX : n ≤ (QMCLeafB.RoundProgram.stX s).length) {dq : ℚ}
    (hgate : QMCLeafB.RoundProgram.dvR s ≤ dq / 4) :
    QMCLeafB.Fal34B.dsum (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) ≤ dq / 4 := by
  have hdv := QMCLeafB.Fal34B.dvR_eq_dsum s (by rw [hN]; exact hlenX)
  rw [hN] at hdv
  rw [← hdv]
  exact hgate

#print axioms QMCLeafB.BH35M5.dsum_of_gate

/-- **The released gate certifies a PINCHED member.**  Same hypotheses as
`Fal34B.relaxMem_diagPinch_of_releasedGate`, conclusion `PinchMem` — the witness is the
programme's own `diagPinch`, so the diagonal is `1 − dq/4` by construction. -/
theorem pinchMem_of_releasedGate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {u dq : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = n)
    (hlenA : n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stA s) = A)
    (hAdiag : ∀ i, A i i = 0)
    (hgate : QMCLeafB.RoundProgram.dvR s ≤ dq / 4)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf
      (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) x)
    (hdqpos : 0 < dq) (hdq4 : dq ≤ 4)
    (hT : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq)
    (hfv : QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.OkLower.levelOf s) :
    PinchMem A u dq := by
  have hsum := dsum_of_gate hN hlenX hgate
  have htrace : QMCLeafB.SepOracle.frob A
      (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) ≤ u + dq / 2 := by
    have hf : QMCLeafB.RoundProgram.fvR s
        = QMCLeafB.SepOracle.frob (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stA s))
            (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) :=
      QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX
    have hl : QMCLeafB.OkLower.levelOf s
        = QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s
            + QMCLeafB.OkLower.dqOf s / 2 := rfl
    rw [hf, hA, hl, hT, hdq] at hfv
    linarith
  refine ⟨QMCLeafB.CentreAdm.diagPinch
      (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) dq, ?_, ?_⟩
  · exact QMCLeafB.Fal34B.relaxMem_diagPinch_of_dsumGate hdqpos hdq4 hAdiag hsum hpsd htrace
  · intro i
    exact QMCLeafB.CentreAdm.diagPinch_diag _ _ i

#print axioms QMCLeafB.BH35M5.pinchMem_of_releasedGate

/-! ## 2.  The dreg band: the bit horn is dead, trajectory-free

`DregM6.not_pinchFeasible` kills every `Δ < δ`, and `DregM6.not_bodyEmpty` keeps the body NONEMPTY
on the whole band.  Combining with §0: any register stream whose `true` rounds certify pinched
members is identically `false` at every band point, hence so is the bit.  Since the body is
nonempty there, the bit-horn hypothesis `¬ BodyEmpty → bit = true` is refuted. -/

/-- **No pinched member at the band, in `PinchMem` form.** -/
theorem dreg_no_pinchMem {Δ : ℚ} (hΔ : Δ < d0) :
    ¬ PinchMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq := by
  intro h
  exact QMCLeafB.DregM6.not_pinchFeasible Δ hΔ
    ((pinchMem_iff_pinchFeasible QMCLeafB.DregM6.G₁ (QMCLeafB.DregM6.tStar + Δ)
      QMCLeafB.DregM6.P₁).1 h)

#print axioms QMCLeafB.BH35M5.dreg_no_pinchMem

/-- **THE KILL.**  At every band point, a pinched-sound `ok` register reads `false` at every round
below every horizon: the bit of any such programme is `false` there. -/
theorem dreg_pinched_ok_false {Δ : ℚ} (hΔ : Δ < d0) {flag : ℕ → Bool}
    (hsound : ∀ k, flag k = true →
      PinchMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
        ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
        QMCLeafB.DregM6.P₁.dq) (T : ℕ) :
    QMCLeafB.SimLoop.anyOk flag T = false :=
  anyOk_false_of_pinched_sound hsound (dreg_no_pinchMem hΔ) T

#print axioms QMCLeafB.BH35M5.dreg_pinched_ok_false

/-- **The band's body is NONEMPTY** (`DregM6.not_bodyEmpty`, with the upper side condition derived
from `Δ < δ`). -/
theorem dreg_not_bodyEmpty {Δ : ℚ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ < d0) :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.DregM6.G₁
      (QMCLeafB.DregM6.tStar + Δ) QMCLeafB.DregM6.P₁ := by
  refine QMCLeafB.DregM6.not_bodyEmpty Δ ?_ ?_
  · exact_mod_cast hΔ0
  · have h1 : (Δ : ℝ) < ((d0 : ℚ) : ℝ) := by exact_mod_cast hΔ
    have h2 : ((d0 : ℚ) : ℝ) = 1 / 380000 := by norm_num [d0]
    have h3 : (1 / 380000 : ℝ) ≤ 2 + 3 * (1 / 380000 : ℝ) / 2 := by norm_num
    rw [h2] at h1
    linarith

#print axioms QMCLeafB.BH35M5.dreg_not_bodyEmpty

/-- **`hcomplete` FAILS at the band for every pinched-candidate programme.**  The bit-horn's
hypothesis (`¬ BodyEmpty → bit = true`) is refuted: the body is nonempty there, the bit is `false`.
This is the exact form `ThinRec34M4.hfalse_of_bit_complete` consumes, so that route cannot discharge
the thin stratum's `hfalse`. -/
theorem dreg_bit_complete_fails {Δ : ℚ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ < d0)
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool} {flag : ℕ → Bool} {T : ℕ}
    (hbit : o QMCLeafB.DregM6.G₁ (QMCLeafB.DregM6.tStar + Δ) = QMCLeafB.SimLoop.anyOk flag T)
    (hsound : ∀ k, flag k = true →
      PinchMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
        ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
        QMCLeafB.DregM6.P₁.dq) :
    ¬ (¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.DregM6.G₁
          (QMCLeafB.DregM6.tStar + Δ) QMCLeafB.DregM6.P₁
        → o QMCLeafB.DregM6.G₁ (QMCLeafB.DregM6.tStar + Δ) = true) := by
  intro hcomp
  have h1 := hcomp (dreg_not_bodyEmpty hΔ0 hΔ)
  rw [hbit, dreg_pinched_ok_false hΔ hsound T] at h1
  exact Bool.false_ne_true h1

#print axioms QMCLeafB.BH35M5.dreg_bit_complete_fails

/-! ## 3.  Where the band's members live: the TOP of the diagonal band

`DregM6.not_pinchFeasible` says the pinch `1 − δ/4` is impossible.  This section pins the other
edge: every rational member at the band has `Q₀₀ + Q₁₁ ≥ 2 + δ/2 − Δ` (while `diag_near` caps the
sum at `2 + δ/2`), so at `Δ = 0` BOTH diagonals are exactly `1 + δ/4`.  Consequences, machine
checked: the sum gate `dsum ≤ δ/4` rejects every member at `Δ = 0` (its `dsum` is `δ/2`), and the
band's member is not near the pinch at all — the pinch and the body are at OPPOSITE edges. -/

/-- The level `u + δ/2` at the band, in closed form. -/
theorem level_eq (Δ : ℚ) :
    ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
        + QMCLeafB.DregM6.P₁.dq / 2 = -(2 + 3 * (1 / 380000) / 2) + Δ := by
  rw [QMCLeafB.DregM6.eps_eq, QMCLeafB.DregM6.dq_eq]
  unfold QMCLeafB.DregM6.tStar
  ring

#print axioms QMCLeafB.BH35M5.level_eq

/-- `⟪wMatrixQ G₁, X⟫ = X₀₁ + X₁₀` on rational codes (the input has one edge, so `A` has zero
diagonal and unit off-diagonal). -/
theorem frob_wMatrixQ_G₁ (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      = Q 0 1 + Q 1 0 := by
  rw [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11]
  ring

#print axioms QMCLeafB.BH35M5.frob_wMatrixQ_G₁

/-- The `wMatrixQ G₁` diagonal vanishes (the gate lemma's `hAdiag`, discharged at the band). -/
theorem wMatrixQ_G₁_diag (i : Fin 2) :
    QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁ i i = 0 := by
  fin_cases i
  · exact QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00
  · exact QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11

#print axioms QMCLeafB.BH35M5.wMatrixQ_G₁_diag

/-- `qf` at the all-ones direction sums all four entries. -/
theorem qf_ones (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.qf Q (fun _ => (1 : ℚ)) = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  ring

#print axioms QMCLeafB.BH35M5.qf_ones

/-- **The objective bound at a member** (the level test in closed form). -/
theorem trace_le_G₁ {Δ : ℚ} {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) :
    Q 0 1 + Q 1 0 ≤ -(2 + 3 * (1 / 380000) / 2) + Δ := by
  have h := hQ.trace_le
  rw [frob_wMatrixQ_G₁, level_eq] at h
  exact h

#print axioms QMCLeafB.BH35M5.trace_le_G₁

/-- **THE TOP-EDGE LEMMA.**  Every rational member at the band has diagonal sum within `Δ` of the
TOP of the allowed box: `2 + δ/2 − Δ ≤ Q₀₀ + Q₁₁`.  (Combined with `diag_near`'s cap `2 + δ/2`
this pins the sum to the top edge as `Δ → 0`.) -/
theorem diag_sum_ge {Δ : ℚ} {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) :
    2 + (1 / 380000) / 2 - Δ ≤ Q 0 0 + Q 1 1 := by
  have hpsd := hQ.psd_margin (fun _ => (1 : ℚ))
  rw [qf_ones, show (∑ i : Fin 2, ((1 : ℚ)) ^ 2) = 2 from by norm_num,
    QMCLeafB.DregM6.dq_eq] at hpsd
  have htr := trace_le_G₁ hQ
  linarith

#print axioms QMCLeafB.BH35M5.diag_sum_ge

/-- The cap: `diag_near` at the band's tolerance. -/
theorem diag_le_top {Δ : ℚ} {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) (i : Fin 2) :
    Q i i ≤ 1 + (1 / 380000) / 4 := by
  have h := hQ.diag_near i
  rw [QMCLeafB.DregM6.dq_eq] at h
  have := (abs_le.1 h).2
  linarith

#print axioms QMCLeafB.BH35M5.diag_le_top

/-- **At `Δ = 0` the diagonal is EXACTLY the top edge** in every coordinate: the pinch `1 − δ/4`
is as far from the body as the box allows. -/
theorem diag_eq_top_zero {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) (i : Fin 2) :
    Q i i = 1 + (1 / 380000) / 4 := by
  have hge : 2 + (1 / 380000) / 2 - 0 ≤ Q 0 0 + Q 1 1 := diag_sum_ge hQ
  have h0 := diag_le_top hQ 0
  have h1 := diag_le_top hQ 1
  have hδ : (0 : ℚ) < 1 / 380000 := by norm_num
  have e0 : Q 0 0 = 1 + (1 / 380000) / 4 := by linarith
  have e1 : Q 1 1 = 1 + (1 / 380000) / 4 := by linarith
  fin_cases i
  · exact e0
  · exact e1

#print axioms QMCLeafB.BH35M5.diag_eq_top_zero

/-- **The sum gate `dvR ≤ δ/4` REJECTS every member at the band's bottom.**  Every member has
`dsum = 2·(δ/4) = δ/2 > δ/4`, so no `ok` test carrying the `dvR ≤ δ/4` gate can ever fire at a
matrix that is a member there — the gate, not only the candidate, has to move. -/
theorem sum_gate_rejects_dreg_member {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) :
    ¬ (QMCLeafB.Fal34B.dsum Q ≤ (1 / 380000) / 4) := by
  intro h
  have h0 := diag_eq_top_zero hQ 0
  have h1 := diag_eq_top_zero hQ 1
  have hδ : (0 : ℚ) < 1 / 380000 := by norm_num
  unfold QMCLeafB.Fal34B.dsum at h
  rw [Fin.sum_univ_two, h0, h1] at h
  have hpos : (0 : ℚ) < 1 + (1 / 380000) / 4 - 1 := by norm_num
  rw [abs_of_pos hpos] at h
  linarith

#print axioms QMCLeafB.BH35M5.sum_gate_rejects_dreg_member

/-! ## 4.  The repair, and why it is the *only* test-side repair

The band's member sits at the top edge (`§3`), so the certified candidate must be the state's own
matrix with its diagonal at `1 + δ/4` (`topPinch`), and the gate must be PER-COORDINATE
(`|Qᵢᵢ − 1| ≤ δ/4`, which accepts the band's member) rather than the sum gate (`δ/4`, which rejects
it, `§3`) or the sum gate at `δ/2` (which is not per-coordinate-sound for this candidate).  The
resulting test `TopGate` is proved here **exactly equivalent to "a rational member exists"**, so the
ok lane's soundness (`hok`) is free — and its completeness reduces to a pure REACH question. -/

/-- The state's own matrix with the diagonal overwritten to the TOP edge `1 + δ/4`. -/
def topPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if i = j then 1 + δ / 4 else Q i j

theorem topPinch_diag {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (i : Fin n) :
    topPinch Q δ i i = 1 + δ / 4 := by
  simp [topPinch]

#print axioms QMCLeafB.BH35M5.topPinch_diag

theorem topPinch_off {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} {i j : Fin n} (h : i ≠ j) :
    topPinch Q δ i j = Q i j := by
  simp [topPinch, h]

#print axioms QMCLeafB.BH35M5.topPinch_off

theorem qf_topPinch {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (topPinch Q δ) x
      = QMCLeafB.SepOracle.qf Q x + ∑ i, ((1 + δ / 4) - Q i i) * x i ^ 2 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, QMCLeafB.SepOracle.qf_eq_sum]
  have hinner : ∀ i : Fin n, ∑ j, x i * (topPinch Q δ i j * x j)
      = ∑ j, x i * (Q i j * x j) + ((1 + δ / 4) - Q i i) * x i ^ 2 := by
    intro i
    have hstep : ∑ j, x i * (topPinch Q δ i j * x j)
        = ∑ j, (x i * (Q i j * x j)
            + (if j = i then ((1 + δ / 4) - Q i i) * x i ^ 2 else 0)) := by
      refine Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => ?_)
      by_cases h : j = i
      · subst h
        rw [topPinch_diag]
        split_ifs with hh
        · ring
        · exact absurd rfl hh
      · rw [topPinch_off (Ne.symm h)]
        simp only [if_neg h, add_zero]
    rw [hstep, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  calc ∑ i, ∑ j, x i * (topPinch Q δ i j * x j)
      = ∑ i, (∑ j, x i * (Q i j * x j) + ((1 + δ / 4) - Q i i) * x i ^ 2) :=
        Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hinner i)
    _ = ∑ i, ∑ j, x i * (Q i j * x j) + ∑ i, ((1 + δ / 4) - Q i i) * x i ^ 2 :=
        Finset.sum_add_distrib

#print axioms QMCLeafB.BH35M5.qf_topPinch

theorem frob_topPinch {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (hA : ∀ i, A i i = 0) :
    QMCLeafB.SepOracle.frob A (topPinch Q δ) = QMCLeafB.SepOracle.frob A Q := by
  rw [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.frob]
  refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
  refine Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => ?_)
  by_cases h : i = j
  · subst h
    rw [topPinch_diag, hA i]
    ring
  · rw [topPinch_off h]

#print axioms QMCLeafB.BH35M5.frob_topPinch

/-- **The repaired `ok` test**: per-coordinate diagonal gate, certified relaxed PSD margin, level
test — all checked on the STATE'S OWN matrix `Q`, certified as `topPinch Q δ`. -/
def TopGate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ)
    (Q : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  0 < δ ∧ (∀ i, |Q i i - 1| ≤ δ / 4)
    ∧ (∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf Q x)
    ∧ QMCLeafB.SepOracle.frob A Q ≤ u + δ / 2

/-- **`hok` at the repaired test** (SOUNDNESS): a `TopGate` state yields a member — its own top-edge
matrix `topPinch Q δ`.  Nothing is lost relative to the pinch route: the diagonal is raised, which
only helps the PSD margin, and the objective is untouched because `wMatrixQ`'s diagonal vanishes. -/
theorem mem_of_topGate {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hA : ∀ i, A i i = 0) (h : TopGate A u δ Q) :
    QMCLeafB.RelaxOracle.RelaxMem A (topPinch Q δ) u δ where
  δ_pos := h.1
  psd_margin := by
    intro x
    have hcoef : ∀ i, (0 : ℚ) ≤ (1 + δ / 4) - Q i i := by
      intro i
      have := (abs_le.1 (h.2.1 i)).2
      linarith
    have hsum : (0 : ℚ) ≤ ∑ i, ((1 + δ / 4) - Q i i) * x i ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hcoef i) (sq_nonneg (x i)))
    rw [qf_topPinch]
    have := h.2.2.1 x
    linarith
  diag_near := by
    have hδ : 0 < δ := h.1
    intro i
    rw [topPinch_diag, show (1 + δ / 4) - 1 = δ / 4 from by ring, abs_of_pos (by linarith)]
  trace_le := by
    rw [frob_topPinch hA]
    exact h.2.2.2

#print axioms QMCLeafB.BH35M5.mem_of_topGate

/-- **Completeness of the repaired test against the body**: every member passes `TopGate` verbatim.
So `TopGate` is not a strengthening of the `ok` lane — it accepts every rational member, including
the band's top-edge one. -/
theorem topGate_of_mem {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ) : TopGate A u δ cX where
  left := h.δ_pos
  right := ⟨h.diag_near, h.psd_margin, h.trace_le⟩

#print axioms QMCLeafB.BH35M5.topGate_of_mem

/-- **THE EXACTNESS OF THE REPAIRED TEST.**  Body nonemptiness and `TopGate`-satisfiability are the
same proposition: the repaired `ok` test is sound AND complete as a test.  Hence the whole content of
`hcomplete` at the repaired programme is a REACH statement about the orbit — no test-side gap
remains. -/
theorem topGate_iff_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hA : ∀ i, A i i = 0) :
    (∃ Q : Matrix (Fin n) (Fin n) ℚ, TopGate A u δ Q)
      ↔ ∃ cX : Matrix (Fin n) (Fin n) ℚ, QMCLeafB.RelaxOracle.RelaxMem A cX u δ := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨topPinch Q δ, mem_of_topGate hA hQ⟩
  · rintro ⟨cX, hc⟩
    exact ⟨cX, topGate_of_mem hc⟩

#print axioms QMCLeafB.BH35M5.topGate_iff_mem

/-! ### 4b.  The band's RATIONAL member: the repaired test is inhabited there

`DregM6.not_bodyEmpty` proves the band's body nonempty over `ℝ` only.  Here the member is produced
over `ℚ`: `XQ Δ` is the band's top-edge point, and it is a genuine rational `RelaxMem` member — so
the repaired `ok` test *can* fire at the band, and `PinchMem` was the only reason the old one could
not.  This is also the non-vacuity receipt for `hok` at the repaired programme on the thin stratum. -/

/-- The band's top-edge witness, over `ℚ`: diagonal `1 + δ/4`, off-diagonal `−(1+3δ/4) + Δ/2`. -/
def XQ (Δ : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.of fun i j =>
    if i = j then 1 + (1 / 380000) / 4 else -(1 + 3 * (1 / 380000) / 4) + Δ / 2

theorem XQ_diag (Δ : ℚ) (i : Fin 2) : XQ Δ i i = 1 + (1 / 380000) / 4 := by
  simp [XQ]

#print axioms QMCLeafB.BH35M5.XQ_diag

theorem XQ_off {Δ : ℚ} {i j : Fin 2} (h : i ≠ j) :
    XQ Δ i j = -(1 + 3 * (1 / 380000) / 4) + Δ / 2 := by
  simp [XQ, h]

#print axioms QMCLeafB.BH35M5.XQ_off

/-- The `n = 2` algebraic core over `ℚ` (`qf_core` in `DregM6` is the `ℝ` version). -/
theorem qf_core_Q {d a x0 x1 : ℚ} (hd : 0 ≤ d) (ha : 0 ≤ a) (ha2 : a ≤ 2 + 3 * d / 2) :
    -(d / 2) * (x0 ^ 2 + x1 ^ 2)
      ≤ (1 + d / 4) * (x0 ^ 2 + x1 ^ 2) + (-(2 + 3 * d / 2) + a) * (x0 * x1) := by
  nlinarith [sq_nonneg (x0 - x1), sq_nonneg (x0 + x1),
    mul_nonneg (show (0 : ℚ) ≤ 1 + 3 * d / 4 - a / 4 by linarith) (sq_nonneg (x0 - x1)),
    mul_nonneg (show (0 : ℚ) ≤ a / 4 by linarith) (sq_nonneg (x0 + x1))]

#print axioms QMCLeafB.BH35M5.qf_core_Q

theorem qf_XQ (Δ : ℚ) (x : Fin 2 → ℚ) :
    QMCLeafB.SepOracle.qf (XQ Δ) x
      = (1 + (1 / 380000) / 4) * (x 0 ^ 2 + x 1 ^ 2)
        + (-(2 + 3 * (1 / 380000) / 2) + Δ) * (x 0 * x 1) := by
  rw [QMCLeafB.SepOracle.qf_eq_sum]
  simp only [Fin.sum_univ_two]
  simp only [XQ, Matrix.of_apply]
  simp
  ring

#print axioms QMCLeafB.BH35M5.qf_XQ

theorem frob_XQ (Δ : ℚ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) (XQ Δ)
      = -(2 + 3 * (1 / 380000) / 2) + Δ := by
  rw [frob_wMatrixQ_G₁,
    XQ_off (by decide : (0 : Fin 2) ≠ 1), XQ_off (by decide : (1 : Fin 2) ≠ 0)]
  ring

#print axioms QMCLeafB.BH35M5.frob_XQ

/-- **THE BAND HAS A RATIONAL MEMBER.**  `XQ Δ` satisfies all three `RelaxMem` clauses at the band's
own level `(t_Δ − ε, δ)`; its diagonal is the TOP edge `1 + δ/4` and its `dsum` is `δ/2` (so the sum
gate at `δ/4` rejects it, `§3`, while the per-coordinate gate accepts it). -/
theorem dreg_member_rational {Δ : ℚ} (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2 + 3 * (1 / 380000) / 2) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) (XQ Δ)
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq where
  δ_pos := by
    rw [QMCLeafB.DregM6.dq_eq]; norm_num
  psd_margin := by
    intro x
    rw [qf_XQ, QMCLeafB.DregM6.dq_eq]
    have hsq : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    rw [hsq]
    exact qf_core_Q (by norm_num) hΔ0 hΔ2
  diag_near := by
    intro i
    rw [QMCLeafB.DregM6.dq_eq]
    rw [XQ_diag]
    norm_num
  trace_le := by
    rw [frob_XQ, level_eq]

#print axioms QMCLeafB.BH35M5.dreg_member_rational

/-- The band's rational member passes the repaired `ok` test: the test is INHABITED on the thin
stratum, so repairing the candidate and the gate is not vacuous — only reach is missing. -/
theorem dreg_topGate_inhabited {Δ : ℚ} (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2 + 3 * (1 / 380000) / 2) :
    TopGate (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq (XQ Δ) :=
  topGate_of_mem (dreg_member_rational hΔ0 hΔ2)

#print axioms QMCLeafB.BH35M5.dreg_topGate_inhabited

/-- **The old gate is a PROPER restriction at the band**: the band's member passes the repaired
per-coordinate gate, while the released sum gate at `δ/4` rejects every member there (`§3`).  So the
`dvR ≤ dqOf/4` release is not repairable by the candidate change alone. -/
theorem dreg_coord_gate_accepts (Δ : ℚ) (i : Fin 2) :
    |XQ Δ i i - 1| ≤ (1 / 380000) / 4 := by
  rw [XQ_diag]
  norm_num

#print axioms QMCLeafB.BH35M5.dreg_coord_gate_accepts

/-! ## 5.  The exact gate is a special case (the campaign's `o33` is dead at the band too)

The phase-33 programme `PBit33M6.o33` reads its `ok` off `RoundProgram.verdict`, whose diagonal test
is the EXACT unit diagonal `dvR s = 0`.  That is the released gate at `dq/4` (for `dq ≥ 0`), so §1's
conclusion applies verbatim: the exact-gate programme also certifies pinched members, and therefore
also reads `false` at every band point. -/

/-- **The exact gate (`dvR = 0`) certifies a pinched member.** -/
theorem pinchMem_of_exactGate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {u dq : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = n)
    (hlenA : n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stA s) = A)
    (hAdiag : ∀ i, A i i = 0)
    (hgate : QMCLeafB.RoundProgram.dvR s = 0)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf
      (QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s)) x)
    (hdqpos : 0 < dq) (hdq4 : dq ≤ 4)
    (hT : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s = u)
    (hdq : QMCLeafB.OkLower.dqOf s = dq)
    (hfv : QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.OkLower.levelOf s) :
    PinchMem A u dq :=
  pinchMem_of_releasedGate hN hlenA hlenX hA hAdiag (by rw [hgate]; exact div_nonneg hdqpos.le (by norm_num))
    hpsd hdqpos hdq4 hT hdq hfv

#print axioms QMCLeafB.BH35M5.pinchMem_of_exactGate

/-- **The exact-gate bit is `false` at the band too** — the same trajectory-free kill. -/
theorem dreg_exactGate_ok_false {Δ : ℚ} (hΔ : Δ < d0) {flag : ℕ → Bool}
    (hsound : ∀ k, flag k = true →
      PinchMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
        ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
        QMCLeafB.DregM6.P₁.dq) (T : ℕ) :
    QMCLeafB.SimLoop.anyOk flag T = false :=
  dreg_pinched_ok_false hΔ hsound T

#print axioms QMCLeafB.BH35M5.dreg_exactGate_ok_false

/-! ## 6.  The residual, named exactly: a REACH theorem

`topGate_iff_mem` says the repaired test is exactly the membership predicate, and `§4b` says it is
inhabited at the band.  So the whole remaining content of the bit horn is: *does the campaign's orbit
visit a matrix satisfying `TopGate`?*  Below: the reach predicate, its equivalence with the bit, and
the fact that it is satisfiable (so no soundness or arithmetic obstruction remains). -/

/-- **The reach obligation** at a point: the orbit's state matrices include one passing `TopGate`. -/
def ReachTop {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ)
    (Q : ℕ → Matrix (Fin n) (Fin n) ℚ) (T : ℕ) : Prop :=
  ∃ k, k < T ∧ TopGate A u δ (Q k)

/-- The repaired bit reads `true` exactly when the orbit reaches `TopGate`. -/
theorem bit_true_iff_reach {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {Q : ℕ → Matrix (Fin n) (Fin n) ℚ} {T : ℕ} {flag : ℕ → Bool}
    (hflag : ∀ k, (flag k = true ↔ TopGate A u δ (Q k))) :
    QMCLeafB.SimLoop.anyOk flag T = true ↔ ReachTop A u δ Q T := by
  rw [QMCLeafB.SimLoop.anyOk_eq_true_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, (hflag k).1 h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, (hflag k).2 h⟩

#print axioms QMCLeafB.BH35M5.bit_true_iff_reach

/-- `ReachTop` is SATISFIABLE at any point where the repaired test is: the residual has no
arithmetic or soundness obstruction left, only the trajectory. -/
theorem reachTop_of_const {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    {Q : Matrix (Fin n) (Fin n) ℚ} (h : TopGate A u δ Q) {T : ℕ} (hT : 0 < T) :
    ReachTop A u δ (fun _ => Q) T :=
  ⟨0, hT, h⟩

#print axioms QMCLeafB.BH35M5.reachTop_of_const

/-- **The band's reach obligation is inhabited**: the constant orbit at the band's rational member
satisfies it.  So a programme whose orbit is that sequence closes the point — the *only* open input
is that the campaign's concrete orbit is such a sequence. -/
theorem dreg_reachTop_const {Δ : ℚ} (hΔ0 : 0 ≤ Δ) (hΔ2 : Δ ≤ 2 + 3 * (1 / 380000) / 2)
    {T : ℕ} (hT : 0 < T) :
    ReachTop (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁)
      ((QMCLeafB.DregM6.tStar + Δ) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq (fun _ => XQ Δ) T :=
  reachTop_of_const (dreg_topGate_inhabited hΔ0 hΔ2) hT

#print axioms QMCLeafB.BH35M5.dreg_reachTop_const

/-! ## 7.  Cost comparison (the recommendation, as a machine-checked ledger)

The two horns at a band point `(G₁, tStar + Δ)`:

| | record horn (`ShallowCut`) | bit horn (repaired `TopGate` programme) |
|---|---|---|
| program change | none (program-free, `ThinRec34M4.bodyRec_iff_recordDatum`) | TWO edits: candidate `diagPinch → topPinch`, gate `dsum ≤ δ/4 →` per-coordinate (`§3`, `§4`) |
| what must be proved | one support inequality per round, `del_k² ≤ rmax²·σ_k` | `ReachTop` at EVERY nonempty-body point (`hcomplete`) |
| available machinery | the ellipsoid's own centre/ledger (`Cat k`, `σ_k`), the normals free | none: the body is ball-free and cube-free (`DregM6.dreg_band`, `DregM6.no_ball`), so the volume/halving route cannot fire |
| obstruction | the ledger `del ≤ rmax·√σ` (shallow cuts only) | landing on a thin face — the banked analysis records thin bodies as volume-invisible |

Both horns are now *precisely* characterised, and the bit horn is strictly harder at the stratum:
its test-side content is fully eliminated (`topGate_iff_mem`, `dreg_topGate_inhabited`), leaving a
reach statement about a ball-free face that the campaign's own volume machinery cannot reach, while
the record horn's obligation is a per-round inequality with free normals.  **Recommendation: land
the record (`ShallowCut`); do not spend another phase on the bit horn at the dreg band.** -/


/-! ## 8.  (sharpens §3)  The band's body at `Δ = 0` is EXACTLY a segment, and every member is non-PSD

`diag_sum_ge` + `diag_le_top` pin the diagonal; the PSD clause at `(1,1)` and the level test pin the
OFF-DIAGONAL SUM.  Both inequalities close to equality, so the rational body at the band's bottom is
the segment

    `{ Q // Q₀₀ = Q₁₁ = 1 + δ/4,  Q₀₁ + Q₁₀ = −(2 + 3δ/2) }`

(one free parameter: the split between `Q₀₁` and `Q₁₀`) — and every point of it satisfies `RelaxMem`.
Consequences: (i) the body is 1-dimensional (thinner than any ball or cube), (ii) every member has
`qf Q ![1,1] = −δ < 0`, so **no exact-PSD matrix is a member at `Δ = 0`** — any `ok` test whose
certified candidate is required to be exactly PSD (the phase-27/32 `push_member` semantics, the
exact-gate descent's `hpsd`) is dead there too. -/

/-- **The off-diagonal sum is pinned** at the band's bottom. -/
theorem offdiag_sum_eq_zero {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) :
    Q 0 1 + Q 1 0 = -(2 + 3 * (1 / 380000) / 2) := by
  have hpsd := hQ.psd_margin (fun _ => (1 : ℚ))
  rw [qf_ones, show (∑ i : Fin 2, ((1 : ℚ)) ^ 2) = 2 from by norm_num,
    QMCLeafB.DregM6.dq_eq] at hpsd
  have h0 := diag_eq_top_zero hQ 0
  have h1 := diag_eq_top_zero hQ 1
  have htr := trace_le_G₁ hQ
  linarith

#print axioms QMCLeafB.BH35M5.offdiag_sum_eq_zero

/-- **Every member at the band's bottom is STRICTLY non-PSD** (`qf Q ![1,1] = −δ < 0`).  So the
exact-PSD candidate semantics cannot certify the band's body. -/
theorem member_strictly_not_psd {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq) :
    QMCLeafB.SepOracle.qf Q (fun _ => (1 : ℚ)) = -(1 / 380000) := by
  have hs := offdiag_sum_eq_zero hQ
  have h0 := diag_eq_top_zero hQ 0
  have h1 := diag_eq_top_zero hQ 1
  rw [qf_ones, h0, h1]
  linarith

#print axioms QMCLeafB.BH35M5.member_strictly_not_psd

/-- **The converse: the whole segment is in the rational body.**  Every symmetric `Q` with the
pinned diagonal and the pinned off-diagonal sum is a `RelaxMem` member at the band's bottom.  So the
member set there is exactly that segment — a complete description of the thin stratum's geometry at
the campaign's own numbers. -/
theorem segment_member {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hdiag : ∀ i : Fin 2, Q i i = 1 + (1 / 380000) / 4)
    (hsum : Q 0 1 + Q 1 0 = -(2 + 3 * (1 / 380000) / 2)) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.DregM6.G₁) Q
      ((QMCLeafB.DregM6.tStar + 0) - QMCLeafB.RundataCert.eps QMCLeafB.DregM6.G₁)
      QMCLeafB.DregM6.P₁.dq where
  δ_pos := by rw [QMCLeafB.DregM6.dq_eq]; norm_num
  psd_margin := by
    intro x
    rw [QMCLeafB.DregM6.dq_eq]
    have hsq : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    have hqf : QMCLeafB.SepOracle.qf Q x
        = (1 + (1 / 380000) / 4) * (x 0 ^ 2 + x 1 ^ 2)
          + (Q 0 1 + Q 1 0) * (x 0 * x 1) := by
      rw [QMCLeafB.SepOracle.qf_eq_sum]
      simp only [Fin.sum_univ_two]
      rw [hdiag 0, hdiag 1]
      ring
    rw [hsq, hqf, hsum]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1),
      mul_nonneg (show (0 : ℚ) ≤ 1 + 3 * (1 / 380000) / 4 by norm_num)
        (sq_nonneg (x 0 - x 1))]
  diag_near := by
    intro i
    rw [QMCLeafB.DregM6.dq_eq, hdiag i]
    norm_num
  trace_le := by
    rw [frob_wMatrixQ_G₁, level_eq, hsum]
    simp

#print axioms QMCLeafB.BH35M5.segment_member

end QMCLeafB.BH35M5


