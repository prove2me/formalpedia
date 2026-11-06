-- Prove2me | Definitions.Def_QMCLeafB_res33
-- name    : QMCLeafB_res33
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:34:25.091564+00:00
-- url     : https://prove2.me/theorems/4a069e75-5e65-4ad6-a763-67dd9c3e3041
-- title:
--   QMCLeafB res33
-- statement:
--   # `Check_res33_m4` — the leaf reduced to ONE slot, in one published-cone file
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_answer_producer
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_refuted_m3
/-
# `Check_res33_m4` — the leaf reduced to ONE slot, in one published-cone file

Phase 33's interface (`Sound31.solution_of_runPartsFamily`) asks for an `Automatic.Poly` bit plus a
`RunParts` family at **every** input and threshold.  This file reaches the same verbatim
`FinishLine.SolutionStatement`, on the published `Definitions/` cone, with the family's obligation
reduced to a single named slot and with the interface's vacuity traps removed.

## What is proved here

* **(A) is used, not assumed** (`round_member`): `RelaxOracle.relaxMem_witness` (`roundDiag`) plus
  the banked `paramsKbc2_budget`.  A symmetric rational `RelaxMem` at `(t - eps, dqShallow)` gives a
  genuine unit-diagonal PSD point at `t + eps`.  This retires `hok`/`Hpsd`/the grid: the program's
  `ok` test may be the cheap rational test at its own snapped centre.
* **`SoundAt`'s lower clause** (`bit_true_of_strict_below`): a port of
  `Sound31.bit_true_of_strict_below` onto the published bundles — no emptiness hypothesis.
* **The all-`ok` record** (`runParts_of_member`, `runParts_true`): bit `true` + a rational relaxed
  member gives the whole record.
* **The `false` record** (`runParts_false`): `EmptyBody` is the published
  `RefutedM3.runParts_of_emptyBody`; what is left over is the slot `hthin`.
* **THE STROKE** (`solution_of_slots`): the verbatim `FinishLine.SolutionStatement` from
  `ho` (`Automatic.Poly`), `hmem` (bit `true` implies a rational relaxed member), `hthin` (bit
  `false`, body nonempty implies a record), `hKm`.

## Why the family is demanded only on the bracket

`soundEpsOnBracket` reads a record only for `2 <= n` and `-Rq <= t <= 0`; everything else is settled
by `soundAt_of_le_one` (which reads no record).  Beyond that, demanding a record outside the bracket
is not merely unnecessary but **impossible**:

* at `Rq = 0` (no edges) the weight matrix vanishes, so `hcert` forces `0 <= t`; and at `t < 0` the
  relaxation body is still fat (the diagonal slab and the PSD margin survive), so a `false` bit
  contradicts `BallM2.no_runParts_of_ball`.  Hence **no `RunParts` exists at all** at `Rq = 0`,
  `t < 0` (down to `t >= -dq/2`), for any bit and any record data.  The `Rq = 0` bracket point
  `t = 0` is sound unconditionally instead (`soundAt_of_Rq_eq_zero`, via
  `zero_weight_of_Rq_eq_zero`), so it needs no record either.

## The residual, honestly

`hthin` is dischargeable only where the body is nonempty and does **not** contain the campaign ball
(`no_runParts_of_ball` forces the bit `true` wherever it does), i.e. on the ball-free thin band —
m6's dreg band.  That is the only open record content left.  On the `ok` side the remaining
obligation is a *reach* statement on the program: its bit must read `true` at ball-bearing bodies.
The cheap rational test makes that a far weaker demand than an exact-PSD/grid test.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom audit after every theorem.  Imports: `Mathlib` + published `Definitions.Def_QMCLeafB_*` only.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Res33M4

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

instance instRequestCodingRes : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 0.  The three predicates the family is keyed on -/

/-- **A symmetric rational relaxed member** at the campaign's level and tolerance. -/
def RatMember (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

/-- **The real relaxed body is empty** at the campaign's level and tolerance (the hypothesis
`QMCLeafB.RefutedM3.runParts_of_emptyBody` consumes). -/
def EmptyBody (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G) :
    Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X

/-- **The leaf's bracket**: the only range on which `SoundεOnBracket` reads a record. -/
def Bracket (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  -QMCLeafB.EngineRuntime.Rq G ≤ t ∧ t ≤ 0

theorem Rq_pos_of_bracket {G : QuantumMaxCutEnergy.Input} {t : ℚ} (h : Bracket G t)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) : 0 < QMCLeafB.EngineRuntime.Rq G :=
  lt_of_le_of_ne (QMCLeafB.EngineRuntime.Rq_nonneg G) (Ne.symm hRq)

#print axioms QMCLeafB.Res33M4.Rq_pos_of_bracket

/-! ## 1a.  The degenerate input: `Rq = 0` makes the bracket a point, where every bit is sound

At `Rq = 0` the bracket `-Rq ≤ t ≤ 0` is `{0}`, `eps = 0`, and `SoundAt` is *trivially* true for
every bit: the identity is a unit-diagonal PSD point of value `0 ≤ t + eps = 0`, and the weight
matrix is zero so every value is `0 = t - eps`.  No record is needed — which matters, because at
`Rq = 0` and `t < 0` (outside the bracket) no record exists at all: `hcert` would need `0 ≤ t`,
while a `false` bit contradicts `BallM2.no_runParts_of_ball` (the body is fat there).  This is why
the family below is demanded on the bracket only. -/

/-- `Rq = 0` forces every weight to vanish. -/
theorem zero_weight_of_Rq_eq_zero (G : QuantumMaxCutEnergy.Input)
    (h : QMCLeafB.EngineRuntime.Rq G = 0) :
    ∀ e : QuantumMaxCutEnergy.Edge G.n, G.weights e = 0 := by
  intro e
  have hsum : ∑ e, (((G.weights e : ℚ≥0)) : ℚ) = 0 := by
    unfold QMCLeafB.EngineRuntime.Rq at h
    linarith
  have hnonneg : ∀ e ∈ (Finset.univ : Finset (QuantumMaxCutEnergy.Edge G.n)),
      (0 : ℚ) ≤ (((G.weights e : ℚ≥0)) : ℚ) := by
    intro e _
    positivity
  have hterm : (((G.weights e : ℚ≥0)) : ℚ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum e (Finset.mem_univ e)
  have h2 : (((G.weights e : ℚ≥0)) : ℚ) = (((0 : ℚ≥0)) : ℚ) := by simpa using hterm
  exact_mod_cast h2

#print axioms QMCLeafB.Res33M4.zero_weight_of_Rq_eq_zero

theorem wMatrix_eq_zero_of_Rq_eq_zero (G : QuantumMaxCutEnergy.Input)
    (h : QMCLeafB.EngineRuntime.Rq G = 0) : QMCLeafB.wMatrix G = 0 := by
  have hw := zero_weight_of_Rq_eq_zero G h
  ext i j
  rw [QMCLeafB.wMatrix_apply]
  split_ifs <;> simp [hw]

#print axioms QMCLeafB.Res33M4.wMatrix_eq_zero_of_Rq_eq_zero

theorem trace_eq_zero_of_Rq_eq_zero (G : QuantumMaxCutEnergy.Input)
    (h : QMCLeafB.EngineRuntime.Rq G = 0) (Z : Matrix (Fin G.n) (Fin G.n) ℝ) :
    (QMCLeafB.wMatrix G * Z).trace = 0 := by
  rw [wMatrix_eq_zero_of_Rq_eq_zero G h]
  simp

#print axioms QMCLeafB.Res33M4.trace_eq_zero_of_Rq_eq_zero

/-- **Every bit is sound inside the bracket at `Rq = 0`.** -/
theorem soundAt_of_Rq_eq_zero (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hRq : QMCLeafB.EngineRuntime.Rq G = 0)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t) (hhi : t ≤ 0) :
    QMCLeafB.VerdictSound.SoundAt o G t := by
  have h0 : (0 : ℚ) ≤ t := by rw [hRq] at hlo; simpa using hlo
  have ht0 : t = 0 := le_antisymm hhi h0
  have htop : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) := by
    rw [hRq, ht0]; norm_num
  refine ⟨fun _ => QMCLeafB.VerdictSound.exists_trace_le_of_neg_eps_le G t htop, ?_⟩
  intro _ Z _
  rw [trace_eq_zero_of_Rq_eq_zero G hRq Z, hRq, ht0]
  norm_num

#print axioms QMCLeafB.Res33M4.soundAt_of_Rq_eq_zero

/-- **VACUITY RECEIPT**: at `Rq = 0` and `t < 0` no record can carry a `true` bit — `hcert` would
demand a unit-diagonal PSD point of value `≤ t + 0 < 0`, while the weight matrix vanishes, so every
value *is* `0`.  (The complementary half, `false` impossible there, is
`BallM2.no_runParts_of_ball`: at `Rq = 0` the relaxation still carries the diagonal slab and the PSD
margin, hence the campaign ball.  Together: the phase-33 obligation `forall G t, RunParts` is
unsatisfiable, which is why `solution_of_slots` quotes the family on the bracket only.) -/
theorem no_true_bit_of_Rq_zero {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hRq : QMCLeafB.EngineRuntime.Rq G = 0) (ht : t < 0)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t ≠ true := by
  intro hbit
  have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = true := by
    rw [← B.hverdict]; exact hbit
  obtain ⟨k, hk, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).1 hany
  obtain ⟨X, hX, htr⟩ := B.hcert k hk hok
  rw [trace_eq_zero_of_Rq_eq_zero G hRq X] at htr
  rw [hRq] at htr
  have ht' : ((t : ℚ) : ℝ) < 0 := by exact_mod_cast ht
  push_cast at htr
  linarith

#print axioms QMCLeafB.Res33M4.no_true_bit_of_Rq_zero

/-! ## 2.  Lemma (A): `RatMember` gives a genuine unit-diagonal PSD point at `t + eps` -/

/-- **LEMMA (A)**, inlined (no `Solutions.` import): `RelaxOracle.relaxMem_witness` composed with the
banked `paramsKbc2_budget`. -/
theorem round_member (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (hmem : RatMember G t) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
  obtain ⟨cX, hCsym, h⟩ := hmem
  have hAsym : (QMCLeafB.Finalization.wMatrixQ G)ᵀ = QMCLeafB.Finalization.wMatrixQ G :=
    QMCLeafB.Finalization.IsQMCWeight.symm (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G)
  have hdiag : ∀ i : Fin G.n, QMCLeafB.Finalization.wMatrixQ G i i = 0 :=
    fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq
  have hbudget := QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq
  have hbudget' : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * QMCLeafB.RundataParams.dqShallow G / 4)
      + QMCLeafB.RundataParams.dqShallow G / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G := hbudget
  obtain ⟨X, hX, htr⟩ := QMCLeafB.RelaxOracle.relaxMem_witness
    (A := QMCLeafB.Finalization.wMatrixQ G) (cX := cX)
    (u := t - QMCLeafB.RundataCert.eps G) (δ := QMCLeafB.RundataParams.dqShallow G)
    h hAsym hCsym hdiag
  refine ⟨X, hX, ?_⟩
  rw [← QMCLeafB.Finalization.wMatrix_castM G]
  have hq : t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallow G / 2
      + QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
          (3 * QMCLeafB.RundataParams.dqShallow G / 4)
      ≤ t + QMCLeafB.RundataCert.eps G := by linarith [hbudget']
  have hr : (((t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallow G / 2
      + QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
          (3 * QMCLeafB.RundataParams.dqShallow G / 4) : ℚ)) : ℝ)
      ≤ (t : ℝ) + ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ) := by
    exact_mod_cast hq
  have hr' : (((t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallow G / 2
      + QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
          (3 * QMCLeafB.RundataParams.dqShallow G / 4) : ℚ)) : ℝ)
      ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := hr
  linarith

#print axioms QMCLeafB.Res33M4.round_member

/-! ## 2.  `SoundAt`'s lower clause: a strict-below point forces the bit `true` -/

/-- Port of `Sound31.ball_of_strict_below` onto the published bundles. -/
theorem ball_of_strict_below {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (P : QMCLeafB.FinalStroke.RunParams G)
    {Z : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hZ : QMCLeafB.AnswerProducer.IsUnitDiagPSD Z)
    (htr : (QMCLeafB.wMatrix G * Z).trace
      < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat Z)
        (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t P := by
  have hδ : (0 : ℝ) < ((P.dq : ℚ) : ℝ) := by exact_mod_cast P.hdq
  have hcA : (0 : ℝ) ≤ ((P.cAq : ℚ) : ℝ) := by exact_mod_cast P.hcAq
  have hmem : QMCLeafB.AnswerProducer.StrictBody (QMCLeafB.wMatrix G) t
      (QMCLeafB.EngineRuntime.Rq G / 40000) (QMCLeafB.AnswerProducer.flat Z) :=
    ⟨Z, hZ, le_of_lt htr, rfl⟩
  have hM : 2 * (((G.n : ℝ)) ^ 2 + (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ 2)
      ≤ ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ) := by
    push_cast
    have h1 : (0 : ℝ) < ((P.cAq : ℚ) : ℝ) + 1 := by linarith
    have h2 : (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ 2
        ≤ ((P.dq : ℚ) : ℝ) ^ 2 := by
      have h3 : (1 : ℝ) ≤ 8 * (((P.cAq : ℚ) : ℝ) + 1) := by nlinarith
      have h4 : (0 : ℝ) < 8 * (((P.cAq : ℚ) : ℝ) + 1) := by linarith
      have h5 : ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) ≤ ((P.dq : ℚ) : ℝ) := by
        rw [div_le_iff₀ h4]; nlinarith [hδ.le]
      have h6 : (0 : ℝ) ≤ ((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)) := by positivity
      nlinarith
    nlinarith
  exact QMCLeafB.Boundary.strictBody_ball_relaxBall (t := t)
    (εr := QMCLeafB.EngineRuntime.Rq G / 40000) (δq := P.dq) (cA := ((P.cAq : ℚ) : ℝ))
    hδ hcA (by simpa using P.hAsum) hM hmem

#print axioms QMCLeafB.Res33M4.ball_of_strict_below

/-- **A strict-below point forces the bit `true`** (port of
`Sound31.bit_true_of_strict_below`). -/
theorem bit_true_of_strict_below {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P)
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    o G t = true := by
  obtain ⟨Z, hZ, htr⟩ := hstrict
  exact QMCLeafB.BallM2.no_runParts_of_ball hn
    (ball_of_strict_below (G := G) (t := t) P (Z := Z) hZ htr) B

#print axioms QMCLeafB.Res33M4.bit_true_of_strict_below

/-! ## 3.  The all-`ok` record (the `M` class), on the published bundles -/

theorem anyOk_const_true : ∀ T : ℕ, 0 < T →
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) T = true
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | (k + 1), _ => by rw [QMCLeafB.SimLoop.anyOk_succ]; rfl

#print axioms QMCLeafB.Res33M4.anyOk_const_true

/-- **The record at an `ok` point.**  All-`ok` stream, every cut slot vacuous, `hcert` the one
member (the published `RunPartsDilate.runCut` supplies the witness stream). -/
noncomputable def runParts_of_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hKm : 1 ≤ Q.K * Q.m)
    (hbit : o G t = true)
    (hmem : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.FinalStroke.RunParts o G t Q := by
  classical
  have hN : 2 ≤ G.n * G.n := by have := hn; nlinarith
  haveI : NeZero (G.n * G.n) := ⟨by omega⟩
  set c : ℕ → Fin (G.n * G.n) → ℚ := fun _ => QMCLeafB.RefutedM3.e₀ (G.n * G.n) with hc
  have hcne : ∀ k : ℕ, c k ≠ 0 := fun _ => QMCLeafB.RefutedM3.e₀_ne (G.n * G.n)
  set cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
    QMCLeafB.RunPartsDilate.runCut G Q hn c hcne with hcd
  have hrunwit : ∀ k,
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * Q.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c :=
    fun k => QMCLeafB.RunPartsDilate.runCut_wit G Q hn c hcne k
  exact
    { ok := fun _ => true
      cd := cd
      del := fun _ => 0
      hcert := by intro k _ _; exact hmem
      hwit := by intro k _ hok; exact absurd hok (by simp)
      hrho := by intro k _ hok; exact absurd hok (by simp)
      hcne := by intro k _ hok; exact absurd hok (by simp)
      hdel0 := by intro k _ hok; exact absurd hok (by simp)
      hcheck := by intro k _ hok; exact absurd hok (by simp)
      hle := by intro k _ hok; exact absurd hok (by simp)
      hcut := by intro k _ hok; exact absurd hok (by simp)
      hverdict := by
        rw [hbit]
        exact (anyOk_const_true (Q.K * Q.m) (by omega)).symm }

#print axioms QMCLeafB.Res33M4.runParts_of_member

/-- **(A)'s payoff**: a rational relaxed member plus a `true` bit gives the whole record at the
campaign parameters.  No exact witness, no emptiness, no thin-body analysis. -/
noncomputable def runParts_true {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : o G t = true) (hmem : RatMember G t) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  runParts_of_member (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hbit
    (round_member G t hn hRq hmem)

#print axioms QMCLeafB.Res33M4.runParts_true

/-! ## 4.  The `false` bit: empty (published) or the thin band (the last slot) -/

/-- **The record at a `false` bit**, from emptiness plus the thin-band slot. -/
noncomputable def runParts_false {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hbit : o G t = false)
    (hthin : ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  by_cases he : EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)
  · refine QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn hbit ?_
    intro X hX
    exact he X hX
  · exact hthin he

#print axioms QMCLeafB.Res33M4.runParts_false

/-- **The whole family from TWO slots, on the interior bracket only.**  The bracket forces
`0 < Rq` (`Rq_pos_of_interior`), so the degenerate `Rq = 0` corner — where no record can exist at
`t < 0` — is never queried. -/
noncomputable def runParts_family {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hmem : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = true → RatMember G t)
    (hthin : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) (hB : Bracket G t)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≠ 0) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  by_cases hb : o G t = true
  · exact runParts_true G t hn (Rq_pos_of_bracket hB hRq) hb (hmem G t hn hb)
  · have hfl : o G t = false := by
      cases h : o G t with
      | false => rfl
      | true => exact absurd h hb
    exact runParts_false G t hn hfl (fun he => hthin G t hn hfl he)

#print axioms QMCLeafB.Res33M4.runParts_family

/-! ## 5.  `SoundAt`, `SoundεOnBracket`, and the leaf -/

/-- **`SoundAt` from one record** (port of `Sound31.soundAt_of_runParts`, with `0 < K·m` explicit). -/
theorem soundAt_of_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P) (hKm : 0 < P.K * P.m) :
    QMCLeafB.VerdictSound.SoundAt o G t := by
  constructor
  · intro htrue
    have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = true := by
      rw [← B.hverdict]; exact htrue
    obtain ⟨k, hk, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).1 hany
    exact B.hcert k hk hok
  · intro hfalse Z hZ
    by_contra hlt
    push Not at hlt
    have htrue := bit_true_of_strict_below P hn B ⟨Z, hZ, hlt⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue

#print axioms QMCLeafB.Res33M4.soundAt_of_runParts

/-- **`SoundεOnBracket`** from the record family on the bracket and the `2 ≤ n` stratum — exactly
where the stroke reads it.  The `Rq = 0` corner is discharged without any record
(`soundAt_of_Rq_eq_zero`). -/
theorem soundEpsOnBracket_of_family {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (B : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n → ∀ t : ℚ, Bracket G t →
      QMCLeafB.EngineRuntime.Rq G ≠ 0 →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hKm : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n →
      0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · by_cases hRq : QMCLeafB.EngineRuntime.Rq G = 0
    · exact soundAt_of_Rq_eq_zero o hRq hlo hhi
    · exact soundAt_of_runParts (QMCLeafB.UnionShallow.paramsKbc2 G) hn
        (B G hn t ⟨hlo, hhi⟩ hRq) (hKm G hn)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms QMCLeafB.Res33M4.soundEpsOnBracket_of_family

/-- **THE STROKE — the whole leaf from ONE open slot.**

```
ho    : the bit is Automatic.Poly                        (direction d3 / the program)
hmem  : bit true ==> a symmetric rational RelaxMem        (the cheap ok-test's soundness; (A) turns it
                                                          into the witness RunParts.hcert needs)
hthin : bit false, body NONEMPTY ==> RunParts            <-- THE LAST SLOT (the ball-free thin band)
```

concluding the verbatim `FinishLine.SolutionStatement`.  Both slots are demanded only inside the
interior bracket and only for `2 <= n`, which is exactly where the stroke reads them; everywhere else
the leaf's `SoundAt` is either settled by `soundAt_of_le_one` or reads no record. -/
theorem solution_of_slots (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hmem : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = true → RatMember G t)
    (hthin : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hKm : ∀ (G : QuantumMaxCutEnergy.Input), 2 ≤ G.n →
      0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (soundEpsOnBracket_of_family
      (fun G hn t hB hRq => runParts_family hmem hthin G t hn hB hRq) hKm) ho

#print axioms QMCLeafB.Res33M4.solution_of_slots

end QMCLeafB.Res33M4


