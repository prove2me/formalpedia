-- Prove2me | Definitions.Def_QMCLeafB_aud39
-- name    : QMCLeafB_aud39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:17:59.820932+00:00
-- url     : https://prove2.me/theorems/a8ab8a2e-ef7d-4fb3-9fa2-0b4c1f75f333
-- title:
--   QMCLeafB aud39
-- statement:
--   # `Check_aud39_m8` — phase 39, member m8, direction d4 (`audit39`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_Core
import Definitions.Def_QMCLeafB_answer_producer
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_anchorfacts
import Definitions.Def_QMCLeafB_face36
import Definitions.Def_QMCLeafB_b1d37
import Definitions.Def_QMCLeafB_dich37
import Definitions.Def_QMCLeafB_rf38
/-
# `Check_aud39_m8` — phase 39, member m8, direction d4 (`audit39`)

**Audit verdict: `SepStream` IS FALSE — for every programme, every stream, every `t`-class that
carries a ball.  `solution_of_separating` (`Check_rf38_m1`) is therefore VACUOUS, and the leaf is
NOT closed by that route.**

The audit chain uses only banked, published theorems, and no new analysis:

1. `Bypass35M6.shallowCut_of_separating` — a separating rational normal stream at the accumulated
   centres gives `ShallowCut` with `del ≡ 0` (`Def_QMCLeafB_by35`).
2. `ThinRec34M4.bodyRec_of_shallowCut` — any `ShallowCut` manufactures the ALL-FALSE record
   (`BodyRec`, i.e. `Nonempty (RunParts falseBit …)`) (`Def_QMCLeafB_thinrec34`).
3. `ThinRec34M4.not_bodyRec_of_ball` / `BallM2.no_runParts_of_ball` — a body carrying a Euclidean
   ball of the campaign radius `dq/(8(c_A+1))` admits NO all-false record: the ellipsoid always
   contains the body, halves its volume potential each round, and must still contain the ball
   (`Def_QMCLeafB_thinrec34`, `Def_QMCLeafB_ball_m2`).

(1)+(2)+(3) at ONE ball-bearing pair `(G,t)` contradict each other, and `SepStream` quantifies over
**every** `t : ℚ` (not only the bracket), so the object is uninhabited.  Two independent witnesses
are machine-checked below:

* `not_sepStream_unconditional` — at `t = 2·Rq G` the identity matrix is a strict interior point of
  the relaxation, so the body carries the campaign ball for **every** `RunParams` `P` and every
  input `G` with `2 ≤ G.n` (no programme hypothesis at all);
* `not_sepStream_paramsKbc2` — the CAMPAIGN family, at the sliver `(G₁, t₁)`: a *bracketed*,
  body-nonempty point.  So not even restricting `SepStream` to the bracket rescues it at the
  campaign's own parameters.

The programme change this forces is stated in §5–§6: the object must be `SepStream` restricted to
the ball-free stratum (the collar), and the ball-bearing stratum must be served by the *bit* horn.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every theorem (all exactly `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Aud39M8

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (BodyRec ShallowCut relaxBallP NormalCut)

/-! ## 1.  Statement lock: the object, verbatim, and the leaf's wiring

`Check_rf38_m1` is the leaf's last form and has **no published mirror** (`Definitions/` has no
`Def_QMCLeafB_rf38`), so this file imports the Check module directly and locks its `SepStream`
against the spelled-out quantifier of the phase-38/39 charter by `Iff.rfl`. -/

/-- **THE LEAF'S LAST OBJECT, VERBATIM.**  Definitionally the charter's sentence. -/
theorem sepStream_lock
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    QMCLeafB.Rf38M1.SepStream P c hc
      ↔ ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
          ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
            (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
                Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
                  (NormalCut G (P G) hn (c G t) (hc G t)) k
              ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z :=
  Iff.rfl

#print axioms QMCLeafB.Aud39M8.sepStream_lock

/-! ## 2.  THE REFUTATION, generic form: a ball in the body kills the stream -/

/-- **SEPARATION DIES AT EVERY BALL-BEARING BODY.**  For every programme `P`, every nonzero
rational stream `c`, and every pair `(G,t)` whose relaxation carries the campaign ball, the
separation demanded by `SepStream` is impossible.  No programme hypothesis, no bracket, no bit. -/
theorem not_sepStream_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  refine QMCLeafB.ThinRec34M4.not_bodyRec_of_ball (G := G) (t := t) (P := P G) hn hball ?_
  exact QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut (G := G) (t := t) (P := P G) hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (G := G) (t := t) (P := P G) hn
      (c G t) (hc G t) (hsep G t hn))

#print axioms QMCLeafB.Aud39M8.not_sepStream_of_ball

/-! ## 3.  A ball-bearing body at every programme: the fat point `t = 2·Rq G`

`SepStream` quantifies over **all** `t : ℚ`, not only the bracket.  At `t = 2·Rq G` the identity
matrix is a strict interior point of the relaxation: it is unit-diagonal PSD, its objective is
`tr (A·1) = tr A = 0 ≤ 2·Rq − Rq/40000`, and the norm bound has room.  So the body carries the
campaign ball at *every* `RunParams`, which is what makes the refutation programme-free. -/

/-- The identity is a strict body point at `t = 2·Rq G` (`StrictBody` at margin `Rq/40000`). -/
theorem strictBody_id_fatPoint {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) :
    QMCLeafB.AnswerProducer.StrictBody (QMCLeafB.wMatrix G)
      (2 * QMCLeafB.EngineRuntime.Rq G) (QMCLeafB.EngineRuntime.Rq G / 40000)
      (QMCLeafB.AnswerProducer.flat (1 : Matrix (Fin G.n) (Fin G.n) ℝ)) := by
  refine ⟨1, QMCLeafB.AnswerProducer.isUnitDiagPSD_one, ?_, rfl⟩
  rw [Matrix.mul_one]
  have htr : (QMCLeafB.wMatrix G).trace = 0 := by
    rw [Matrix.trace]
    exact Finset.sum_eq_zero fun i _ => QMCLeafB.wMatrix_apply_of_eq
  rw [htr]
  have hR : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.EngineRuntime.Rq_nonneg G
  have hR' : (0 : ℝ) ≤ ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by exact_mod_cast hR
  have hgoal : ((0 : ℚ) : ℝ) ≤ ((2 * QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      - ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) := by
    push_cast
    nlinarith
  linarith

#print axioms QMCLeafB.Aud39M8.strictBody_id_fatPoint

/-- **EVERY PROGRAMME HAS A BALL-BEARING BODY.**  At `t = 2·Rq G` the relaxation contains the
Euclidean ball of the campaign's own radius `dq/(8(c_A+1))` about `flat 1`. -/
theorem ball_at_fatPoint {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n)
    (P : QMCLeafB.FinalStroke.RunParams G) :
    QMCLeafB.Boundary.eucBallF
        (QMCLeafB.AnswerProducer.flat (1 : Matrix (Fin G.n) (Fin G.n) ℝ))
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G (2 * QMCLeafB.EngineRuntime.Rq G) P := by
  have hδ : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
  have hcA : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
  have hden : (0 : ℝ) < 8 * ((P.cAq : ℝ) + 1) := by linarith
  have hdq : (0 : ℝ) < (P.dq : ℝ) := hδ
  have hle : (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) ≤ (P.dq : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hr0 : (0 : ℝ) ≤ (P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1)) := by positivity
  have hsq : ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ^ 2 ≤ (P.dq : ℝ) ^ 2 := by
    nlinarith
  have hM : 2 * (((G.n : ℝ)) ^ 2 + ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ^ 2)
      ≤ (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) := by
    push_cast
    nlinarith
  simpa [QMCLeafB.BallM2.runBall] using
    QMCLeafB.Boundary.strictBody_ball_relaxBall (n := G.n) (A := QMCLeafB.wMatrix G)
      (t := 2 * QMCLeafB.EngineRuntime.Rq G) (εr := QMCLeafB.EngineRuntime.Rq G / 40000)
      (δq := P.dq) hδ (cA := (P.cAq : ℝ)) hcA (by simpa using P.hAsum)
      (M := (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ)) hM
      (strictBody_id_fatPoint hn)

#print axioms QMCLeafB.Aud39M8.ball_at_fatPoint

/-! ## 4.  THE REFUTATION, unconditional: `SepStream` is uninhabited -/

/-- **`SepStream` IS FALSE — no programme, no stream, ever.**  For every family `P` and every
nonzero rational stream `c`, at any input with `2 ≤ G.n`, at `t = 2·Rq G`. -/
theorem not_sepStream_unconditional
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc :=
  not_sepStream_of_ball (P := P) (c := c) (hc := hc)
    (t := 2 * QMCLeafB.EngineRuntime.Rq G) hn
    (X₀ := 1) (ball_at_fatPoint hn (P G))

#print axioms QMCLeafB.Aud39M8.not_sepStream_unconditional

/-- **THE HYPOTHESIS OF `solution_of_separating` IS EMPTY.**  For every programme there is NO
nonzero rational normal stream satisfying `SepStream` (`G₁`'s `2 ≤ n` is the only input fact used). -/
theorem sepStream_uninhabited
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) :
    ¬ ∃ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
        (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0),
        QMCLeafB.Rf38M1.SepStream P c hc := by
  rintro ⟨c, hc, hsep⟩
  exact not_sepStream_unconditional P c hc QMCLeafB.AnchorFactsM2.hn₁ hsep

#print axioms QMCLeafB.Aud39M8.sepStream_uninhabited

/-- **THE CAMPAIGN FAMILY, AT A BRACKETED BODY-NONEMPTY POINT.**  Even if `SepStream` were
restricted to the leaf's bracket, the campaign family at the sliver `(G₁, t₁)` refutes it: that
body carries the campaign ball at its own radius (`BallM2.sliver_ball_campaign`). -/
theorem not_sepStream_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ QMCLeafB.Rf38M1.SepStream QMCLeafB.UnionShallow.paramsKbc2 c hc :=
  not_sepStream_of_ball (P := QMCLeafB.UnionShallow.paramsKbc2) (c := c) (hc := hc)
    (G := QMCLeafB.AnchorFactsM2.G₁) (t := QMCLeafB.AnchorFactsM2.t₁)
    QMCLeafB.AnchorFactsM2.hn₁ (X₀ := QMCLeafB.BallM2.Xs)
    QMCLeafB.BallM2.sliver_ball_campaign

#print axioms QMCLeafB.Aud39M8.not_sepStream_paramsKbc2

/-! ## 5.  Non-vacuity of the PREDICATE: `SepStream` is not self-contradictory

The refutation of §4 is caused by ball-bearing bodies, not by an inconsistent predicate: on a
programme whose relaxations are all empty, EVERY stream satisfies `SepStream`.  So the object is
\"true on the empty-body stratum and false on the ball stratum\" — which is exactly the programme
change: the hypothesis must be restricted to the ball-free (collar) stratum. -/

/-- `SepStream` holds whenever every relaxation is empty — for any nonzero rational stream. -/
theorem sepStream_of_emptyBody
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), relaxBallP G t (P G) = ∅) :
    QMCLeafB.Rf38M1.SepStream P c hc := by
  intro G t hn k hk z hz
  rw [hempty G t] at hz
  simp at hz

#print axioms QMCLeafB.Aud39M8.sepStream_of_emptyBody

/-- **THE DOMAIN OF `SepStream`, EXACTLY: BALL-FREE BODIES ONLY.**  A stream obeying `SepStream`
cannot coexist with a single body carrying the campaign ball, at any `t`. -/
theorem sepStream_ball_free
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : QMCLeafB.Rf38M1.SepStream P c hc)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    False :=
  not_sepStream_of_ball P c hc hn hball hsep

#print axioms QMCLeafB.Aud39M8.sepStream_ball_free

/-! ## 6.  RECEIPTS — the live statements the refutation consumes, and the leaf's own wiring

`#check` locks (Lean-side statement records).  Each is a published `Definitions.*` declaration
except `Rf38M1.*` (the leaf's last form has no mirror yet — see §1). -/

#check @QMCLeafB.Bypass35M6.shallowCut_of_separating
#check @QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut
#check @QMCLeafB.ThinRec34M4.not_bodyRec_of_ball
#check @QMCLeafB.BallM2.no_runParts_of_ball
#check @QMCLeafB.BallM2.sliver_ball_campaign
#check @QMCLeafB.Boundary.strictBody_ball_relaxBall
#check @QMCLeafB.Rf38M1.selfRecG_of_separating
#check @QMCLeafB.Rf38M1.no_selfRecG_of_ball
#check @QMCLeafB.Rf38M1.solution_of_separating
#check @QMCLeafB.Rf38M1.round_zero_separation
#check @QMCLeafB.Dich37M1.solution_of_gate_recSlot
#check @QMCLeafB.B1D37M5.isSquare_sigma_of_rational_step
#check @QMCLeafB.B1D37M5.runParams_rmax_lt_one
#check @QMCLeafB.B1D37M5.runParts_del_le_rmax_sqrt

/-- **THE CONTRADICTION INSIDE `Check_rf38_m1`, made explicit.**  `Rf38M1.no_selfRecG_of_ball`
(refuted record at a ball-bearing bit-false point) and `Rf38M1.selfRecG_of_separating` (record from
`SepStream`) cannot both hold: at every ball-bearing bit-false bracketed point the supporting-stream
hypothesis of `solution_of_separating` is refuted.  This is the leaf-internal shadow of §4. -/
theorem not_selfRecG_and_sepStream
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc :=
  not_sepStream_of_ball P c hc hn hball

#print axioms QMCLeafB.Aud39M8.not_selfRecG_and_sepStream


/-! ## 7.  The SECOND branch of `Check_rf38_m1` is refuted the same way

`Rf38M1.solution_of_trace` replaces the supporting stream by the constant TRACE direction with a
cumulative trace ceiling `hTrc`.  `Bypass35M6.shallowCut_of_trace` turns that ceiling into
`ShallowCut`, hence into the all-false record, hence into the same ball contradiction — at the fat
point, for EVERY programme.  So both horns of the phase-38 file are uninhabited. -/

/-- **THE TRACE-CEILING HYPOTHESIS IS EMPTY.**  The `hTrc` that `Rf38M1.solution_of_trace`
consumes holds for no programme. -/
theorem traceCeiling_uninhabited
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) :
    ¬ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
        ∀ k, k < (P G).K * (P G).m →
          ∑ i, QMCLeafB.Boundary.unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (QMCLeafB.Bypass35M6.traceStream G.n)
              (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) k) i i
          ≤ (G.n : ℝ) * (1 - (((P G).dq : ℚ) : ℝ) / 4)) := by
  intro hTrc
  have hB : BodyRec QMCLeafB.AnchorFactsM2.G₁
      (2 * QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁)
      (P QMCLeafB.AnchorFactsM2.G₁) :=
    QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut (P := P QMCLeafB.AnchorFactsM2.G₁)
      QMCLeafB.AnchorFactsM2.hn₁
      (QMCLeafB.Bypass35M6.shallowCut_of_trace (G := QMCLeafB.AnchorFactsM2.G₁)
        (t := 2 * QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁)
        (P := P QMCLeafB.AnchorFactsM2.G₁) QMCLeafB.AnchorFactsM2.hn₁
        (hTrc QMCLeafB.AnchorFactsM2.G₁
          (2 * QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁) QMCLeafB.AnchorFactsM2.hn₁))
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball (G := QMCLeafB.AnchorFactsM2.G₁)
    (t := 2 * QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁)
    (P := P QMCLeafB.AnchorFactsM2.G₁) QMCLeafB.AnchorFactsM2.hn₁
    (ball_at_fatPoint QMCLeafB.AnchorFactsM2.hn₁ (P QMCLeafB.AnchorFactsM2.G₁)) hB

#print axioms QMCLeafB.Aud39M8.traceCeiling_uninhabited


/-! ## 8.  The refutation is SHARP: the surviving stratum is inhabited

The refutation of §4 is caused solely by ball-bearing bodies.  The complement — a bracketed point
with a NONEMPTY, ball-free body — is inhabited and already carries a record: the phase-36 face
`(G₁, tStar)` of `Check_face36_m2` (`face_summary`, `face_no_ball`).  So the programme change this
audit forces is exactly:

* ball-bearing bodies: the bit must read TRUE (`BallM2.no_runParts_of_ball`), and NO stream can
  separate (`not_sepStream_of_ball` above);
* ball-free bodies: separation is not excluded by this audit, and the record exists there
  (`Face36M2.bodyRec_of_level`).

That is the phase-24..37 two-horn architecture, re-derived from the leaf's own last object. -/

/-- **THE SURVIVING DOMAIN IS INHABITED.**  A bracketed point whose relaxation is nonempty and
carries no ball of positive radius — the only place a supporting stream is not excluded. -/
theorem ballFree_stratum_inhabited :
    ∃ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G),
      -QMCLeafB.EngineRuntime.Rq G ≤ t
      ∧ t < -(QMCLeafB.EngineRuntime.Rq G) / 40000
      ∧ ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t P
      ∧ (¬ ∃ (u : Fin (G.n * G.n) → ℝ) (r : ℝ), 0 < r ∧
          QMCLeafB.Boundary.eucBallF u r ⊆ relaxBallP G t P)
      ∧ BodyRec G t P :=
  ⟨QMCLeafB.DregM6.G₁, QMCLeafB.DregM6.tStar, QMCLeafB.DregM6.P₁,
   QMCLeafB.Face36M2.face_summary.1, QMCLeafB.Face36M2.face_summary.2.1,
   QMCLeafB.Face36M2.face_summary.2.2.1, QMCLeafB.Face36M2.face_no_ball,
   QMCLeafB.Face36M2.face_summary.2.2.2⟩

#print axioms QMCLeafB.Aud39M8.ballFree_stratum_inhabited


/-! ## 9.  What the refutation transfers to: the programme obligation is FORCED

The leaf's closing stroke (`Asm36M8.solution_of_two_slots_selfRec`) consumes `SelfRecG` and `hok`.
`SelfRecG` plus a ball-bearing bracketed body forces the bit `true` there, and `hok` then forces a
`RelaxMem` member.  So **every** programme that closes the leaf must carry a member certificate at
every bracketed ball-bearing body — the obligation is not optional, and it is what replaces the
refuted `SepStream` on that stratum.  (This is `Asm36M8.bit_true_of_fatG` without the separate
`FatG` horizon hypothesis: the campaign ball plus the `RunParams` budget `P.hbudget` suffice.) -/

/-- **`SelfRecG` reads the bit `true` at every ball-bearing bracketed body.** -/
theorem selfRecG_bit_true_at_ball
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.Asm36M8.SelfRecG o P)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    o G t = true := by
  by_contra hcon
  have hb : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball (P := P G) hn hball (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Aud39M8.selfRecG_bit_true_at_ball

/-- **THE FORCED PROGRAMME OBLIGATION.**  At every bracketed ball-bearing body, a leaf-closing
programme hands over a symmetric rational `RelaxMem` member at `(t − eps, dqShallow)`.  With
`not_sepStream_unconditional` this is the whole replacement for `SepStream` on that stratum. -/
theorem leaf_forces_member_at_ball
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.Asm36M8.SelfRecG o P)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) :=
  hok G t hn hlo hlt (selfRecG_bit_true_at_ball H hn hlo hlt hball)

#print axioms QMCLeafB.Aud39M8.leaf_forces_member_at_ball

end QMCLeafB.Aud39M8


