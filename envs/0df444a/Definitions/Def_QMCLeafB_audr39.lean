-- Prove2me | Definitions.Def_QMCLeafB_audr39
-- name    : QMCLeafB_audr39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:22:44.996196+00:00
-- url     : https://prove2.me/theorems/18b70572-8135-46bb-898e-2d9819a0aa75
-- title:
--   QMCLeafB audr39
-- statement:
--   # `Check_audr39_m6` — phase 39, member m6, direction d10 (`scope audit of the refutation`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_anchorfacts
import Definitions.Def_QMCLeafB_sound31
import Definitions.Def_QMCLeafB_aud36
import Definitions.Def_QMCLeafB_relaxapi
import Definitions.Def_QMCLeafB_rf38
/-
# `Check_audr39_m6` — phase 39, member m6, direction d10 (`scope audit of the refutation`)

**Task.** `Check_rf38_m1.SepStream` is the leaf's last object.  Phase 39 (m2, `Check_sw39_m2`)
refuted it at the campaign family.  This file does two things:

* **SECOND, INDEPENDENT DERIVATION** of the refutation, by a different route: instead of composing
  the *shallow-cut* obstruction (`Asm35M4.not_shallowCut_of_ball`), it goes through the *record*
  obstruction (`ThinRec34M4.not_bodyRec_of_ball`) via `bodyRec_of_shallowCut`.  The engine of both
  is `sepStream_to_bodyRec`: **`SepStream` manufactures the all-false record at EVERY body with
  `2 ≤ G.n`** — it mentions no bit and no bracket, so it is a statement about the body alone.
* **THE EXACT TRIGGER SET**, which is strictly larger than the one m2 used:
  `not_sepStream_of_ball` fires on any body carrying the campaign ball;
  `not_sepStream_of_strictBelow` fires on any body carrying a unit-diagonal PSD point strictly
  below the engine's level (`Sound31.ball_of_strict_below` supplies the ball there);
  `not_sepStream_of_ball_gen` is the sharpest: **any ball at all** of radius `r > 0` obeying the
  horizon criterion `volPot A₀ · 2^{-K} < r^{n·n}` kills `SepStream`.  No bracket, no bit, no
  `t`-restriction, no campaign radius: the refutation is a property of the relaxation's inradius.
* **NON-VACUITY COMPANION.**  `sepStream_of_emptyBodies`: at a programme all of whose bodies are
  empty `SepStream` holds with ANY nonzero stream.  So the refutation is exactly the nonempty part,
  and the object is not empty by accident of its own shape.
* `not_sepStream_paramsKbc2` is the concrete instance at the campaign family, at `(G₁,t₁)` via the
  banked sliver ball.

Discipline: `set_option autoImplicit false`; `#print axioms` after every theorem (exactly
`[propext, Classical.choice, Quot.sound]`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
Imports: `Mathlib`, the live `Solutions.Check_rf38_m1` olean (the same `SepStream` m2 refuted), and
published `Definitions.Def_QMCLeafB_*` bundles only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Audr39M6

open Matrix
open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec BodyEmpty falseBit)
open QMCLeafB.BallM2 (runBall)

/-! ## 1.  The engine: `SepStream` records at EVERY body

`SepStream` says nothing about the programme's bit and nothing about the leaf's bracket.  Feeding it
through `shallowCut_of_separating` (`del ≡ 0`) and `bodyRec_of_shallowCut` produces the all-false
record at every `(G,t)` with `2 ≤ G.n`.  This is what makes the hypothesis too strong: the record
obstructions are then free to fire anywhere. -/

theorem sepStream_to_bodyRec
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : QMCLeafB.Rf38M1.SepStream P c hc)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n) :
    BodyRec G t (P G) :=
  QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P G) hn (c G t) (hc G t)
      (hsep G t hn))

#print axioms sepStream_to_bodyRec

/-! ## 2.  Second derivation of the refutation (through the record, not the shallow cut) -/

/-- **No separating stream at a ball-bearing body.**  Route: `SepStream ⟹ BodyRec` at every body
(§1), and `not_bodyRec_of_ball` forbids a record at a body carrying the campaign ball.  Independent
of m2's `not_shallowCut_of_ball` composition. -/
theorem not_sepStream_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((((P G).dq : ℚ) : ℝ) / (8 * ((((P G).cAq : ℚ) : ℝ) + 1))) ⊆ runBall G t (P G)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (sepStream_to_bodyRec P c hc hsep hn)

#print axioms not_sepStream_of_ball

/-! ## 3.  A strictly wider trigger: a strict-below point

`Sound31.ball_of_strict_below`: a unit-diagonal PSD `Z` with `tr (W Z) < t - Rq/40000` carries the
campaign ball into the body.  So the ball is not needed as data — a strict-below point supplies it,
and `bit_true_of_strict_below` says such points already force the programme's bit `true`. -/

theorem not_sepStream_of_strictBelow
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  obtain ⟨Z, hZ, htr⟩ := hstrict
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn
    (QMCLeafB.Sound31.ball_of_strict_below (G := G) (t := t) (P G) hZ htr)
    (sepStream_to_bodyRec P c hc hsep hn)

#print axioms not_sepStream_of_strictBelow

/-! ## 4.  The sharpest trigger: ANY ball above the horizon threshold

`Aud36M6.no_runParts_of_ball_gen` needs no campaign radius: any ball of radius `r > 0` inside the
body with `volPot A₀ · 2^{-K} < r^{n·n}` forbids the all-false record.  So `SepStream` forces the
relaxation to be *horizon-thin* — of inradius below that explicit bound — at every body. -/

theorem not_sepStream_of_ball_gen
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
      ⊆ runBall G t (P G))
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * (P G).dq ^ 2)) * (1 / 2) ^ (P G).K
      < r ^ (G.n * G.n)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  obtain ⟨B⟩ := sepStream_to_bodyRec P c hc hsep hn
  have htrue := QMCLeafB.Aud36M6.no_runParts_of_ball_gen (P := P G) hn hr hball hR B
  have h' : (false : Bool) = true := htrue
  exact Bool.false_ne_true h'

#print axioms not_sepStream_of_ball_gen

/-- **The necessary condition `SepStream` imposes on the body**: at every `(G,t)` with `2 ≤ G.n`
the relaxation carries no ball of any radius above the horizon threshold. -/
theorem sepStream_imp_ball_free
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : QMCLeafB.Rf38M1.SepStream P c hc)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * (P G).dq ^ 2)) * (1 / 2) ^ (P G).K
      < r ^ (G.n * G.n)) :
    ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
        ⊆ runBall G t (P G)) :=
  fun hball => not_sepStream_of_ball_gen P c hc hn hr hball hR hsep

#print axioms sepStream_imp_ball_free

/-! ## 5.  The concrete instance at the campaign family -/

/-- **`SepStream` is EMPTY at `paramsKbc2`** — every stream fails, at `(G₁,t₁)` via the banked
sliver ball.  (`P₁` is `paramsKbc2 G₁` by `abbrev`, so the sliver ball is the required hypothesis
definitionally.) -/
theorem not_sepStream_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ QMCLeafB.Rf38M1.SepStream QMCLeafB.UnionShallow.paramsKbc2 c hc :=
  not_sepStream_of_ball _ c hc (G := QMCLeafB.AnchorFactsM2.G₁) (t := QMCLeafB.AnchorFactsM2.t₁)
    QMCLeafB.AnchorFactsM2.hn₁ (X₀ := QMCLeafB.BallM2.Xs)
    QMCLeafB.BallM2.sliver_ball_campaign

#print axioms not_sepStream_paramsKbc2

/-! ## 5b.  THE UNCONDITIONAL REFUTATION

`SepStream` quantifies over EVERY `t : ℚ`, and the relaxation grows with `t`.  At `t = Rq/40000 + 1`
the level is `t - Rq/40000 = 1`; the weight matrix is trace-free (`trace_wMatrix_one`), so the
identity is *strictly* below the level (`0 < 1`).  `Sound31.ball_of_strict_below` then puts the
campaign ball around `flat 1` inside the body, and §1+§2 kill the record there.  Hence the leaf's
last object is empty **for every programme and every stream** — no choice of `P`, `o` or `c` can
inhabit it.  This is strictly stronger than the campaign-anchored `not_sepStream_paramsKbc2`: the
sliver is not needed, only the `t`-quantifier is. -/

theorem sepStream_empty
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  refine not_sepStream_of_ball P c hc
    (G := QMCLeafB.AnchorFactsM2.G₁)
    (t := QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 + 1)
    QMCLeafB.AnchorFactsM2.hn₁
    (X₀ := (1 : Matrix (Fin QMCLeafB.AnchorFactsM2.G₁.n) (Fin QMCLeafB.AnchorFactsM2.G₁.n) ℝ)) ?_
  refine QMCLeafB.Sound31.ball_of_strict_below (G := QMCLeafB.AnchorFactsM2.G₁)
    (t := QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 + 1)
    (P QMCLeafB.AnchorFactsM2.G₁)
    (Z := 1) (QMCLeafB.RelaxApiM3.isUnitDiagPSD_one (n := QMCLeafB.AnchorFactsM2.G₁.n)) ?_
  rw [QMCLeafB.RelaxApiM3.trace_wMatrix_one]
  push_cast
  linarith

#print axioms sepStream_empty

/-- **The diagnosis**: the refuting threshold `t = Rq/40000 + 1` is strictly POSITIVE, hence lies
outside the leaf's own interior bracket `[-Rq, -Rq/40000)` — where `SelfRecG` actually reads the
hypothesis.  So the emptiness of `SepStream` is caused by its UNBOUNDED `t`-quantifier, not by the
bracket; a repair must keep the bracket (and, m2/ph39, gate on the bit). -/
theorem witness_not_in_bracket :
    ¬ (-(QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁)
          ≤ QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 + 1
        ∧ QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 + 1
            < -(QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000)) := by
  intro h
  linarith [h.2]

#print axioms witness_not_in_bracket

/-- **`solution_of_separating` never fires.**  Its last binder is uninhabited at every programme,
so the phase-38 reduction is a true conditional whose hypothesis is empty; the leaf can only be
reached through the bracket + bit-gated forms (`Check_sw39_m2`). -/
theorem solution_of_separating_never_fires
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc :=
  sepStream_empty P c hc

#print axioms solution_of_separating_never_fires

/-! ## 6.  Non-vacuity: the object is inhabited on the empty stratum

The refutation is a statement about the body, not about the shape of the hypothesis: at a programme
whose bodies are all empty, the inequality is vacuous and ANY nonzero rational stream separates. -/

theorem sepStream_of_emptyBodies
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → BodyEmpty G t (P G)) :
    QMCLeafB.Rf38M1.SepStream P c hc := by
  intro G t hn k hk z hz
  exact absurd hz.1 (hempty G t hn (QMCLeafB.Boundary.unflat z))

#print axioms sepStream_of_emptyBodies

end QMCLeafB.Audr39M6


