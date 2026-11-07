-- Prove2me | Definitions.Def_QMCLeafB_sw39
-- name    : QMCLeafB_sw39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:40:59.527339+00:00
-- url     : https://prove2.me/theorems/b2d7630c-5152-4c5b-abe6-2382989f331d
-- title:
--   QMCLeafB sw39
-- statement:
--   # `Check_sw39_m2` — phase 39, member m2, direction d2 (`separation-weak-form`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_anchorfacts
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_rf38
/-
# `Check_sw39_m2` — phase 39, member m2, direction d2 (`separation-weak-form`)

**Task.** Pin down exactly what `Check_rf38_m1.solution_of_separating` consumes, and replace its
last hypothesis `SepStream` by the weakest hypothesis that still closes the leaf.

**Verdict of this file (three machine-checked statements).**

* **(REFUTATION) `SepStream` is FALSE — not merely unproved — at every programme with a body that
  carries the campaign ball.**  `SepStream` quantifies over ALL `(G,t)` with `2 ≤ G.n` and demands a
  rational supporting normal at every round below the horizon.  A supporting stream at a ball-bearing
  body would give `ShallowCut` with `del ≡ 0` (`Bypass35M6.shallowCut_of_separating`), hence
  `BodyRec` (`ThinRec34M4.bodyRec_of_shallowCut`), hence a `RunParts` record — and the volume
  obstruction `ThinRec34M4.not_bodyRec_of_ball` says no record exists there.  So
  `∀ c hc, ¬ SepStream P c hc` (`not_sepStream_of_ball`), and at the campaign family
  `paramsKbc2` this fires at the banked sliver `(G₁,t₁)` (`not_sepStream_paramsKbc2`,
  `BallM2.sliver_ball_campaign`).  Hence **`solution_of_separating` cannot be applied at the
  campaign programme at all**: its last hypothesis is unsatisfiable there.
* **(THE PROGRAMME CHANGE) gate the separation on the programme's own bit** — and on the leaf's
  bracket, which is where `SelfRecG` reads it.  `SepFalse o P c hc` is `SepStream` restricted to
  `-Rq G ≤ t`, `t < -Rq G/40000`, `o G t = false`.  It implies `SepStream`'s consequences where they
  are used (`sepStream_to_sepFalse` is the other direction), it keeps the leaf closed
  (`solution_of_sepFalse`, verbatim `FinishLine.SolutionStatement`), and it is **satisfiable exactly
  where `SepStream` is not** (`sep_refuted_but_gated_lives`).  The gating is not cosmetic: a gated
  supporting stream FORCES the bit `true` at every ball-bearing body
  (`sepFalse_forces_bit_true_at_ball`) — the same conclusion the upper-slot lane reaches
  independently (`Asm36M8.bit_true_of_fatG`).  So the programme change is: **the bit must read
  `true` wherever the relaxation carries the campaign ball, and separation is owed only on the
  ball-free bit-`false` stratum.**
* **(THE WEAKEST FORM) the leaf's true analytic hypothesis is bit-gated `ShallowCut`, not
  separation.**  `ShallowOnFalse o P` — `ShallowCut G t (P G) hn` at every bit-`false` bracket point
  — implies `SelfRecG o P` (`selfRecG_of_shallowOnFalse`) and hence the leaf
  (`solution_of_shallowOnFalse`), and `SepFalse` is one of its sufficient forms
  (`shallowOnFalse_of_sepFalse`).  `del ≡ 0` (separation) is therefore an avoidable strengthening:
  what the leaf consumes is the shallow-cut inequality with the ledger `del² ≤ rmax²·σ`, nothing
  more.

Discipline: `set_option autoImplicit false`; `#print axioms` after every theorem (all exactly
`[propext, Classical.choice, Quot.sound]`); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
imports: `Mathlib`, the one `Solutions.Check_rf38_m1` olean (the live `SepStream`), and published
`Definitions.Def_QMCLeafB_*` bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Sw39M2

open Matrix
open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)
open QMCLeafB.Boundary (unflat)
open QMCLeafB.Rf38M1 (SepStream)

/-! ## 0.  The campaign's horizon is positive (so `SepStream` is not vacuous for want of a round) -/

theorem paramsKbc2_Km_pos (G : QuantumMaxCutEnergy.Input) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K_mul_m]
  exact lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul G)

#print axioms QMCLeafB.Sw39M2.paramsKbc2_Km_pos

/-! ## 1.  THE REFUTATION

A separating stream at a ball-bearing body produces a record; the volume obstruction forbids records
there.  So no separating stream exists at such a body — for ANY programme. -/

/-- **NO SEPARATING STREAM AT A BALL-BEARING BODY.**  `SepStream` at any programme with a body
carrying the campaign ball is FALSE.  Chain: `SepStream ⟹ ShallowCut` (`del ≡ 0`, phase 35)
`⟹ BodyRec` (phase 34) `⟹` contradiction with the volume obstruction (phase 24's
`BallM2.no_runParts_of_ball`, exposed at the record by `ThinRec34M4.not_bodyRec_of_ball`). -/
theorem not_sepStream_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ∀ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
      (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0),
      ¬ SepStream P c hc := by
  intro c hc hsep
  have hsc : ShallowCut G t (P G) hn :=
    QMCLeafB.Bypass35M6.shallowCut_of_separating (G := G) (t := t) (P := P G) hn
      (c G t) (hc G t) (hsep G t hn)
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn hsc)

#print axioms QMCLeafB.Sw39M2.not_sepStream_of_ball

/-- **THE CAMPAIGN PROGRAMME HAS NO SEPARATING STREAM.**  At `paramsKbc2` the banked sliver
`(G₁,t₁)` is a `2 ≤ n` bracket point whose relaxation carries the campaign's own ball
(`BallM2.sliver_ball_campaign`), so `SepStream` is unsatisfiable there.  Consequently
`Check_rf38_m1.solution_of_separating` cannot be applied at the campaign programme: its last
hypothesis is empty. -/
theorem not_sepStream_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepStream QMCLeafB.UnionShallow.paramsKbc2 c hc :=
  not_sepStream_of_ball (P := QMCLeafB.UnionShallow.paramsKbc2) QMCLeafB.AnchorFactsM2.hn₁
    (X₀ := QMCLeafB.BallM2.Xs) (t := QMCLeafB.AnchorFactsM2.t₁)
    QMCLeafB.BallM2.sliver_ball_campaign c hc

#print axioms QMCLeafB.Sw39M2.not_sepStream_paramsKbc2

/-- **THE GENERAL FORM**: a separating stream forbids ball-bearing bodies outright.  Stated as the
exact obstruction to `SepStream` — no `(G,t,X₀)` with `2 ≤ n` and the campaign ball in the
relaxation can coexist with a separating stream. -/
theorem sepStream_forbids_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0}
    (H : SepStream P c hc) :
    ¬ ∃ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (X₀ : Matrix (Fin G.n) (Fin G.n) ℝ),
        2 ≤ G.n ∧
          QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
            (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1)))
            ⊆ QMCLeafB.BallM2.runBall G t (P G) := by
  rintro ⟨G, t, X₀, hn, hball⟩
  exact not_sepStream_of_ball P hn hball c hc H

#print axioms QMCLeafB.Sw39M2.sepStream_forbids_ball

/-! ## 1b.  The trace ceiling is vacuous for the same reason

`Check_rf38_m1.solution_of_trace` replaces the supporting stream by the constant TRACE direction and
the budget `hTrc : tr (Cat k) ≤ n(1 - dq/4)` for all rounds below the horizon.  Phase 35's
`shallowCut_of_trace` turns that budget into `ShallowCut` with `del ≡ 0`, so the same volume
obstruction kills it at any ball-bearing body: **`hTrc` is FALSE at every programme with a
ball-bearing body**, hence `solution_of_trace` is vacuous at the campaign family too. -/

/-- **THE TRACE BUDGET IS FALSE AT A BALL-BEARING BODY.** -/
theorem not_traceCeiling_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t (P G))
    (hTrc : ∀ k, k < (P G).K * (P G).m →
      ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
        (NormalCut G (P G) hn (QMCLeafB.Bypass35M6.traceStream G.n)
          (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) k) i i
      ≤ (G.n : ℝ) * (1 - (((P G).dq : ℚ) : ℝ) / 4)) :
    False :=
  QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
      (QMCLeafB.Bypass35M6.shallowCut_of_trace (P := P G) hn hTrc))

#print axioms QMCLeafB.Sw39M2.not_traceCeiling_of_ball

/-- **THE TRACE BUDGET IN `solution_of_trace`'s OWN BINDER SHAPE IS UNSATISFIABLE AT `paramsKbc2`** —
the exact hypothesis of `Check_rf38_m1.solution_of_trace`, refuted at the banked sliver. -/
theorem not_traceCeiling_paramsKbc2 :
    ¬ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
        ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
            * (QMCLeafB.UnionShallow.paramsKbc2 G).m →
          ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
              (QMCLeafB.Bypass35M6.traceStream G.n)
              (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) k) i i
          ≤ (G.n : ℝ)
            * (1 - (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) / 4)) := by
  intro H
  exact not_traceCeiling_of_ball (P := QMCLeafB.UnionShallow.paramsKbc2)
    (t := QMCLeafB.AnchorFactsM2.t₁) (X₀ := QMCLeafB.BallM2.Xs)
    QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.BallM2.sliver_ball_campaign
    (H QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁)

#print axioms QMCLeafB.Sw39M2.not_traceCeiling_paramsKbc2

/-- **The bracket restriction does NOT save `SepStream`.**  Separation demanded only at the leaf's own
bracket points `-Rq G ≤ t < -Rq G/40000` (no bit clause) is still unsatisfiable at the campaign
family: the banked sliver `(G₁,t₁)` lies INSIDE the bracket (`EmptyBodyM5.t₁_mem_bracket`) and carries
the campaign ball.  So the defect of `SepStream` is the missing BIT gate, not a missing `t`-window. -/
def SepBrk
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

theorem not_sepBrk_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepBrk QMCLeafB.UnionShallow.paramsKbc2 c hc := by
  intro H
  have hsc : ShallowCut QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁)
      QMCLeafB.AnchorFactsM2.hn₁ :=
    QMCLeafB.Bypass35M6.shallowCut_of_separating (G := QMCLeafB.AnchorFactsM2.G₁)
      (t := QMCLeafB.AnchorFactsM2.t₁)
      (P := QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁)
      QMCLeafB.AnchorFactsM2.hn₁
      (c QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁)
      (hc QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁)
      (H QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
        QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2)
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.BallM2.sliver_ball_campaign
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut QMCLeafB.AnchorFactsM2.hn₁ hsc)

#print axioms QMCLeafB.Sw39M2.not_sepBrk_paramsKbc2

/-! ## 2.  THE PROGRAMME CHANGE: gate the separation on the bit and the bracket

`SepStream`'s quantifier over ALL interior `(G,t)` is exactly the defect: the campaign's programme is
supposed to read `true` at ball-bearing bodies (the visit/volume lane), and `SepStream` is
unsatisfiable there.  The leaf reads the record only at bit-`false` bracket points (`SelfRecG`), so
that is the correct domain. -/

/-- **Bit-gated separation**: `SepStream` restricted to the leaf's bracket and to bit-`false` points.
Nothing else changes: the same rational stream, the same inequality, the same rounds. -/
def SepFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- `SepStream` implies its gated form (the gated form is strictly weaker — §3). -/
theorem sepStream_to_sepFalse
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0}
    (H : SepStream P c hc) : SepFalse o P c hc :=
  fun G t hn _ _ _ => H G t hn

#print axioms QMCLeafB.Sw39M2.sepStream_to_sepFalse

/-! ## 3.  The gated form is satisfiable exactly where the ungated one is not -/

/-- At the constant-`true` bit the gated hypothesis is vacuous — hence satisfiable with ANY stream,
at the very programme where `SepStream` is refuted. -/
theorem sepFalse_trueBit
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    SepFalse (fun _ _ => true) P c hc :=
  fun _ _ _ _ _ hb => absurd hb (by simp)

#print axioms QMCLeafB.Sw39M2.sepFalse_trueBit

/-- **THE GATING IS NOT COSMETIC.**  At the campaign family the ungated hypothesis is EMPTY while the
gated one is satisfiable — so the programme change §2 is exactly the difference between a vacuous and
a live reduction. -/
theorem sep_refuted_but_gated_lives
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepStream QMCLeafB.UnionShallow.paramsKbc2 c hc
      ∧ SepFalse (fun _ _ => true) QMCLeafB.UnionShallow.paramsKbc2 c hc :=
  ⟨not_sepStream_paramsKbc2 c hc, sepFalse_trueBit _ c hc⟩

#print axioms QMCLeafB.Sw39M2.sep_refuted_but_gated_lives

/-- **A GATED SUPPORTING STREAM FORCES THE BIT TRUE AT EVERY BALL-BEARING BODY.**  This is the
programme obligation the gating creates, and it is exactly the conclusion the upper-slot lane reaches
by volume (`Asm36M8.bit_true_of_fatG`): the ball obstruction that kills the record kills the
separation too, so the bit must read `true` there. -/
theorem sepFalse_forces_bit_true_at_ball
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0}
    (H : SepFalse o P c hc)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    o G t = true := by
  by_contra hcon
  have hb : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  have hsc : ShallowCut G t (P G) hn :=
    QMCLeafB.Bypass35M6.shallowCut_of_separating (G := G) (t := t) (P := P G) hn
      (c G t) (hc G t) (H G t hn hlo hlt hb)
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn hsc)

#print axioms QMCLeafB.Sw39M2.sepFalse_forces_bit_true_at_ball

/-! ## 4.  THE WEAKEST FORM: bit-gated `ShallowCut`

Separation is `del ≡ 0`; the record's own ledger allows `del² ≤ rmax²·σ`.  The leaf consumes only
the shallow-cut inequality at bit-`false` bracket points, so that is the weakest hypothesis of this
shape, and `SepFalse` is one sufficient way to get it. -/

/-- **The leaf's true analytic hypothesis**: `ShallowCut` at every bit-`false` bracket point. -/
def ShallowOnFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false → ShallowCut G t (P G) hn

/-- Separation (gated) gives the shallow cut with `del ≡ 0`. -/
theorem shallowOnFalse_of_sepFalse
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0}
    (H : SepFalse o P c hc) : ShallowOnFalse o P :=
  fun G t hn hlo hlt hb =>
    QMCLeafB.Bypass35M6.shallowCut_of_separating (G := G) (t := t) (P := P G) hn
      (c G t) (hc G t) (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Sw39M2.shallowOnFalse_of_sepFalse

/-- Ungated separation gives the gated shallow cut (so `SepStream` is a sufficient, strictly
stronger — in fact unsatisfiable at the campaign — hypothesis). -/
theorem shallowOnFalse_of_sepStream
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0}
    (H : SepStream P c hc) : ShallowOnFalse o P :=
  shallowOnFalse_of_sepFalse (sepStream_to_sepFalse H)

#print axioms QMCLeafB.Sw39M2.shallowOnFalse_of_sepStream

/-- **`SelfRecG` FROM THE WEAKEST FORM** — the record family at an arbitrary bit and programme. -/
theorem selfRecG_of_shallowOnFalse
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ShallowOnFalse o P) : QMCLeafB.Asm36M8.SelfRecG o P :=
  fun G t hn hlo hlt hb =>
    QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Sw39M2.selfRecG_of_shallowOnFalse

/-- **THE LEAF FROM THE WEAKEST FORM.**  The verbatim `FinishLine.SolutionStatement` from
{`Automatic.Poly` bit} + {`1 ≤ K·m`} + {top slice} + {upper slot} + {bit-gated shallow cut} — the
same programme facts as `solution_of_separating`, with its unsatisfiable last hypothesis replaced by
one that is satisfiable. -/
theorem solution_of_shallowOnFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (H : ShallowOnFalse o P) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_shallowOnFalse H)

#print axioms QMCLeafB.Sw39M2.solution_of_shallowOnFalse

/-- **THE LEAF FROM THE GATED SEPARATING STREAM** — the repaired form of
`Check_rf38_m1.solution_of_separating`: same programme facts, and a separating stream that is owed
only on the ball-free bit-`false` stratum (where the record lives). -/
theorem solution_of_sepFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepFalse o P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_shallowOnFalse o P ho hKm htop hok (shallowOnFalse_of_sepFalse H)

#print axioms QMCLeafB.Sw39M2.solution_of_sepFalse

/-! ## 5.  One more weakening: the separation is not owed at all at EMPTY bodies

`Asm35M4.shallowCut_of_emptyBody` gives `ShallowCut` for free at every empty body (the constant
all-ones normal stream), so the separating stream's domain shrinks again: bit-`false`, bracketed,
NONEMPTY.  That is the exact class on which the collar lives. -/

/-- At an empty body the shallow cut is free — no separation, no stream, no choice. -/
theorem shallowCut_of_emptyPoint
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (hempty : QMCLeafB.ThinRec34M4.BodyEmpty G t P) :
    ShallowCut G t P hn :=
  Asm35M4.shallowCut_of_emptyBody hn hempty

#print axioms QMCLeafB.Sw39M2.shallowCut_of_emptyPoint

/-- **The separation, owed only on the NONEMPTY part of the bit-`false` bracket.**  This is the
weakest domain any separating stream can be asked for: every other case is either vacuous (bit
`true`), outside the leaf's quantifier (outside the bracket), or free (empty body). -/
def SepFalseNE
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false → ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P G) →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- The nonempty-domain separation implies the gated shallow cut (empty bodies supplied free). -/
theorem shallowOnFalse_of_sepFalseNE
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0}
    (H : SepFalseNE o P c hc) : ShallowOnFalse o P := by
  intro G t hn hlo hlt hb
  by_cases hempty : QMCLeafB.ThinRec34M4.BodyEmpty G t (P G)
  · exact shallowCut_of_emptyPoint hn hempty
  · exact QMCLeafB.Bypass35M6.shallowCut_of_separating (G := G) (t := t) (P := P G) hn
      (c G t) (hc G t) (H G t hn hlo hlt hb hempty)

#print axioms QMCLeafB.Sw39M2.shallowOnFalse_of_sepFalseNE

/-- **THE LEAF FROM THE WEAKEST SEPARATION.**  The verbatim sentence from the programme facts plus a
separating stream owed ONLY at bit-`false`, bracketed, nonempty bodies. -/
theorem solution_of_sepFalseNE
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepFalseNE o P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_shallowOnFalse o P ho hKm htop hok (shallowOnFalse_of_sepFalseNE H)

#print axioms QMCLeafB.Sw39M2.solution_of_sepFalseNE

/-- **THE GATING IS NOT A FREE PASS.**  A bit that reads `false` at a ball-bearing bracket point
cannot carry the gated hypothesis either: at the sliver, `SepFalse` at the constant-`false` bit is
contradictory.  So the programme change of §2 is a genuine OBLIGATION on the programme (bit `true` at
every ball-bearing body), not a weakening that removes it. -/
theorem not_sepFalse_falseBit_sliver
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t (P G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepFalse (fun _ _ => false) P c hc := by
  intro H
  exact absurd (sepFalse_forces_bit_true_at_ball H hn hlo hlt hball) (by simp)

#print axioms QMCLeafB.Sw39M2.not_sepFalse_falseBit_sliver

/-- **THE WEAKEST GATED FORM IS STILL CONTRADICTORY WITH A FALSE BIT AT A BALL-BEARING BODY.**  Even
after gating on the bit, the bracket and nonemptiness, a `false` bit at a ball-bearing body admits no
separating stream: the shallow cut at that one point would be a record, and the volume obstruction
forbids records there.  So the gating is an OBLIGATION, not an escape clause. -/
theorem not_sepFalseNE_falseBit_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t (P G))
    (hne : ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P G))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepFalseNE (fun _ _ => false) P c hc := by
  intro H
  have hsc : ShallowCut G t (P G) hn :=
    QMCLeafB.Bypass35M6.shallowCut_of_separating (G := G) (t := t) (P := P G) hn
      (c G t) (hc G t) (H G t hn hlo hlt rfl hne)
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn hsc)

#print axioms QMCLeafB.Sw39M2.not_sepFalseNE_falseBit_of_ball

/-- **THE RECEIPT AT THE CAMPAIGN'S OWN SLIVER.**  `(G₁,t₁)` is a bit-`false` (constant bit),
bracketed, NONEMPTY (`AnchorFactsM2.realBody_G₁`) point carrying the campaign ball
(`BallM2.sliver_ball_campaign`), and the weakest gated hypothesis is contradictory there.  So the
programme change is forced: no version of the separating hypothesis survives a `false` bit at a
ball-bearing body. -/
theorem not_sepFalseNE_falseBit_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepFalseNE (fun _ _ => false) QMCLeafB.UnionShallow.paramsKbc2 c hc := by
  refine not_sepFalseNE_falseBit_of_ball (P := QMCLeafB.UnionShallow.paramsKbc2)
    (G := QMCLeafB.AnchorFactsM2.G₁) (t := QMCLeafB.AnchorFactsM2.t₁)
    QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1
    QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2 (X₀ := QMCLeafB.BallM2.Xs)
    QMCLeafB.BallM2.sliver_ball_campaign ?_ c hc
  intro he
  obtain ⟨X, hX⟩ := QMCLeafB.AnchorFactsM2.realBody_G₁
  exact he X hX

#print axioms QMCLeafB.Sw39M2.not_sepFalseNE_falseBit_paramsKbc2

end QMCLeafB.Sw39M2


