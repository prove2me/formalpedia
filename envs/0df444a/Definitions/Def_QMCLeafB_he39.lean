-- Prove2me | Definitions.Def_QMCLeafB_he39
-- name    : QMCLeafB_he39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:42:28.842677+00:00
-- url     : https://prove2.me/theorems/2f711f48-53de-40ba-8da3-330d0088e5ee
-- title:
--   QMCLeafB he39
-- statement:
--   # `Check_he39_m1` — phase 39, member m1, direction d1 (`hull-escape`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dc35
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_aud36
import Definitions.Def_QMCLeafB_face36
import Definitions.Def_QMCLeafB_rf38
import Definitions.Def_QMCLeafB_sw39
/-
# `Check_he39_m1` — phase 39, member m1, direction d1 (`hull-escape`)

**Question.** `Rf38M1.SepStream P c hc` asks: at every input `G` with `2 ≤ G.n`, every `t`, and every
round `k < (P G).K * (P G).m`, the engine's accumulated centre `Cat k` (built from the stream `c`
itself, at the ceiling depth `ρ = rmax`) lies on the far side of the WHOLE relaxation:

    c_k ⬝ Cat_k  ≤  c_k ⬝ z      for every `z` in `relaxBallP G t (P G)`.

That is hull escape with zero depth.  Question of this file: is there a normal-selection rule and a
depth rule keeping the centre outside the body at every round?

**Answer (machine-checked below): NO — not at any admissible programme, at any point whose
relaxation carries the campaign ball; and, on the positive side, YES exactly on the ball-free
rational-level face (§9).**  The obstruction is not analytic: it is `RunParams.hbudget`
itself.  `BallM2.no_runParts_of_ball` says a body carrying the ball of radius `dq/(8(cAq+1))` admits
no recorded run at all (`RunParts`), because the depth ledger `ρ ≤ rmax` keeps the body inside every
iterate's ellipsoid while `hhalve` halves that ellipsoid every `m` rounds and `hbudget` makes the
final ellipsoid smaller than the ball.  Since a separating stream at `del ≡ 0` *is* a record
(`Bypass35M6.shallowCut_of_separating` + `ThinRec34M4.bodyRec_of_shallowCut`), hull escape dies with
it.  At the campaign's own programme `paramsKbc2` the sliver point `(G₁, t₁)` carries exactly that
ball (`BallM2.sliver_ball_campaign`), so

    ¬ ∃ c hc, SepStream paramsKbc2 c hc.

**What this decides.**  `SepStream` is not the leaf's residual: at the campaign programme the
hypothesis of `Rf38M1.solution_of_separating` is unsatisfiable, so that stroke is vacuous.  The
programme change it forces is machine-checked in §6: the separation must be **keyed to the verdict
bit** (`SepStreamFalse`), and then the ball itself forces the bit `true` at every ball-bearing point
(`sepFalse_forces_bit_true`), i.e. the residue is exactly the campaign's known thin/ball-free
stratum, with the fat stratum served by the ok lane.

**Two further results.**  §5: `SepStream` is ALSO formally vacuous — the nonzero-normal hypothesis
`hc : ∀ G t k, c G t k ≠ 0` is unsatisfiable at an input with `n = 0` — and §8 shows the accepted
gated repair `Sw39M2.SepFalse` inherits that defect (machine-checked), while §6's repaired object is
inhabited with an explicit stream.  §9 supplies the POSITIVE half: at a body in a rational level set
the engine's own `NormalCut` trajectory at the sign-adaptive stream separates with `del ≡ 0`
(`shallowCut_of_faceLevel`), and at the campaign's face point `(G₁, tStar)` that body is NONEMPTY —
so the residual object is inhabited at a nonempty, ball-free body.

**Declarations:** 24, each followed by `#print axioms` (all exactly `[propext, Classical.choice,
Quot.sound]`), zero `sorryAx`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration (all exactly `[propext, Classical.choice, Quot.sound]`);
imports are published `Definitions.*` bundles plus two `Solutions.*` files that have no mirror bundle
yet: the phase-38 `Solutions.Check_rf38_m1` (which defines `SepStream`) and — for the audit of §8 —
the phase-39 `Solutions.Check_sw39_m2` (the accepted gated repair).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.He39M1

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates (Aat Cat cutCR sigmaQ)
open QMCLeafB.Rf38M1 (SepStream)
open QMCLeafB.ThinRec34M4 (ShallowCut BodyRec relaxBallP NormalCut falseBit)

/-! ## 1.  The bridge: `SepStream` at one point is a `ShallowCut` there

Nothing here is new mathematics — this is phase 35's `shallowCut_of_separating` fed by phase 38's
`SepStream` instead of by a pointwise separating hypothesis.  It is the step that turns "hull
escape" into "a record exists", which is where the parameter obstruction bites. -/

/-- **A separating stream at `(G,t)` is a shallow cut there** (phase 35, re-fed). -/
theorem shallowCut_of_sepStream
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) :
    ShallowCut G t (P G) hn :=
  QMCLeafB.Bypass35M6.shallowCut_of_separating hn (c G t) (hc G t)
    (fun k hk z hz => hsep G t hn k hk z hz)

#print axioms QMCLeafB.He39M1.shallowCut_of_sepStream

/-! ## 2.  THE OBSTRUCTION: a ball-bearing body admits no separating stream

The content is a three-line composition of banked theorems:

* `BallM2.no_runParts_of_ball`: at a body carrying the campaign ball of radius `dq/(8(cAq+1))`,
  every record reads the bit `true` — there is no all-false record.  Its two inputs are exactly
  `RunParams.hhalve` and `RunParams.hbudget` (fields of `RunParams`: the parameters cannot avoid it);
* `ThinRec34M4.bodyRec_of_shallowCut`: a `ShallowCut` at that point IS a record with the bit `false`;
* hence no stream separates at every round below the horizon.

Note the form: the hypothesis is a *ball inside the body*, so the statement is about the geometry of
the relaxation, not about the trajectory.  Any selection rule whatsoever (rational or not, adaptive
or fixed) is defeated, because the depth ledger `ρ_k ≤ rmax` is what the engine gives and it is what
keeps the body inside the contracting ellipsoid. -/

/-- **NO SEPARATING STREAM AT A BALL-BEARING BODY** (pointwise form).  For every nonzero normal
stream, some round below the horizon fails to separate the accumulated centre from the relaxation. -/
theorem not_separates_of_ball
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ relaxBallP G t P)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ¬ ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
        cutCR (NormalCut G P hn c hc) k
            ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k
          ≤ cutCR (NormalCut G P hn c hc) k ⬝ᵥ z := by
  intro hsep
  have hsc : ShallowCut G t P hn :=
    QMCLeafB.Bypass35M6.shallowCut_of_separating hn c hc hsep
  obtain ⟨B⟩ := QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn hsc
  have htrue : falseBit G t = true :=
    QMCLeafB.BallM2.no_runParts_of_ball hn
      (by simpa only [QMCLeafB.BallM2.runBall, QMCLeafB.ThinRec34M4.relaxBallP] using hball) B
  exact Bool.false_ne_true htrue

#print axioms QMCLeafB.He39M1.not_separates_of_ball

/-- **The same at family level**: a programme family with ONE ball-bearing body at `2 ≤ n` admits
no separating stream at all. -/
theorem not_sepStream_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G₀ : QuantumMaxCutEnergy.Input} {t₀ : ℚ} (hn : 2 ≤ G₀.n)
    {X₀ : Matrix (Fin G₀.n) (Fin G₀.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G₀).dq : ℝ) / (8 * (((P G₀).cAq : ℝ) + 1))) ⊆ relaxBallP G₀ t₀ (P G₀))
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepStream P c hc := by
  intro H
  exact not_separates_of_ball hn hball (c G₀ t₀) (hc G₀ t₀)
    (fun k hk z hz => H G₀ t₀ hn k hk z hz)

#print axioms QMCLeafB.He39M1.not_sepStream_of_ball

/-! ## 2b.  The radius-free form, and the NECESSARY THINNESS of any surviving body

`Aud36M6.no_runParts_of_ball_gen` is the same obstruction with the ball radius free: what matters is
`volPot A₀ · (1/2)^K < r^(n·n)` — the ellipsoid's final volume against the ball's.  Reading it in the
separating direction gives the sharpest statement of what a programme must look like for hull escape
to have any chance:

> if any stream separates at `(G,t)`, then EVERY ball inside the relaxation at `(G,t)` has
> `r^(n·n) ≤ volPot A₀ · (1/2)^K`.

At the campaign's `paramsKbc2`/`G₁` the parameters are `K = 89856`, `n·n = 4`,
`volPot A₀ = (π²/2)/8² ≈ 0.0771`, so the right-hand side is `≈ 2^{-22464}` in the fourth root: every
body of inradius above `≈ 10^{-6763}` is OUT of reach of `del ≡ 0` separation (the same order as
`Aud36M6`'s `10^{-6761}`).  So the programme change cannot be "pick a better selection rule": it must
restrict the object to the nano-collar of thin bodies (or key it to the bit, §6). -/

/-- **NO SEPARATION AT A BODY CARRYING A BALL ABOVE THE VOLUME THRESHOLD** (radius-free). -/
theorem not_separates_of_ball_gen
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ relaxBallP G t P)
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K < r ^ (G.n * G.n))
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ¬ ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
        cutCR (NormalCut G P hn c hc) k
            ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k
          ≤ cutCR (NormalCut G P hn c hc) k ⬝ᵥ z := by
  intro hsep
  have hsc : ShallowCut G t P hn :=
    QMCLeafB.Bypass35M6.shallowCut_of_separating hn c hc hsep
  obtain ⟨B⟩ := QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn hsc
  have htrue : falseBit G t = true :=
    QMCLeafB.Aud36M6.no_runParts_of_ball_gen hn hr
      (by simpa only [QMCLeafB.BallM2.runBall, QMCLeafB.ThinRec34M4.relaxBallP] using hball) hR B
  exact Bool.false_ne_true htrue

#print axioms QMCLeafB.He39M1.not_separates_of_ball_gen

/-- **THE NECESSARY THINNESS OF A SEPARATING BODY.**  If the accumulated centre is separated from the
relaxation at every round below the horizon, then no ball inside the relaxation can beat the volume
threshold: `r^(n·n) ≤ volPot A₀ · (1/2)^K`.  This is the exact shape of the programme change at body
level — separation survives only on bodies too thin for the ellipsoid to be squeezed below them. -/
theorem ball_volume_le_of_separating
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ relaxBallP G t P,
        cutCR (NormalCut G P hn c hc) k
            ⬝ᵥ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (NormalCut G P hn c hc) k
          ≤ cutCR (NormalCut G P hn c hc) k ⬝ᵥ z)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r ⊆ relaxBallP G t P) :
    r ^ (G.n * G.n) ≤ QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) * (1 / 2) ^ P.K := by
  by_contra hcon
  exact not_separates_of_ball_gen hn hr hball (lt_of_not_ge hcon) c hc hsep

#print axioms QMCLeafB.He39M1.ball_volume_le_of_separating

/-! ## 3.  The campaign programme is refuted (the sliver carries the ball)

`AnchorFactsM2.G₁` is the campaign's two-vertex input (`n = 2`, `Rq = 2`), `t₁ = -2 + 71/1520000`
the sliver threshold, `P₁ = paramsKbc2 G₁` the campaign's own parameter family.  `BallM2`'s
`sliver_ball_campaign` says the relaxation there carries the ball of the campaign's own radius
`dq/(8(cAq+1)) = 1/9120000` about the explicit point `Xs`.  Hull escape therefore fails on the
campaign's own programme; the sliver's body is nonempty (certificate below), so the failure is not
vacuous. -/

/-- The campaign programme, as a family (definitionally `UnionShallow.paramsKbc2`). -/
abbrev campaignP : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.UnionShallow.paramsKbc2

/-- **`SepStream` IS FALSE AT THE CAMPAIGN PROGRAMME.**  No rational normal stream whatsoever
separates the accumulated centres at every round below the horizon. -/
theorem campaign_not_sepStream :
    ¬ ∃ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
        (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0),
      SepStream campaignP c hc := by
  rintro ⟨c, hc, H⟩
  exact not_sepStream_of_ball campaignP QMCLeafB.AnchorFactsM2.hn₁
    (G₀ := QMCLeafB.AnchorFactsM2.G₁) (t₀ := QMCLeafB.AnchorFactsM2.t₁)
    (X₀ := QMCLeafB.BallM2.Xs) QMCLeafB.BallM2.sliver_ball_campaign c hc H

#print axioms QMCLeafB.He39M1.campaign_not_sepStream

/-- **The refutation is not vacuous**: the sliver's relaxation contains its own centre point, hence
is nonempty; hull escape is demanded at a point where there IS something to separate from. -/
theorem campaign_sliver_nonempty :
    (relaxBallP QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      (campaignP QMCLeafB.AnchorFactsM2.G₁)).Nonempty := by
  have hr : (0 : ℝ) ≤ ((QMCLeafB.AnchorFactsM2.P₁).dq : ℝ)
      / (8 * (((QMCLeafB.AnchorFactsM2.P₁).cAq : ℝ) + 1)) := by
    have h1 : (0 : ℝ) < ((QMCLeafB.AnchorFactsM2.P₁).dq : ℝ) := by
      exact_mod_cast (QMCLeafB.AnchorFactsM2.P₁).hdq
    have h2 : (0 : ℝ) ≤ ((QMCLeafB.AnchorFactsM2.P₁).cAq : ℝ) := by
      exact_mod_cast (QMCLeafB.AnchorFactsM2.P₁).hcAq
    positivity
  have hmem : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs)
      ((QMCLeafB.AnchorFactsM2.P₁.dq : ℝ)
        / (8 * ((QMCLeafB.AnchorFactsM2.P₁.cAq : ℝ) + 1)))
      (QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs) := by
    show (∑ i, (QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs i
        - QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs i) ^ 2)
      ≤ ((QMCLeafB.AnchorFactsM2.P₁.dq : ℝ)
          / (8 * ((QMCLeafB.AnchorFactsM2.P₁.cAq : ℝ) + 1))) ^ 2
    rw [show (∑ i, (QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs i
        - QMCLeafB.AnswerProducer.flat QMCLeafB.BallM2.Xs i) ^ 2) = 0 by simp]
    simpa using pow_nonneg hr 2
  exact ⟨_, QMCLeafB.BallM2.sliver_ball_campaign hmem⟩

#print axioms QMCLeafB.He39M1.campaign_sliver_nonempty

/-! ## 4.  The hull-escape reading, displayed

The negation of §2 in the language of the direction: at the sliver, for every admitted stream there
IS a round below the horizon and a body point at which the accumulated centre is not separated.  This
is the "exhibit a body + a round at which every admissible sequence fails" half of the direction,
stated for an arbitrary stream (the direction's `ρ_k` is pinned to `rmax` by `NormalCut`). -/

/-- **NO HULL ESCAPE AT THE SLIVER.** -/
theorem campaign_hull_escape_fails
    (c : ℕ → Fin (2 * 2) → ℚ) (hc : ∀ k, c k ≠ 0) :
    ¬ ∀ k, k < (campaignP QMCLeafB.AnchorFactsM2.G₁).K * (campaignP QMCLeafB.AnchorFactsM2.G₁).m →
        ∀ z ∈ relaxBallP QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
            (campaignP QMCLeafB.AnchorFactsM2.G₁),
          cutCR (NormalCut QMCLeafB.AnchorFactsM2.G₁ (campaignP QMCLeafB.AnchorFactsM2.G₁)
              QMCLeafB.AnchorFactsM2.hn₁ c hc) k
              ⬝ᵥ Cat (QMCLeafB.AnchorFactsM2.G₁.n * QMCLeafB.AnchorFactsM2.G₁.n)
                  (0 : Fin (QMCLeafB.AnchorFactsM2.G₁.n * QMCLeafB.AnchorFactsM2.G₁.n) → ℝ)
                  (NormalCut QMCLeafB.AnchorFactsM2.G₁ (campaignP QMCLeafB.AnchorFactsM2.G₁)
                    QMCLeafB.AnchorFactsM2.hn₁ c hc) k
            ≤ cutCR (NormalCut QMCLeafB.AnchorFactsM2.G₁ (campaignP QMCLeafB.AnchorFactsM2.G₁)
                QMCLeafB.AnchorFactsM2.hn₁ c hc) k ⬝ᵥ z :=
  not_separates_of_ball QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.BallM2.sliver_ball_campaign c hc

#print axioms QMCLeafB.He39M1.campaign_hull_escape_fails

/-! ## 5.  A SECOND, TRIVIAL refutation: the statement's own nonzero-normal hypothesis

Before the geometric obstruction of §2 there is a formal one.  `SepStream` demands
`hc : ∀ G t k, c G t k ≠ 0` at EVERY input `G : QuantumMaxCutEnergy.Input`, and an input may have
`n = 0` (`Input` is `⟨n, weights⟩`, and `Weights 0` is inhabited).  At `n = 0` the vector
`c G t k : Fin (0*0) → ℚ` is a function on an empty type, hence `0`: no nonzero vector exists, so
`SepStream` is FALSE for every `P, c, hc` — for a reason with no geometric content.

This is a defect of the STATEMENT, and the repair is forced by it: the nonvanishing hypothesis must
live where the separation is used, i.e. at `2 ≤ G.n` (equivalently, `hc` should be a hypothesis of
the round only).  §2 shows the defect is not the whole story: after that repair the object still
fails at the campaign's own programme, so the repair has to be accompanied by the change of §6. -/

/-- The empty input (`n = 0`): inhabited because `Weights 0` is a function on an empty type. -/
def zeroInput : QuantumMaxCutEnergy.Input :=
  ⟨0, fun e => e.1.1.elim0⟩

/-- **`SepStream` IS FORMALLY VACUOUS**: at `n = 0` no nonzero rational vector exists, so the
nonzero-normal hypothesis `hc` is unsatisfiable and `SepStream` is false for every programme and
every stream.  (The leaf's one-hypothesis form is therefore vacuous as stated, independently of
§2.) -/
theorem not_sepStream_trivial
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ SepStream P c hc := by
  intro H
  have hne : c zeroInput 0 0 ≠ 0 := hc zeroInput 0 0
  have hzero : c zeroInput 0 0 = 0 := by
    funext i
    exact i.elim0
  exact hne hzero

#print axioms QMCLeafB.He39M1.not_sepStream_trivial

/-! ## 6.  THE PROGRAMME CHANGE: key the separation to the verdict bit

Two changes, both forced:

* **(R) repair the statement** — the stream's nonvanishing is required only where it is used
  (`2 ≤ G.n`);
* **(K) key the separation to the bit** — a cut round is owed only where the run reads `false`.

`SepStreamFalse` below is (R) + (K).  §4 already shows the geometric obstruction cannot be avoided by
`ρ`/selection rules, and §3 that it bites at the campaign's sliver; the theorems here show what (R)+(K)
buys: it implies the leaf's own `SelfRecG`, the ball FORCES the bit `true` at ball-bearing bodies
(so the fat stratum is the ok lane's), and the object is INHABITED on the empty-false programmes —
so the residual is exactly the nonempty ball-free (thin) stratum, not everything. -/

/-- **Bit-keyed separation, with the nonvanishing hypothesis at `2 ≤ G.n`** (`SepStream` with (R) and
(K) applied). -/
def SepStreamFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n), o G t = false →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (fun k => hc G t k hn)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- `SepStream` implies the keyed form (with (R) applied): the unconditional demand is stronger. -/
theorem sepStreamFalse_of_sepStream
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (H : SepStream P c hc) :
    SepStreamFalse o P c (fun G t k _ => hc G t k) := by
  intro G t hn hbit k hk z hz
  exact H G t hn k hk z hz

#print axioms QMCLeafB.He39M1.sepStreamFalse_of_sepStream

/-- **The keyed stream gives the all-cut identity** (`Asm36M8.SelfRecG`) — phase 38's
`selfRecG_of_separating` with the bit hypothesis threaded in place of the unconditional demand. -/
theorem selfRecG_of_sepFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0)
    (hsep : SepStreamFalse o P c hc) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  exact QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P G) hn (c G t)
      (fun k => hc G t k hn)
      (fun k hk z hz => hsep G t hn hb k hk z hz))

#print axioms QMCLeafB.He39M1.selfRecG_of_sepFalse

/-- **THE LEAF FROM THE KEYED STREAM** — `FinishLine.SolutionStatement` from {`Automatic.Poly` bit} +
{`1 ≤ K·m`} + {top slice} + {upper slot} + {bit-keyed separation}: the corrected form of
`Rf38M1.solution_of_separating`. -/
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
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0)
    (hsep : SepStreamFalse o P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_sepFalse o P c hc hsep)

#print axioms QMCLeafB.He39M1.solution_of_sepFalse

/-- **The ball FORCES the bit `true` at a ball-bearing body, even under the keyed hypothesis.**  So
the programme change is real, not a relabelling: wherever the relaxation carries the campaign ball,
the cut lane is closed and the ok lane must serve. -/
theorem sepFalse_forces_bit_true
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0)
    (hsep : SepStreamFalse o P c hc)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ relaxBallP G t (P G)) :
    o G t = true := by
  by_contra hcon
  have hfalse : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hcon
  exact not_separates_of_ball hn hball (c G t) (fun k => hc G t k hn)
    (fun k hk z hz => hsep G t hn hfalse k hk z hz)

#print axioms QMCLeafB.He39M1.sepFalse_forces_bit_true

/-- **At the campaign programme the keyed hypothesis forces the campaign bit `true` at the sliver**
— the concrete form of the programme change: the sliver's obligation is not a cut, it is an ok
round (equivalently a `RelaxMem` member at the search's own level). -/
theorem campaign_bit_true_of_sepFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0)
    (hsep : SepStreamFalse o campaignP c hc) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
  sepFalse_forces_bit_true o campaignP c hc hsep QMCLeafB.AnchorFactsM2.hn₁
    (X₀ := QMCLeafB.BallM2.Xs)
    (by simpa only [QMCLeafB.BallM2.runBall, QMCLeafB.ThinRec34M4.relaxBallP]
      using QMCLeafB.BallM2.sliver_ball_campaign)

#print axioms QMCLeafB.He39M1.campaign_bit_true_of_sepFalse

/-- **NON-VACUITY of the keyed form.**  A programme whose `false` points are body-EMPTY points
satisfies the keyed hypothesis outright — with the constant stream `c ≡ 1`, which is nonzero at every
`2 ≤ G.n` — because the quantifier over the relaxation is then vacuous.  So (R)+(K) is inhabited,
and what it leaves is the nonempty ball-free stratum, not the whole interior. -/
theorem exists_sepFalse_of_emptyBody
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      QMCLeafB.ThinRec34M4.BodyEmpty G t (P G)) :
    ∃ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
      (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0),
      SepStreamFalse o P c hc := by
  refine ⟨fun _ _ _ _ => 1, ?_, ?_⟩
  · intro G t k hn h
    have h1 : (1 : ℚ) = 0 := congrFun h ⟨0, by
      have h2 : 0 < G.n := by omega
      exact Nat.mul_pos h2 h2⟩
    exact one_ne_zero h1
  · intro G t hn hbit k hk z hz
    exact absurd hz.1 (hempty G t hn hbit (QMCLeafB.Boundary.unflat z))

#print axioms QMCLeafB.He39M1.exists_sepFalse_of_emptyBody

/-- **THE LEAF FROM AN EMPTY-FALSE PROGRAMME.**  {`Automatic.Poly` bit} + {`1 ≤ K·m`} + {top slice} +
{upper slot} + {`false` only at empty bodies} concludes the verbatim `SolutionStatement`.  So the
whole residual is the nonempty ball-free stratum: nothing else is owed. -/
theorem solution_of_emptyFalse
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
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      QMCLeafB.ThinRec34M4.BodyEmpty G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement := by
  obtain ⟨c, hc, hsep⟩ := exists_sepFalse_of_emptyBody o P hempty
  exact solution_of_sepFalse o P ho hKm htop hok c hc hsep

#print axioms QMCLeafB.He39M1.solution_of_emptyFalse

/-- **THE RESIDUAL SHAPE, EXACTLY.**  Under a keyed stream, every interior bit-`false` point has
(i) an all-false record and (ii) NO campaign ball in its relaxation.  So the residual the programme
change leaves is exactly `{interior, bit false, nonempty, ball-free}` — the campaign's collar — and
nothing else. -/
theorem sepFalse_residual_exact
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ}
    {hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), 2 ≤ G.n → c G t k ≠ 0}
    (hsep : SepStreamFalse o P c hc)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hb : o G t = false) :
    BodyRec G t (P G) ∧
      ∀ X₀ : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
            (((P G).dq : ℝ) / (8 * (((P G).cAq : ℝ) + 1))) ⊆ relaxBallP G t (P G)) := by
  refine ⟨selfRecG_of_sepFalse o P c hc hsep G t hn hlo hlt hb, fun X₀ hball => ?_⟩
  have htrue := sepFalse_forces_bit_true o P c hc hsep hn (X₀ := X₀) hball
  rw [hb] at htrue
  exact Bool.false_ne_true htrue

#print axioms QMCLeafB.He39M1.sepFalse_residual_exact

/-! ## 7.  What is left, exactly

`SepStream` is refuted twice over at the campaign programme: formally, at any input with `n = 0`
(§5), and geometrically, at the campaign's own sliver (§2, §3) — the second survives the natural
statement repair.  The keyed form `SepStreamFalse` is the satisfiable replacement: it implies the
leaf's `SelfRecG` and hence the verbatim `SolutionStatement` (§6), its ball-bearing points are forced
to the ok lane (§6), and it is inhabited on the empty-false class (§6).  Off the ball it is exactly
the campaign's `BodyRec`/`SelfRec` residual, the object the campaign already knows how to state.

The direction's positive half — "prove the invariant for a concrete selection rule" — is answered
negatively at the same level: `not_separates_of_ball` quantifies over EVERY normal stream, so no
selection rule (adaptive, rational, eigenvector-based, sign-flipping) and no depth schedule with
`ρ_k ≤ rmax` can keep the centre outside a ball-bearing body.  The obstruction is the parameter
field `RunParams.hbudget` itself, so no choice of `(K, m, dq, rmax)` obeying `RunParams` escapes it. -/

/-! ## 8.  Audit: the repair must also fix the nonzero-normal hypothesis

§5's formal defect does not go away by gating the separation on the bit: any hypothesis class of the
form `∃ c hc, …` whose `hc` is `∀ G t k, c G t k ≠ 0` is EMPTY, because at the empty input
(`n = 0`) the space `Fin (0*0) → ℚ` is a singleton.  The phase-39 gated repair
`Sw39M2.SepFalse` (and its `SepFalseNE`) keeps that `hc` verbatim, so its hypothesis class is empty
too — machine-checked below.  The repair is to put the nonvanishing where the separation is used
(`2 ≤ G.n`), which is what this file's `SepStreamFalse` does (§6), and which is inhabited: see
`exists_sepFalse_of_emptyBody` for an explicit stream.

The stream-FREE forms are unaffected: `ShallowCut`-based slots (`Sw39M2.ShallowOnFalse`) carry no
`hc`, and they are inhabited in the empty-false regime (`shallowOnFalse_of_emptyBody`). -/

/-- **NO STREAM IS EVERYWHERE NONZERO** — the formal obstruction behind §5, in the form that hits
every gated repair keeping the original `hc`. -/
theorem no_everywhere_nonzero_stream
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ) :
    ¬ ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0 := by
  intro hc
  have hne : c zeroInput 0 0 ≠ 0 := hc zeroInput 0 0
  have hzero : c zeroInput 0 0 = 0 := by
    funext i
    exact i.elim0
  exact hne hzero

#print axioms QMCLeafB.He39M1.no_everywhere_nonzero_stream

/-- **The accepted gated repair's hypothesis class is EMPTY**: `Sw39M2.SepFalse` keeps the
unrepaired `hc`, so no stream inhabits it.  (The gating CONTENT is right — §6 proves the same
implication — the hypothesis just has to be restated to be inhabitable.) -/
theorem not_exists_sepFalse_sw39
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) :
    ¬ ∃ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
        (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0),
      QMCLeafB.Sw39M2.SepFalse o P c hc := by
  rintro ⟨c, hc, _⟩
  exact no_everywhere_nonzero_stream c hc

#print axioms QMCLeafB.He39M1.not_exists_sepFalse_sw39

/-- Same for the "nonempty" variant `Sw39M2.SepFalseNE`. -/
theorem not_exists_sepFalseNE_sw39
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) :
    ¬ ∃ (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
        (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0),
      QMCLeafB.Sw39M2.SepFalseNE o P c hc := by
  rintro ⟨c, hc, _⟩
  exact no_everywhere_nonzero_stream c hc

#print axioms QMCLeafB.He39M1.not_exists_sepFalseNE_sw39

/-- **The stream-free form is inhabited** at any programme whose `false` points are empty-body
points: this is the shape of `Sw39M2.ShallowOnFalse` minus the (inessential) bracket, and it is
satisfied with no stream, no `hc`, no choice. -/
theorem shallowOnFalse_of_emptyBody
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      QMCLeafB.ThinRec34M4.BodyEmpty G t (P G))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) (hb : o G t = false) :
    ShallowCut G t (P G) hn :=
  QMCLeafB.Rf38M1.shallowCut_of_emptyBody hn (hempty G t hn hb)

#print axioms QMCLeafB.He39M1.shallowOnFalse_of_emptyBody

/-! ## 9.  THE POSITIVE INSTANCE: the residual object is INHABITED at a nonempty ball-free body

Everything above is negative.  This section supplies the other half: at a body lying in a RATIONAL
LEVEL SET the engine's own `NormalCut` trajectory at the sign-adaptive stream `±v` separates the
accumulated centre from the relaxation at every round with zero margins, i.e. `ShallowCut` — the exact
object the leaf's residual (`SelfRecG` / bit-gated `ShallowCut`) consumes.  That upgrades phase-36's
`Face36M2.bodyRec_of_level` (a record, on the adaptive chain) to the canonical `NormalCut` shape.

At the campaign's exemplar `(G₁, tStar, P₁)` this gives `ShallowCut` where the body is NONEMPTY
(`face_ball_nonempty`, from `DregM6.body_witness`), so the residual class is not vacuous at a
nonempty body: at the measure-zero face it is discharged outright.
-/

/-- The adaptive normal stream of the level face, as a plain stream. -/
noncomputable def faceNorm (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) : ℕ → Fin (G.n * G.n) → ℚ :=
  fun k => (QMCLeafB.Face36M2.faceCd G P hn v hv b k).c

theorem faceNorm_ne_zero (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) :
    ∀ k, faceNorm G P hn v hv b k ≠ 0 :=
  fun k => QMCLeafB.Face36M2.pickN_ne_zero hv b (QMCLeafB.Face36M2.faceSt G P hn v hv b k).2

theorem key_face (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ) :
    ∀ k, Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P)
            (QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
              (faceNorm_ne_zero G P hn v hv b)) k
          = (QMCLeafB.Face36M2.faceSt G P hn v hv b k).1.1
        ∧ Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
              (faceNorm_ne_zero G P hn v hv b)) k
          = (QMCLeafB.Face36M2.faceSt G P hn v hv b k).2 := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ihA, ihC⟩ := ih
    have hp : (QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
          (faceNorm_ne_zero G P hn v hv b) k).p
        = (QMCLeafB.Face36M2.faceCd G P hn v hv b k).p := by
      have h1 : (QMCLeafB.Face36M2.faceSt G P hn v hv b k).1.1
          *ᵥ (QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
              (faceNorm_ne_zero G P hn v hv b) k).p
          = faceNorm G P hn v hv b k := by
        rw [← ihA]
        exact QMCLeafB.RunPartsDilate.runCut_wit G P hn (faceNorm G P hn v hv b)
          (faceNorm_ne_zero G P hn v hv b) k
      have hFA : Aat (G.n * G.n) (QMCLeafB.RunPartsDilate.A0P G P)
          (QMCLeafB.Face36M2.faceCd G P hn v hv b) k
          = (QMCLeafB.Face36M2.faceSt G P hn v hv b k).1.1 :=
        QMCLeafB.Face36M2.Aat_faceCd G P hn v hv b k
      have h2 : (QMCLeafB.Face36M2.faceSt G P hn v hv b k).1.1
          *ᵥ (QMCLeafB.Face36M2.faceCd G P hn v hv b k).p
          = (QMCLeafB.Face36M2.faceCd G P hn v hv b k).c := by
        rw [← hFA]
        exact QMCLeafB.Face36M2.face_hwit G P hn v hv b k
      have h3 : faceNorm G P hn v hv b k = (QMCLeafB.Face36M2.faceCd G P hn v hv b k).c := rfl
      rw [h3] at h1
      exact QMCLeafB.RunPartsDilate.mulVec_inj_of_posQ
        (QMCLeafB.EngineIterates.posQ_of_cast (QMCLeafB.Face36M2.faceSt G P hn v hv b k).1.2)
        (h1.trans (h2.symm))
    refine ⟨?_, ?_⟩
    · rw [QMCLeafB.EngineIterates.Aat_unfold]
      rw [ihA, hp]
      rfl
    · rw [QMCLeafB.EngineIterates.Cat_unfold]
      rw [ihC]
      change QMCLeafB.EngineIterates.stepCentre (G.n * G.n)
          (QMCLeafB.Face36M2.faceSt G P hn v hv b k).2
          (fun i => (((QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
            (faceNorm_ne_zero G P hn v hv b) k).c i : ℚ) : ℝ))
          (fun i => (((QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
            (faceNorm_ne_zero G P hn v hv b) k).p i : ℚ) : ℝ))
          (((QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
            (faceNorm_ne_zero G P hn v hv b) k).rho : ℚ) : ℝ)
        = (QMCLeafB.Face36M2.faceSt G P hn v hv b (k + 1)).2
      rw [hp]
      rfl


/-- **`ShallowCut` AT A RATIONAL LEVEL FACE.**  If the relaxation lies in a rational level set
`{z | v ⬝ z = b}` with `v ≠ 0`, the engine's own `NormalCut` trajectory at the SIGN-ADAPTIVE stream
`±v` separates the accumulated centre from the relaxation at every round, with zero margins.  (This is
`Face36M2.bodyRec_of_level` upgraded from a record to the record's canonical `ShallowCut` shape: the
adaptive chain `faceSt` is identified with `NormalCut`'s own `Aat`/`Cat`.) -/
theorem shallowCut_of_faceLevel
    (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) (t : ℚ)
    (v : Fin (G.n * G.n) → ℚ) (hv : v ≠ 0) (b : ℝ)
    (hface : ∀ z ∈ relaxBallP G t P, QMCLeafB.Face36M2.vR v ⬝ᵥ z = b) :
    ShallowCut G t P hn := by
  refine ⟨faceNorm G P hn v hv b, faceNorm_ne_zero G P hn v hv b, fun _ => 0,
    fun k _ => le_refl 0, ?_, ?_⟩
  · intro k
    have hσ : (0 : ℚ) ≤ sigmaQ (faceNorm G P hn v hv b k)
        ((NormalCut G P hn (faceNorm G P hn v hv b) (faceNorm_ne_zero G P hn v hv b) k).p) :=
      QMCLeafB.Bypass35M6.sigmaQ_normalCut_pos (t := t) hn _ _ k
    have h2 : (0 : ℚ) ≤ P.rmax ^ 2 * sigmaQ (faceNorm G P hn v hv b k)
        ((NormalCut G P hn (faceNorm G P hn v hv b) (faceNorm_ne_zero G P hn v hv b) k).p) :=
      mul_nonneg (sq_nonneg _) hσ
    simpa using h2
  · intro k hk z hz
    have hz' : z ∈ QMCLeafB.Face36M2.relaxBallP G t P := hz
    have hF := QMCLeafB.Face36M2.face_hcut G P hn v hv b t hface k z hz'
    have h1 : Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn (faceNorm G P hn v hv b)
            (faceNorm_ne_zero G P hn v hv b)) k
        = (QMCLeafB.Face36M2.faceSt G P hn v hv b k).2 := (key_face G P hn v hv b k).2
    have h2 : Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.Face36M2.faceCd G P hn v hv b) k
        = (QMCLeafB.Face36M2.faceSt G P hn v hv b k).2 :=
      QMCLeafB.Face36M2.Cat_faceCd G P hn v hv b k
    have hcatN : Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G P hn (faceNorm G P hn v hv b) (faceNorm_ne_zero G P hn v hv b)) k
        = Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.Face36M2.faceCd G P hn v hv b) k := h1.trans h2.symm
    have hcR : cutCR (NormalCut G P hn (faceNorm G P hn v hv b) (faceNorm_ne_zero G P hn v hv b)) k
        = cutCR (QMCLeafB.Face36M2.faceCd G P hn v hv b) k := rfl
    have hsub := dotProduct_sub (cutCR (QMCLeafB.Face36M2.faceCd G P hn v hv b) k) z
      (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) (QMCLeafB.Face36M2.faceCd G P hn v hv b) k)
    have h0 : ((((fun _ : ℕ => (0 : ℚ)) k : ℚ)) : ℝ) = 0 := by norm_num
    rw [hcatN, hcR, h0]
    linarith [hF, hsub]

#print axioms QMCLeafB.He39M1.shallowCut_of_faceLevel


/-- **THE POSITIVE INSTANCE: `ShallowCut` AT A NONEMPTY BALL-FREE BODY.**  At the campaign's face
point `(G₁, tStar)` the relaxation lies in the rational level `{X₀₀ = 1 + dq/4}`
(`Face36M2.face_level_G1`), so the adaptive stream gives `ShallowCut` on the engine's own canonical
trajectory — and the body there is NONEMPTY (`DregM6.body_witness` at `a = 0`).  This is a non-vacuous
instance of the leaf's residual object at a nonempty body. -/
theorem shallowCut_face_G1 :
    ShallowCut QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁
      (by norm_num [QMCLeafB.DregM6.G₁]) :=
  shallowCut_of_faceLevel QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.P₁
    (by norm_num [QMCLeafB.DregM6.G₁]) QMCLeafB.DregM6.tStar
    QMCLeafB.Face36M2.e00 QMCLeafB.Face36M2.e00_ne (1 + (1 / 380000 : ℝ) / 4)
    (fun z hz => QMCLeafB.Face36M2.face_level_G1 QMCLeafB.DregM6.P₁ QMCLeafB.DregM6.dq_eq z hz)

#print axioms QMCLeafB.He39M1.shallowCut_face_G1


/-- **The body at the campaign face is NONEMPTY** — `DregM6`'s band witness at `a = 0`, converted
from `relaxBodyLE` to the relaxation ball's coordinate form (the norm bound is the only extra
field). -/
theorem face_ball_nonempty :
    (relaxBallP QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁).Nonempty := by
  have hw := QMCLeafB.DregM6.body_witness (a := 0) le_rfl (by norm_num)
  refine ⟨QMCLeafB.AnswerProducer.flat (QMCLeafB.DregM6.Xd 0), ?_, ?_⟩
  · rw [QMCLeafB.Boundary.unflat_flat]
    convert hw using 2
    · have hu : ((QMCLeafB.DregM6.tStar : ℚ) : ℝ)
          - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.DregM6.G₁ / 40000 : ℚ)) : ℝ)
          = -(2 + 2 * (1 / 380000 : ℝ)) := by
        simpa using QMCLeafB.DregM6.thresh_eq 0
      rw [hu]
      ring
    · have hd : (((QMCLeafB.DregM6.P₁).dq : ℚ) : ℝ) = 1 / 380000 := by
        rw [QMCLeafB.DregM6.dq_eq]; norm_num
      exact hd
  · have hM : ((2 * (QMCLeafB.DregM6.G₁.n : ℚ) ^ 2
        + 2 * (QMCLeafB.DregM6.P₁).dq ^ 2 : ℚ) : ℝ)
        = 8 + 2 * (1 / 380000 : ℝ) ^ 2 := by
      rw [show QMCLeafB.DregM6.G₁.n = 2 from rfl, QMCLeafB.DregM6.dq_eq]
      norm_num
    rw [hM]
    have hval : (∑ i, QMCLeafB.AnswerProducer.flat (QMCLeafB.DregM6.Xd 0) i ^ 2)
        = 2 * (1 + (1 / 380000 : ℝ) / 4) ^ 2
          + 2 * (-(1 + 3 * (1 / 380000 : ℝ) / 4)) ^ 2 := by
      rw [QMCLeafB.Boundary.sum_sq_flat]
      simp only [QMCLeafB.BallFloor.frobNormSq, QMCLeafB.DregM6.Xd, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
        Matrix.empty_val']
      norm_num
    rw [hval]
    nlinarith [sq_nonneg (1 / 380000 : ℝ)]

#print axioms QMCLeafB.He39M1.face_ball_nonempty


end QMCLeafB.He39M1


