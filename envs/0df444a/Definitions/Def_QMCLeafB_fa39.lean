-- Prove2me | Definitions.Def_QMCLeafB_fa39
-- name    : QMCLeafB_fa39
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:29:11.274593+00:00
-- url     : https://prove2.me/theorems/3e2f00ae-0000-4b3b-8ad6-091fcbce83d6
-- title:
--   QMCLeafB fa39
-- statement:
--   # `Check_fa39_m4` — phase 39, member m4, direction d6 (`falsify39`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_anchorfacts
import Definitions.Def_QMCLeafB_asm36_m8
import Definitions.Def_QMCLeafB_aud36
import Definitions.Def_QMCLeafB_face36
import Definitions.Def_QMCLeafB_rf38
/-
# `Check_fa39_m4` — phase 39, member m4, direction d6 (`falsify39`)

**Task (attack role).** Phase 38 reduced the whole leaf to `Rf38M1.SepStream`:

    ∃ c, (hc : c ≠ 0 everywhere), ∀ (G) (t) (hn : 2 ≤ G.n), ∀ k < (P G).K * (P G).m,
      ∀ z ∈ relaxBallP G t (P G),  (c G t k) ⬝ Cat_k  ≤  (c G t k) ⬝ z.

**Verdict: `SepStream` is UNINHABITED at the campaign family** — for every normal stream `c`
(`not_sepStream_paramsKbc2`).  Independently derived and in agreement with d2/m2's
`Check_sw39_m2`; what this file adds is the *radius-free* trigger, the exact surviving scope, and
the rationalisation of the support normals.

**§1 — DIAGNOSIS: `SepStream` is a `∀` over ALL `(G,t)`, with no bit and no ball.**
At any single `(G,t)` its content is exactly `Bypass35M6.shallowCut_of_separating`'s hypothesis, hence
(`bodyRec_of_sep`) it produces the all-false record `ThinRec34M4.BodyRec` at that point.  So
`SepStream` asserts `BodyRec` at *every* interior point of the campaign family (`bodyRec_of_sepStream`).

**§2 — THE OBSTRUCTION.**  A record is impossible at any body carrying a ball of radius `r > 0` whose
volume beats the horizon: `Aud36M6.no_runParts_of_ball_gen` (campaign-radius form:
`BallM2.no_runParts_of_ball`).  So `¬ SepStream` for ANY programme/stream owning one ball-bearing
body with `volPot A₀ · 2^{-K} < r^{2N}` (`not_sepStream_of_ball_gen`, `not_sepStream_of_ball`).

**§3 — THE REFUTATION AT THE CAMPAIGN FAMILY (no hypotheses left).**
`not_sepStream_paramsKbc2 : ¬ SepStream paramsKbc2 c hc` for EVERY `c`, witnessed at `(G₁, t₁)` by
the banked `BallM2.sliver_ball_campaign` (the campaign's own `dq/24` ball sits inside
`runBall G₁ t₁ P₁`).  `refutation_point_dossier` records that `(G₁,t₁)` is a BRACKETED interior point
with a NONEMPTY body — the refutation is not an artefact of a far-away `t`.  `bit_true_at_ball` is
the reason this is a defect of SCOPE, not of the leaf: the same ball forces every record — hence the
programme's bit — to read TRUE there (`BallM2.sliver_bit_true`), so no record is owed at the point
where separation dies.  **`solution_of_separating` has no instance at `paramsKbc2`.**

**§4 — THE FORCED REPAIR (two scopes, machine-checked).**
* `BallFree` — no campaign-radius ball in the body; `BallFreeSep` — separation on that stratum;
  `selfRecG_of_ballfree_sep` / `solution_of_ballfree_sep`: (B) bit true off `BallFree` + (S')
  `BallFreeSep` ⟹ `SelfRecG` ⟹ the verbatim `SolutionStatement`.
* THE SHARP SCOPE (§4b): separation is dead at every NON-thin body, where `Thin` = "no ball of ANY
  radius beating the halving budget" (`not_sepStream_of_notThin`).  So the surviving hypothesis is
  `ThinSep`, and `selfRecG_of_thin_sep` closes the leaf from (bit true off `Thin`) + (`ThinSep`).
  `BallFree` is the coarser, campaign-radius version of the same scope; `Thin` is the exact one.
* NON-VACUITY (§4c): at the phase-36 face `(G₁,tStar)` the relaxation carries no ball at all, so it is
  horizon-thin (`thin_at_face`, `ballFree_at_face`) while the body is nonempty and the record exists
  (`Face36M2.bodyRec_face_G1`) — so the repaired scope is inhabited and the repair is not a sixth
  vacuity defect (`repaired_scope_inhabited`).

**§5 — THE SUPPORT CLAIMS SURVIVE (the refutation is about SCOPE, not the normals).**
* (a) A violated DIAGONAL slot supports the WHOLE relaxation with the rational normal `±e_ii`
  (`diag_support_whole`, `diag_support_whole_low`), and a violated objective bound with `−A`
  (`trace_support_whole`) — simultaneity of violations is irrelevant, because each constraint is
  valid at every body point.  Bridges to the leaf's own pairing: `frob_unflat_flat`, `flat_vv_dot`.
* (b) The PSD slot's normal CAN be taken rational: the violation is an open condition, so density of
  `ℚⁿ` upgrades a real witness (`exists_rat_violation`), giving the rational rank-one support
  `v vᵀ` (`psd_support_whole`).  This closes the one real→rational gap in `VerdictCut.psdCut`, which
  takes a rational witness as a hypothesis — relevant to d5/m7's selection rule.
* (c) `Cat_k`-rationality is never used: `SepStream` says `c : ... → ℚ` and constrains `hc`; nothing
  in `bodyRec_of_sep` inspects the centre.  Phase 37's `isSquare_sigma_of_rational_step` obstruction
  therefore does not reach this hypothesis.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every theorem, each exactly `[propext, Classical.choice, Quot.sound]`.
Imports: `Mathlib` + `Solutions.Check_rf38_m1` (no mirror bundle exists for it yet — if one is
published, co-load the mirror OR this file, never both) + six published `Definitions.*` bundles.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Fa39M4

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates

/-- The campaign ball radius `dq / (8·(c_A + 1))` of a parameter point, as a real number. -/
def campRadius {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G) : ℝ :=
  let d : ℝ := ((P.dq : ℚ) : ℝ)
  let c : ℝ := ((P.cAq : ℚ) : ℝ)
  d / (8 * (c + 1))


/-! ## 1.  The diagnostic: `SepStream` at one point IS the all-cut record there -/

/-- **`SepStream`'s single-point content produces the record.**  No bit, no ball, no bracket: the
separation inequality at `(G,t)` is exactly `shallowCut_of_separating`'s hypothesis, and a nonzero
normal stream therefore forces `BodyRec` there.  This is the step that turns the unscoped `∀ (G,t)`
in `SepStream` into an assertion about EVERY body of the family. -/
theorem bodyRec_of_sep {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsep : ∀ k, k < P.K * P.m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ≤ (fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ z) :
    QMCLeafB.ThinRec34M4.BodyRec G t P :=
  QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P) hn c hc
      (fun k hk z hz => hsep k hk z hz))

#print axioms QMCLeafB.Fa39M4.bodyRec_of_sep

/-- **The unscoped quantifier, displayed.**  `SepStream` at `P` implies the all-false record at EVERY
point `(G,t)` with `2 ≤ G.n` — the bracket, the bit and the body are all irrelevant to it. -/
theorem bodyRec_of_sepStream
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : QMCLeafB.Rf38M1.SepStream P c hc)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) :
    QMCLeafB.ThinRec34M4.BodyRec G t (P G) :=
  bodyRec_of_sep hn (c G t) (hc G t) (hsep G t hn)

#print axioms QMCLeafB.Fa39M4.bodyRec_of_sepStream

/-! ## 2.  The obstruction: a ball in the body kills every record -/

/-- **`¬ SepStream` from one ball-bearing body (radius-free, criterion explicit).**
If some body of the family carries a ball of radius `r > 0` with `volPot A₀ · 2^{-K} < r^{2N}`, then
NO nonzero rational normal stream separates the accumulated centres from the whole family: the ball
would have to stay inside every ceiling-chain ellipsoid while the ellipsoid volume halves `K` times.
(`Aud36M6.no_runParts_of_ball_gen` is the record-level form; here it reaches `SepStream`.) -/
theorem not_sepStream_of_ball_gen
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} {r : ℝ} (hr : 0 < r)
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
      ⊆ QMCLeafB.BallM2.runBall G t (P G))
    (hR : QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * ((P G).dq) ^ 2)) * (1 / 2) ^ ((P G).K)
      < r ^ (G.n * G.n)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  have htrue : (QMCLeafB.ThinRec34M4.falseBit G t) = true :=
    QMCLeafB.Aud36M6.no_runParts_of_ball_gen (P := P G) hn (o := QMCLeafB.ThinRec34M4.falseBit)
      hr hball hR
      (Classical.choice (bodyRec_of_sepStream P c hc hsep G t hn))
  exact Bool.false_ne_true htrue

#print axioms QMCLeafB.Fa39M4.not_sepStream_of_ball_gen

/-- **`¬ SepStream` from a ball at the campaign's own radius** — the same obstruction with the ball
size fixed by the programme's `dq`, `c_A` and the banked halving budget (`BallM2.no_runParts_of_ball`,
which already performs that arithmetic). -/
theorem not_sepStream_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((((P G).dq : ℚ) : ℝ) / (8 * ((((P G).cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball (P := P G) hn hball
    (bodyRec_of_sepStream P c hc hsep G t hn)

#print axioms QMCLeafB.Fa39M4.not_sepStream_of_ball

/-! ## 3.  THE REFUTATION AT THE CAMPAIGN FAMILY -/

/-- **`SepStream` IS UNINHABITED AT THE CAMPAIGN FAMILY.**  For EVERY normal stream `c` (rational,
nonzero at every round, adapted to `(G,t)` in any way) there is a pair `(G,t)` — `(G₁,t₁)`, the
campaign's own sliver — where the family's body carries the campaign ball, so the accumulated centre
cannot be on the body's far side at every round below the horizon.

Consequently `Rf38M1.solution_of_separating` has no instance at `paramsKbc2`: its fifth hypothesis is
false, not merely unproved. -/
theorem not_sepStream_paramsKbc2
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) :
    ¬ QMCLeafB.Rf38M1.SepStream QMCLeafB.UnionShallow.paramsKbc2 c hc :=
  not_sepStream_of_ball QMCLeafB.UnionShallow.paramsKbc2 c hc
    (G := QMCLeafB.AnchorFactsM2.G₁) (t := QMCLeafB.AnchorFactsM2.t₁)
    QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.BallM2.sliver_ball_campaign

#print axioms QMCLeafB.Fa39M4.not_sepStream_paramsKbc2

/-- **The refutation point is in the LEAF's own domain.**  `(G₁,t₁)` is a bracketed interior point
with a nonempty body — so the refutation is not an artefact of a quantifier running outside the
leaf's bracket: `SepStream` is false at a point where `SelfRecG` is asked for. -/
theorem refutation_point_dossier :
    -QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ ≤ QMCLeafB.AnchorFactsM2.t₁ ∧
    (QMCLeafB.AnchorFactsM2.t₁ : ℝ)
        < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ) ∧
    2 ≤ QMCLeafB.AnchorFactsM2.G₁.n ∧
    QMCLeafB.AnchorFactsM2.G₁.n = 2 ∧
    ∃ X : Matrix (Fin QMCLeafB.AnchorFactsM2.G₁.n) (Fin QMCLeafB.AnchorFactsM2.G₁.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁)
        (((QMCLeafB.AnchorFactsM2.t₁ : ℚ) : ℝ)
          - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.AnchorFactsM2.P₁.dq : ℚ) : ℝ)) X :=
  ⟨QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1, QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2,
    QMCLeafB.AnchorFactsM2.hn₁, QMCLeafB.AnchorFactsM2.n₁,
    QMCLeafB.AnchorFactsM2.realBody_G₁⟩

#print axioms QMCLeafB.Fa39M4.refutation_point_dossier

/-- **The bit is FORCED TRUE at a ball-bearing body** (re-export of `BallM2.no_runParts_of_ball` at
the leaf's interface).  This is why §3's refutation is a defect of `SepStream`'s SCOPE and not of the
leaf: the point that kills the hypothesis is a point where no record is owed. -/
theorem bit_true_at_ball
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) (campRadius P)
      ⊆ QMCLeafB.BallM2.runBall G t P)
    (B : QMCLeafB.FinalStroke.RunParts o G t P) : o G t = true :=
  QMCLeafB.BallM2.no_runParts_of_ball hn hball B

#print axioms QMCLeafB.Fa39M4.bit_true_at_ball

/-! ## 4.  THE FORCED REPAIR

The refutation above uses only the BALL and the fact that `SepStream` quantifies over every `(G,t)`.
It never uses the bit.  So the one change that repairs the hypothesis without weakening anything the
leaf actually consumes is a SCOPE change: separate only where a record is possible at all, i.e. where
the body carries no campaign ball, and make the bit TRUE on the rest.  Both halves are exactly what
phase 36/37 established about the campaign (`BallM2.sliver_bit_true`: a record at a ball-bearing body
forces the bit true; `Cov36M7.bit_true_of_ball`: the volume/visit half). -/

/-- **The repaired scope**: the point's body carries no ball of the campaign's own radius.  This is
the class on which §3 is silent, i.e. exactly where a record can exist. -/
def BallFree (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ¬ ∃ X₀ : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) (campRadius P)
        ⊆ QMCLeafB.BallM2.runBall G t P

/-- **The repaired stream hypothesis.**  `SepStream` with its quantifier restricted to the ball-free
stratum.  §3 shows the unrestricted version is false; this is the same content where it can be owed. -/
def BallFreeSep
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n), BallFree G t (P G) →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.ThinRec34M4.NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- **THE REPAIRED PAIR ⟹ THE ALL-CUT IDENTITY.**  (B) the bit is true at every ball-bearing body,
(S') separation on the ball-free stratum: together they give `SelfRecG` at ANY programme and bit.
The ball half is not a mathematical obligation at all — it is what a correct programme must satisfy
(`BallM2.no_runParts_of_ball` forbids the alternative). -/
theorem selfRecG_of_ballfree_sep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ BallFree G t (P G) →
      o G t = true)
    (hsep : BallFreeSep P c hc) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  by_cases hbf : BallFree G t (P G)
  · exact bodyRec_of_sep hn (c G t) (hc G t) (hsep G t hn hbf)
  · exact absurd (hbit G t hn hbf) (by rw [hb]; simp)

#print axioms QMCLeafB.Fa39M4.selfRecG_of_ballfree_sep

/-- **THE LEAF FROM THE REPAIRED PAIR** — `Rf38M1.solution_of_separating` with its (false) fifth
hypothesis replaced by (B)+(S').  This is the form the next phase must instantiate. -/
theorem solution_of_ballfree_sep
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
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ BallFree G t (P G) →
      o G t = true)
    (hsep : BallFreeSep P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_ballfree_sep o P c hc hbit hsep)

#print axioms QMCLeafB.Fa39M4.solution_of_ballfree_sep

/-- **THE TWO FORMS ARE RELATED, EXACTLY.**  `SepStream` is `BallFreeSep` without the ball
restriction — so §3's refutation is precisely the statement that the restriction is not removable. -/
theorem sepStream_imp_ballFreeSep
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : QMCLeafB.Rf38M1.SepStream P c hc) :
    BallFreeSep P c hc :=
  fun G t hn _ k hk z hz => hsep G t hn k hk z hz

#print axioms QMCLeafB.Fa39M4.sepStream_imp_ballFreeSep

/-- **THE MIRROR.**  `SepStream` = `BallFreeSep` plus its values at ball-bearing points — and the
ball-bearing values are FALSE (`not_sepStream_of_ball`).  So the unrestricted hypothesis is strictly
stronger than anything the leaf can use. -/
theorem not_unrestricted_of_ball
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((((P G).dq : ℚ) : ℝ) / (8 * ((((P G).cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc :=
  not_sepStream_of_ball P c hc hn hball

#print axioms QMCLeafB.Fa39M4.not_unrestricted_of_ball

/-- **The horizon-thin stratum**: the point's body carries no ball of ANY radius beating the
halving budget (no `r > 0` with `volPot A₀ · 2^{-K} < r^{2N}` inside it).  This is the sharp scope:
`not_sepStream_of_notThin` shows separation is impossible everywhere else. -/
def Thin (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (X₀ : Matrix (Fin G.n) (Fin G.n) ℝ) (r : ℝ), 0 < r →
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀) r
        ⊆ QMCLeafB.BallM2.runBall G t P →
    QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * ((P.dq)) ^ 2)) * (1 / 2) ^ (P.K)
      ≥ r ^ (G.n * G.n)

/-- **THE REFUTATION IN ITS SHARP FORM, POINTWISE.**  At any point whose body is NOT horizon-thin,
no nonzero rational stream separates — so `SepStream` would have to be false there anyway, and its
`∀ (G,t)` is what makes it false *simpliciter*. -/
theorem not_sepStream_of_notThin
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (h : ¬ Thin G t (P G)) :
    ¬ QMCLeafB.Rf38M1.SepStream P c hc := by
  intro hsep
  rw [Thin] at h
  push Not at h
  obtain ⟨X₀, r, hr, hball, hR⟩ := h
  exact not_sepStream_of_ball_gen P c hc hn hr hball hR hsep

#print axioms QMCLeafB.Fa39M4.not_sepStream_of_notThin

/-- **The sharp repaired hypothesis**: separation on the horizon-thin stratum only. -/
def ThinSep
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n), Thin G t (P G) →
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.ThinRec34M4.NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- **THE SHARP REPAIRED PAIR ⟹ THE LEAF.**  `ThinSep` plus the bit being true off the thin stratum.
`SepStream` is this with `Thin` DELETED, and §3/§4 shows the deletion is exactly what is false. -/
theorem selfRecG_of_thin_sep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ Thin G t (P G) →
      o G t = true)
    (hsep : ThinSep P c hc) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  by_cases ht : Thin G t (P G)
  · exact bodyRec_of_sep hn (c G t) (hc G t) (hsep G t hn ht)
  · exact absurd (hbit G t hn ht) (by rw [hb]; simp)

#print axioms QMCLeafB.Fa39M4.selfRecG_of_thin_sep

/-! ## 5.  The support claims SURVIVE — so the refutation is about SCOPE, not about the normals

The falsification questions this direction was chartered to answer:

* (a) does the normal of a violated DIAGONAL slot support the WHOLE relaxation, with the other slots
  violated simultaneously?  YES — and for the trivial reason that each constraint is valid on the
  whole relaxation, so a violation of one is a violation at every body point (`diag_support_whole`,
  `trace_support_whole`).  Simultaneity of violations is irrelevant.
* (b) can the PSD slot's support be taken with a RATIONAL normal?  YES — the violation condition is
  an OPEN condition on the witness vector, so density of `ℚⁿ` in `ℝⁿ` upgrades a real witness to a
  rational one (`exists_rat_violation`), and `v vᵀ` is then a rational normal
  (`psd_support_whole`).  This is the one place where a real→rational step is genuinely needed, and
  it costs nothing.
* (c) is `Cat_k`-rationality irrelevant?  YES: `SepStream` constrains the NORMALS to be rational
  (`c : ... → ℚ`) and never asks `Cat_k` to be rational; `hc` mentions only `c`.  Nothing in
  `bodyRec_of_sep` uses rationality of the centre, so phase 37's `isSquare_sigma_of_rational_step`
  obstruction does not apply to this hypothesis. -/

/-! ### 5.0  Flat coordinates -/

/-- Row-major flattening over `ℚ`, and its cast. -/
def flatQ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) : Fin (n * n) → ℚ :=
  fun k => N (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The rational-to-real matrix cast. -/
def castQ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((N i j : ℚ) : ℝ)

theorem flatQ_cast {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) :
    (fun m => ((flatQ N m : ℚ) : ℝ)) = QMCLeafB.AnswerProducer.flat (castQ N) := by
  funext k
  simp [flatQ, castQ, QMCLeafB.AnswerProducer.flat]

/-- **The pairing bridge**: the leaf's `⬝ᵥ` on flat vectors IS the relaxation's `frob` pairing. -/
theorem frob_unflat_flat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin (n * n) → ℝ) :
    QMCLeafB.BallFloor.frob A (QMCLeafB.Boundary.unflat z)
      = (QMCLeafB.AnswerProducer.flat A) ⬝ᵥ z := by
  have h1 : QMCLeafB.BallFloor.frob A (QMCLeafB.Boundary.unflat z)
      = ∑ p : Fin n × Fin n, A p.1 p.2 * z (finProdFinEquiv p) := by
    simp only [QMCLeafB.BallFloor.frob, QMCLeafB.Boundary.unflat]
    exact (Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
      A p.1 p.2 * z (finProdFinEquiv p))).symm
  have h2 : (QMCLeafB.AnswerProducer.flat A) ⬝ᵥ z
      = ∑ p : Fin n × Fin n, A p.1 p.2 * z (finProdFinEquiv p) := by
    rw [dotProduct, ← Equiv.sum_comp finProdFinEquiv
      (fun k => QMCLeafB.AnswerProducer.flat A k * z k)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [QMCLeafB.AnswerProducer.flat]
  rw [h1, h2]

#print axioms QMCLeafB.Fa39M4.frob_unflat_flat

/-- **A rank-one normal in flat coordinates is the quadratic form**: `flat (v vᵀ) ⬝ z = qfR (unflat z) v`.
No symmetry hypothesis on `z` is needed — the quadratic form only sees the symmetric part, and
`v vᵀ` pairs against the full matrix entrywise. -/
theorem flat_vv_dot {n : ℕ} (v : Fin n → ℝ) (z : Fin (n * n) → ℝ) :
    (QMCLeafB.AnswerProducer.flat (Matrix.vecMulVec v v)) ⬝ᵥ z
      = QMCLeafB.BallFloor.qfR (QMCLeafB.Boundary.unflat z) v := by
  rw [← frob_unflat_flat, QMCLeafB.BallFloor.qfR_eq_sum]
  simp only [QMCLeafB.BallFloor.frob, Matrix.vecMulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

#print axioms QMCLeafB.Fa39M4.flat_vv_dot

/-! ### 5a.  A violated DIAGONAL slot supports the WHOLE relaxation -/

/-- **THE DIAGONAL NORMAL SUPPORTS THE WHOLE RELAXATION.**  If the accumulated centre `a` sits above
the diagonal band `1 + dq/4` in coordinate `(i,i)`, then the rational unit normal `e_{ii}` places `a`
on the far side of every point of the relaxation — regardless of what else `a` violates (PSD, trace,
the norm bound).  The reason is structural: the diagonal constraint is valid at every body point, so
one violation separates from all of them at once. -/
theorem diag_support_whole {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {a : Fin (G.n * G.n) → ℝ} {i : Fin G.n}
    (hviol : 1 + (((P.dq : ℚ) : ℝ)) / 4 < QMCLeafB.Boundary.unflat a i i) :
    ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      (fun k => if k = finProdFinEquiv (i, i) then (-1 : ℝ) else 0) ⬝ᵥ a
        ≤ (fun k => if k = finProdFinEquiv (i, i) then (-1 : ℝ) else 0) ⬝ᵥ z := by
  intro z hz
  have hzii : QMCLeafB.Boundary.unflat z i i ≤ 1 + (((P.dq : ℚ) : ℝ)) / 4 := by
    have h := hz.1.2.1 i
    have h' := (abs_le.mp h).2
    linarith
  have ha : (fun k => if k = finProdFinEquiv (i, i) then (-1 : ℝ) else 0) ⬝ᵥ a
      = -QMCLeafB.Boundary.unflat a i i := by
    simp [dotProduct, QMCLeafB.Boundary.unflat]
  have hb : (fun k => if k = finProdFinEquiv (i, i) then (-1 : ℝ) else 0) ⬝ᵥ z
      = -QMCLeafB.Boundary.unflat z i i := by
    simp [dotProduct, QMCLeafB.Boundary.unflat]
  rw [ha, hb]
  linarith

#print axioms QMCLeafB.Fa39M4.diag_support_whole

/-- The same for the LOWER edge of the diagonal band (the normal `−e_{ii}`). -/
theorem diag_support_whole_low {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {a : Fin (G.n * G.n) → ℝ} {i : Fin G.n}
    (hviol : QMCLeafB.Boundary.unflat a i i < 1 - (((P.dq : ℚ) : ℝ)) / 4) :
    ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      (fun k => if k = finProdFinEquiv (i, i) then (1 : ℝ) else 0) ⬝ᵥ a
        ≤ (fun k => if k = finProdFinEquiv (i, i) then (1 : ℝ) else 0) ⬝ᵥ z := by
  intro z hz
  have hzii : 1 - (((P.dq : ℚ) : ℝ)) / 4 ≤ QMCLeafB.Boundary.unflat z i i := by
    have h := hz.1.2.1 i
    have h' := (abs_le.mp h).1
    linarith
  have ha : (fun k => if k = finProdFinEquiv (i, i) then (1 : ℝ) else 0) ⬝ᵥ a
      = QMCLeafB.Boundary.unflat a i i := by
    simp [dotProduct, QMCLeafB.Boundary.unflat]
  have hb : (fun k => if k = finProdFinEquiv (i, i) then (1 : ℝ) else 0) ⬝ᵥ z
      = QMCLeafB.Boundary.unflat z i i := by
    simp [dotProduct, QMCLeafB.Boundary.unflat]
  rw [ha, hb]
  linarith

#print axioms QMCLeafB.Fa39M4.diag_support_whole_low

/-! ### 5b.  The PSD slot's normal can be taken RATIONAL -/

/-- **RATIONALISATION.**  If the quadratic form of `X` dips below `-(c/2)·‖·‖²` at some REAL vector,
it does so at a RATIONAL one.  The set `{v | qfR X v + (c/2)·‖v‖² < 0}` is open and nonempty, and
`ℚⁿ` is dense in `ℝⁿ`.  This is the only real→rational step the support argument needs. -/
theorem exists_rat_violation {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : ¬ ∀ x : Fin n → ℝ,
      -(c / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR X x) :
    ∃ v : Fin n → ℚ,
      QMCLeafB.BallFloor.qfR X (fun i => ((v i : ℚ) : ℝ))
        < -(c / 2) * (∑ i, (((v i : ℚ) : ℝ)) ^ 2) := by
  classical
  rw [not_forall] at h
  obtain ⟨x₀, hx₀⟩ := h
  rw [not_le] at hx₀
  set F : (Fin n → ℝ) → ℝ := fun x => QMCLeafB.BallFloor.qfR X x + (c / 2) * (∑ i, x i ^ 2) with hF
  have hF0 : F x₀ < 0 := by simp only [hF]; linarith
  have hcont : Continuous F := by
    simp only [hF, QMCLeafB.BallFloor.qfR, dotProduct, Matrix.mulVec]
    fun_prop
  have hopen : IsOpen {x : Fin n → ℝ | F x < 0} := isOpen_lt hcont continuous_const
  obtain ⟨v, hv⟩ := (DenseRange.piMap (f := fun (_ : Fin n) => ((↑) : ℚ → ℝ))
      (fun _ => Rat.denseRange_cast)).exists_mem_open hopen ⟨x₀, hF0⟩
  have hv' : QMCLeafB.BallFloor.qfR X (fun i => ((v i : ℚ) : ℝ))
      + (c / 2) * (∑ i, (((v i : ℚ) : ℝ)) ^ 2) < 0 := by
    have h1 := hv
    simp only [Set.mem_ofPred_eq, hF] at h1
    exact h1
  exact ⟨v, by linarith⟩

#print axioms QMCLeafB.Fa39M4.exists_rat_violation

/-- **THE PSD NORMAL, RATIONALLY.**  If the accumulated centre `a` is not relaxed-PSD, some
rational rank-one normal `v vᵀ` supports the WHOLE relaxation at `a` — `v` comes from
`exists_rat_violation`, so no real witness is left in the statement. -/
theorem psd_support_whole {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {a : Fin (G.n * G.n) → ℝ}
    (hviol : ¬ ∀ x : Fin G.n → ℝ,
      -((((P.dq : ℚ) : ℝ)) / 2) * (∑ i, x i ^ 2)
        ≤ QMCLeafB.BallFloor.qfR (QMCLeafB.Boundary.unflat a) x) :
    ∃ v : Fin G.n → ℚ, v ≠ 0 ∧
      ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
        (fun k => ((flatQ (Matrix.vecMulVec v v) k : ℚ) : ℝ)) ⬝ᵥ a
          ≤ (fun k => ((flatQ (Matrix.vecMulVec v v) k : ℚ) : ℝ)) ⬝ᵥ z := by
  classical
  obtain ⟨v, hv⟩ := exists_rat_violation (c := (((P.dq : ℚ) : ℝ))) hviol
  have hvne : v ≠ 0 := by
    intro h0
    subst h0
    simp [QMCLeafB.BallFloor.qfR] at hv
  have hcast : castQ (Matrix.vecMulVec v v)
      = Matrix.vecMulVec (fun i => ((v i : ℚ) : ℝ)) (fun i => ((v i : ℚ) : ℝ)) := by
    ext i j
    simp [castQ, Matrix.vecMulVec]
  have hres : ∀ y : Fin (G.n * G.n) → ℝ,
      (fun k => ((flatQ (Matrix.vecMulVec v v) k : ℚ) : ℝ)) ⬝ᵥ y
        = QMCLeafB.BallFloor.qfR (QMCLeafB.Boundary.unflat y) (fun i => ((v i : ℚ) : ℝ)) := by
    intro y
    rw [flatQ_cast, hcast, flat_vv_dot]
  refine ⟨v, hvne, ?_⟩
  intro z hz
  have hbody : -((((P.dq : ℚ) : ℝ)) / 2) * (∑ i, (((v i : ℚ) : ℝ)) ^ 2)
      ≤ QMCLeafB.BallFloor.qfR (QMCLeafB.Boundary.unflat z) (fun i => ((v i : ℚ) : ℝ)) :=
    hz.1.1 (fun i => ((v i : ℚ) : ℝ))
  rw [hres, hres]
  linarith

#print axioms QMCLeafB.Fa39M4.psd_support_whole

/-- **THE TRACE NORMAL.**  A violated objective bound gives the rational normal `−A` (given any
rational presentation `Aq` of the objective matrix).  Again the other slots play no role. -/
theorem trace_support_whole {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {a : Fin (G.n * G.n) → ℝ}
    {Aq : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hA : ∀ i j, ((Aq i j : ℚ) : ℝ) = QMCLeafB.wMatrix G i j)
    (hviol : ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        + (((P.dq : ℚ) : ℝ)) / 2
      < QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G) (QMCLeafB.Boundary.unflat a)) :
    ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      (fun k => ((-(flatQ Aq k) : ℚ) : ℝ)) ⬝ᵥ a
        ≤ (fun k => ((-(flatQ Aq k) : ℚ) : ℝ)) ⬝ᵥ z := by
  have hcastA : castQ Aq = QMCLeafB.wMatrix G := by
    ext i j
    simpa [castQ] using hA i j
  have hflat : ∀ y : Fin (G.n * G.n) → ℝ,
      (fun k => ((-(flatQ Aq k) : ℚ) : ℝ)) ⬝ᵥ y
        = -QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G) (QMCLeafB.Boundary.unflat y) := by
    intro y
    have h1 : (fun k => ((-(flatQ Aq k) : ℚ) : ℝ))
        = -(fun k => ((flatQ Aq k : ℚ) : ℝ)) := by
      funext k
      simp
    rw [h1]
    have h2 : (-(fun k => ((flatQ Aq k : ℚ) : ℝ))) ⬝ᵥ y
        = -((fun k => ((flatQ Aq k : ℚ) : ℝ)) ⬝ᵥ y) := by
      simp [dotProduct, Finset.sum_neg_distrib, neg_mul]
    rw [h2, flatQ_cast, ← frob_unflat_flat, hcastA]
  intro z hz
  have hbody : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G) (QMCLeafB.Boundary.unflat z)
      ≤ ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        + (((P.dq : ℚ) : ℝ)) / 2 := hz.1.2.2
  rw [hflat, hflat]
  linarith

#print axioms QMCLeafB.Fa39M4.trace_support_whole

/-! ### 4c.  The repaired scope is INHABITED — the restriction is not vacuous

A scope restriction is only a legitimate repair if its domain is nonempty (five vacuity defects are
already on this campaign's record).  At the phase-36 face `(G₁, tStar)` the relaxation carries NO ball
at all, so it is horizon-thin, and the record exists there unconditionally (`bodyRec_of_level`). -/

/-- **The face is horizon-thin.**  No ball fits in the face's relaxation (`Face36M2.face_no_ball`). -/
theorem thin_at_face :
    Thin QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ := by
  intro X₀ r hr hball
  refine absurd ?_ QMCLeafB.Face36M2.face_no_ball
  refine ⟨QMCLeafB.AnswerProducer.flat X₀, r, hr, ?_⟩
  intro y hy
  exact hball hy

#print axioms QMCLeafB.Fa39M4.thin_at_face

/-- **The face is ball-free** in the campaign-radius sense too. -/
theorem ballFree_at_face :
    BallFree QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ := by
  intro ⟨X₀, hball⟩
  refine QMCLeafB.Face36M2.face_no_ball
    ⟨QMCLeafB.AnswerProducer.flat X₀, campRadius QMCLeafB.DregM6.P₁, ?_, ?_⟩
  · have h1 : (0 : ℝ) < ((QMCLeafB.DregM6.P₁.dq : ℚ) : ℝ) := by
      have := QMCLeafB.DregM6.P₁.hdq
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ ((QMCLeafB.DregM6.P₁.cAq : ℚ) : ℝ) := by
      have := QMCLeafB.DregM6.P₁.hcAq
      exact_mod_cast this
    simp only [campRadius]
    positivity
  · intro y hy
    exact hball hy

#print axioms QMCLeafB.Fa39M4.ballFree_at_face

/-- **THE REPAIRED SCOPE IS INHABITED, WITH ITS RECORD.**  At the face the body is nonempty,
horizon-thin (hence ball-free) and the all-false record exists — so `ThinSep`'s domain is nonempty
and §4b's repair is not the sixth vacuity defect. -/
theorem repaired_scope_inhabited :
    Thin QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ ∧
    QMCLeafB.ThinRec34M4.BodyRec QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar QMCLeafB.DregM6.P₁ ∧
    ¬ QMCLeafB.ThinRec34M4.BodyEmpty QMCLeafB.DregM6.G₁ QMCLeafB.DregM6.tStar
        QMCLeafB.DregM6.P₁ :=
  ⟨thin_at_face, QMCLeafB.Face36M2.bodyRec_face_G1,
    QMCLeafB.Face36M2.face_summary.2.2.1⟩

#print axioms QMCLeafB.Fa39M4.repaired_scope_inhabited

end QMCLeafB.Fa39M4


