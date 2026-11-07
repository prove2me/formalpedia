-- Prove2me | Definitions.Def_QMCLeafB_rf38
-- name    : QMCLeafB_rf38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:12:30.433531+00:00
-- url     : https://prove2.me/theorems/17213358-e1d1-4dd9-b121-d16380022843
-- title:
--   QMCLeafB rf38
-- statement:
--   # `Check_rf38_m1` — phase 38, member m1, direction d7 (`reuse-first search`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_asm36_m8
import Definitions.Def_QMCLeafB_asm35
/-
# `Check_rf38_m1` — phase 38, member m1, direction d7 (`reuse-first search`)

**Task.** Decide leaf B's one inequality

    sup_{z in body} c_k . (Cat_k - z)  <=  rmax * sqrt(sigma_k)      (every round k < K*m),

`rmax = rmaxOf (n*n) = 1/(4n^2)`, the body being the phase-34/35 relaxation `relaxBallP` and
`Cat_k` the engine's accumulated centre.

**Verdict of this file (everything below is REUSE of live, published bundles — no re-derivation).**

* **FALSE in the programme's hypothesis class, in the sharp sense.**  Phase 34/35 already
  machine-check that the obligation fails at every body carrying the campaign ball:
  `ThinRec34M4.not_bodyRec_of_ball` (no all-cut record at a ball-bearing body) and
  `Asm35M4.not_shallowCut_of_ball` (no `ShallowCut` stream: no normal, no depth).  Corollary here
  (`no_selfRecG_of_ball`): no all-cut identity `SelfRecG` — hence no leaf through this route — can
  exist at a ball-bearing bit-`false` point.  So `body_containment` plus the depth ledger do **not**
  imply `rmax`-bounded distance; a depth/thinness estimate cannot decide the leaf.
* **TRUE, and with `del ≡ 0`, from a separating (supporting) direction.**  Phase 35's
  `Bypass35M6.shallowCut_of_separating` turns a rational supporting stream at the accumulated
  centres into `ShallowCut` with zero depth — `rmax`, `sigma`, the ellipsoid all unused (only
  `sigmaQ_normalCut_pos` is consumed).  Reused here in the leaf's own interface:
  * `selfRecG_of_separating` — the all-cut identity `Asm36M8.SelfRecG` from a supporting stream;
  * `solution_of_separating` — the full `FinishLine.SolutionStatement` from
    {`Automatic.Poly` bit} + {`1 <= K*m`} + {top slice} + {upper slot} + {supporting stream};
  * `support_le_rmax_of_separating` — the obligation ITSELF, in the problem's exact shape.
* **The residual is therefore SEPARATION, not an estimate.**  The leaf's one hypothesis is the
  existence of a rational direction in which the accumulated centre sits on the body's far side
  (`c . Cat_k <= c . z` for every body point) — the `del ≡ 0` regime.  Phase 35's trace direction
  supplies it at round `0` (`round_zero_separation`, every `dq <= 4`), and its drift recursion
  (`trF_Cat_succ`) says the trace certificate is self-limiting: the surviving witness must be a
  genuine far-side direction, which is exactly the "land / supporting-cut" programme, not a
  bounded-distance inequality.

Discipline: `set_option autoImplicit false`; `#print axioms` after every theorem (all exactly
[propext, Classical.choice, Quot.sound]); imports are published `Definitions.*` only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Rf38M1

open Matrix
open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)
open QMCLeafB.Boundary (unflat)

/-! ## 1.  The supporting stream, as a hypothesis

`SepStream` is the leaf's whole analytic content in the `del ≡ 0` regime: at every round the round's
own rational normal puts the engine's accumulated centre on the far side of the WHOLE relaxation.
Phase 35 proved that this gives `ShallowCut` with zero depth, so no `rmax` enters. -/

/-- A nonzero rational stream which, at every round below the horizon, places the accumulated centre
on the far side of the relaxation: a supporting-hyperplane certificate. -/
def SepStream (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-! ## 2.  The all-cut identity from a supporting stream (reuse: phase 35) -/

/-- **`SelfRecG` FROM SEPARATION.**  The leaf's all-cut identity at an ARBITRARY programme, from a
supporting rational stream — no `rmax`, no `sigma` estimate, no ellipsoid.  This is phase 35's
`shallowCut_of_separating` (`del ≡ 0`) transported into phase 36's `SelfRecG` interface by
`bodyRec_of_shallowCut`. -/
theorem selfRecG_of_separating
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  exact QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P G) hn (c G t) (hc G t)
      (hsep G t hn))

#print axioms QMCLeafB.Rf38M1.selfRecG_of_separating

/-! ## 3.  The leaf, from the programme facts plus separation -/

/-- **THE LEAF FROM A SUPPORTING STREAM.**  `FinishLine.SolutionStatement` from {`Automatic.Poly`
bit} + {`1 <= K*m`} + {top slice} + {upper slot} + {separating rational stream}.  The last binder is
the leaf's whole analytic content; the first four are facts about which programme runs. -/
theorem solution_of_separating
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
    (hsep : SepStream P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_separating o P c hc hsep)

#print axioms QMCLeafB.Rf38M1.solution_of_separating

/-! ## 4.  The obligation itself, in the problem's exact shape

Under a supporting direction the round's support value is `<= 0`, and the ledger ceiling
`rmax * sqrt (sigma_k)` is nonnegative — so the inequality holds with all of its slack, and in
particular `sigma_k > 0` (`sigmaQ_normalCut_pos`) is the only numeric input. -/

/-- **THE INEQUALITY, DISPLAYED.**  At every round below the horizon and every body point, the
support value in the round's own normal is bounded by `rmax * sqrt (sigma_k)` — the phase-38
obligation, verbatim. -/
theorem support_le_rmax_of_separating
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (k : ℕ) (hk : k < (P G).K * (P G).m) (z : Fin (G.n * G.n) → ℝ)
    (hz : z ∈ relaxBallP G t (P G)) :
    (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
        Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G (P G) hn (c G t) (hc G t)) k
      - (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z
      ≤ ((((P G).rmax : ℚ) : ℝ))
        * Real.sqrt (((sigmaQ (c G t k)
            ((NormalCut G (P G) hn (c G t) (hc G t)) k).p : ℚ) : ℝ)) := by
  have hle : (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
        Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G (P G) hn (c G t) (hc G t)) k
      - (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z ≤ 0 := by
    have h := hsep G t hn k hk z hz
    linarith
  have hcast : (0 : ℝ) ≤ ((((P G).rmax : ℚ) : ℝ)) := by
    exact_mod_cast (P G).hrmax
  have hsig : (0 : ℝ) ≤ Real.sqrt (((sigmaQ (c G t k)
      ((NormalCut G (P G) hn (c G t) (hc G t)) k).p : ℚ) : ℝ)) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hcast hsig]

#print axioms QMCLeafB.Rf38M1.support_le_rmax_of_separating

/-! ## 4b.  The second positive certificate: the trace ceiling (reuse: phase 35)

Phase 35's other covering case: if the trace-driven trajectory keeps the accumulated trace below the
body's trace floor `n(1 - dq/4)` for the whole horizon, the constant trace direction separates the
centre from every body point at every round, and the obligation holds with `del ≡ 0` again.  This is
the branch that makes the residual a BUDGET statement (`trF_Cat_succ`), and it dies exactly when the
trace has overflowed — the mechanism the `land / supporting-cut` programme replaces. -/

/-- **`SelfRecG` FROM THE TRACE CEILING.** -/
theorem selfRecG_of_trace
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hTrc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      ∀ k, k < (P G).K * (P G).m →
        ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G (P G) hn (QMCLeafB.Bypass35M6.traceStream G.n)
            (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) k) i i
        ≤ (G.n : ℝ) * (1 - (((P G).dq : ℚ) : ℝ) / 4)) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  exact QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_trace (P := P G) hn (hTrc G t hn))

#print axioms QMCLeafB.Rf38M1.selfRecG_of_trace

/-- The leaf from the trace ceiling instead of a general supporting stream. -/
theorem solution_of_trace
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
    (hTrc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      ∀ k, k < (P G).K * (P G).m →
        ∑ i, unflat (Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (NormalCut G (P G) hn (QMCLeafB.Bypass35M6.traceStream G.n)
            (QMCLeafB.Bypass35M6.traceStream_ne_zero (by omega))) k) i i
        ≤ (G.n : ℝ) * (1 - (((P G).dq : ℚ) : ℝ) / 4)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec o P ho hKm htop hok
    (selfRecG_of_trace o P hTrc)

#print axioms QMCLeafB.Rf38M1.solution_of_trace

/-! ## 5.  The FALSE branch: separation is not removable

Phase 34/35 already machine-check that the obligation FAILS at every body carrying the campaign
ball.  Re-exported here at the leaf's own interface: at such a point there is no all-cut identity,
so no leaf can be built through this route without a separating direction. -/

/-- **NO ALL-CUT IDENTITY AT A BALL-BEARING BODY** (phase 34's `not_bodyRec_of_ball`, phase 35's
`not_shallowCut_of_ball`).  So the supporting-stream hypothesis of §3 cannot be dropped: `rmax`
bounded distance is not implied by `body_containment` plus the depth ledger. -/
theorem no_selfRecG_of_ball
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hb : o G t = false)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((((P G).dq : ℚ) : ℝ) / (8 * ((((P G).cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P G)) :
    ¬ QMCLeafB.Asm36M8.SelfRecG o P := by
  intro H
  exact QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball (H G t hn hlo hlt hb)

#print axioms QMCLeafB.Rf38M1.no_selfRecG_of_ball

/-- Re-export: at a ball-bearing body NO shallow-cut stream exists — no normal, no depth. -/
theorem shallowCut_fails_of_ball
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((((P.dq : ℚ) : ℝ)) / (8 * ((((P.cAq : ℚ) : ℝ)) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t P) :
    ¬ ShallowCut G t P hn :=
  Asm35M4.not_shallowCut_of_ball hn hball

#print axioms QMCLeafB.Rf38M1.shallowCut_fails_of_ball

/-! ## 6.  The TRUE branch's cheap cases (reuse, no new analysis)

Empty bodies: the obligation is free (`shallowCut_of_emptyBody`).  Round `0`: the trace direction
separates the accumulated centre from every relaxation with `dq <= 4` (`round_zero_separation`), so
the obligation holds at the first round unconditionally. -/

/-- `ShallowCut` at every EMPTY body — the obligation is vacuous there. -/
theorem shallowCut_of_emptyBody
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (hempty : QMCLeafB.ThinRec34M4.BodyEmpty G t P) :
    ShallowCut G t P hn :=
  Asm35M4.shallowCut_of_emptyBody hn hempty

#print axioms QMCLeafB.Rf38M1.shallowCut_of_emptyBody

/-- The trace direction separates the accumulated centre at round `0`, for every `dq <= 4`. -/
theorem round_zero_separation
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (hdq : P.dq ≤ 4) {z : Fin (G.n * G.n) → ℝ} (hz : z ∈ relaxBallP G t P) :
    (fun k => (((QMCLeafB.Bypass35M6.diagQ G.n k : ℚ) : ℝ))) ⬝ᵥ (0 : Fin (G.n * G.n) → ℝ)
      ≤ (fun k => (((QMCLeafB.Bypass35M6.diagQ G.n k : ℚ) : ℝ))) ⬝ᵥ z :=
  QMCLeafB.Bypass35M6.round_zero_separation hdq hz

#print axioms QMCLeafB.Rf38M1.round_zero_separation

end QMCLeafB.Rf38M1


