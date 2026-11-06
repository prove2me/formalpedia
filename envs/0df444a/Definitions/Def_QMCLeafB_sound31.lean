-- Prove2me | Definitions.Def_QMCLeafB_sound31
-- name    : QMCLeafB_sound31
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:10:36.51263+00:00
-- url     : https://prove2.me/theorems/e0377411-f471-422c-8325-7d3ccd18b0a5
-- title:
--   QMCLeafB sound31
-- statement:
--   # The soundness of a run record — `SoundAt` from `RunParts`, with no emptiness hypothesis
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_boundary_m2
import Definitions.Def_QMCLeafB_answer_producer
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_brick_finish_line
/-
# The soundness of a run record — `SoundAt` from `RunParts`, with no emptiness hypothesis

The leaf's verdict predicate `SoundAt o G t` has two clauses: `true ⇒ ∃` unit-diag PSD `X` with
`tr(AX) ≤ t + ε` (the primal witness), and `false ⇒ ∀` unit-diag PSD `Z`, `t - ε ≤ tr(AZ)` (the dual
bound).  Both are *already* consequences of a run record at the same point:

* the `true` clause is exactly `RunParts.hcert` at the `ok` round;
* the `false` clause is `ball truth`: if some `Z` had `tr(AZ) < t - ε`, the ball of radius
  `dq/(8(c_A+1))` around `flat Z` would lie in the relaxed body (`strictBody_ball_relaxBall`), and then
  `BallM2.no_runParts_of_ball` would force the bit to be `true` — contradiction.

So no emptiness (and no thin-body analysis) is needed to certify the lower bound: the record does it.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Sound31

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding the leaf's `Poly` statements use. -/
instance instRequestCodingSound : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  A point strictly below the level carries the campaign ball into the body -/

/-- **The ball around a strict-below point.**  If `Z` is unit-diagonal PSD with `tr A Z` strictly
below the engine's level `t - Rq/40000`, then the campaign ball `dq/(8(c_A+1))` around `flat Z` lies
in the run's relaxation.  This is `strictBody_ball_relaxBall` at `M = 2n² + 2dq²`, which is exactly
the `runBall` of the engine. -/
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
  refine Set.Subset.trans ?_ (Set.Subset.refl _)
  have hM : 2 * (((G.n : ℝ)) ^ 2 + (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ 2)
      ≤ ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ) := by
    push_cast
    have h1 : (0 : ℝ) < ((P.cAq : ℚ) : ℝ) + 1 := by linarith
    have h2 : (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ^ 2 ≤ ((P.dq : ℚ) : ℝ) ^ 2 := by
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

#print axioms QMCLeafB.Sound31.ball_of_strict_below


/-! ## 2.  Strict-below points force the bit `true` -/

/-- **A strict-below point forces the bit `true`.**  With a run record at the point, the ball of
`ball_of_strict_below` contradicts the volumetric lemma. -/
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

#print axioms QMCLeafB.Sound31.bit_true_of_strict_below

/-! ## 3.  `SoundAt` from a run record -/

/-- **The leaf's soundness clause from the record alone.**  The upper clause is `hcert`; the lower
clause is `bit_true_of_strict_below` in contrapositive form.  No emptiness, no thin-body analysis. -/
theorem soundAt_of_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (B : QMCLeafB.FinalStroke.RunParts o G t P)
    (hKm : 0 < P.K * P.m) :
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

#print axioms QMCLeafB.Sound31.soundAt_of_runParts

/-! ## 4.  The closing stroke: a `RunParts` family is all the leaf needs -/

/-- **`SoundεOnBracket` from a `RunParts` family.** -/
theorem soundEpsOnBracket_of_family {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SoundεOnBracket o := by
  rw [QMCLeafB.VerdictSound.soundEpsOnBracket_iff]
  intro G t hlo hhi
  by_cases hn : 2 ≤ G.n
  · exact soundAt_of_runParts (P G) hn (B G t) (hKm G)
  · exact QMCLeafB.VerdictSound.soundAt_of_le_one o (by omega) t hlo hhi

#print axioms QMCLeafB.Sound31.soundEpsOnBracket_of_family


/-- **THE STROKE: `SolutionStatement` from a POLY BIT plus a `RunParts` family.**
No init/verdict structure, no size ledger, no `htop`, no emptiness analysis: the record at every
interior point certifies both clauses of the leaf's soundness, and the bracket stroke closes. -/
theorem solution_of_runPartsFamily (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    {P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (ho : Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (B : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts o G t (P G))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 0 < (P G).K * (P G).m) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o
    (soundEpsOnBracket_of_family B hKm) ho

#print axioms QMCLeafB.Sound31.solution_of_runPartsFamily

end QMCLeafB.Sound31


