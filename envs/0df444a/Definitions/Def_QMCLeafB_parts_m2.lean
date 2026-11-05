-- Prove2me | Definitions.Def_QMCLeafB_parts_m2
-- name    : QMCLeafB_parts_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:45.924531+00:00
-- url     : https://prove2.me/theorems/7c5825fe-8e4a-438d-a3d3-c7dd15493f39
-- title:
--   QMCLeafB parts_m2
-- statement:
--   # Leaf B phase 23 — m2, part 2: the corrected residual and its stroke
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_anchorfacts
/-
# Leaf B phase 23 — m2, part 2: the corrected residual and its stroke

Companion to `Check_anchorfacts_m2.lean` (§1–§5), which machine-checks that the phase-22 conduit
shape `EndgameM2.CoreDataG` is **uninhabited at the sliver exemplar `(G₁, t₁)` for every verdict
bit**, hence that `Audit2M5.ResidSplit` — and with it the accepted "closure stroke"
`Audit2M5.solution_of_split` — is vacuous.

This file supplies the coordinate move that refutation forces: the leaf's residual restated at the
interface the leaf actually consumes, `QMCLeafB.FinalStroke.RunParts`, which carries **no drift
slots** at all (`hcert hwit hrho hcne hdel0 hcheck hle hcut hverdict` — see
`Check_final_stroke_m7`).  Two consequences make that the right home:

* the empty real body is discharged outright by `RefutedM3.runParts_of_emptyBody` (no drift, bit
  `false`);
* on a nonempty body the residual is genuine separation work, not a trace budget — so the pinch
  ceiling `n(1 − dq/4)` never enters.

Nothing here is new mathematics: `hdProp_of_parts` is `Audit2M5.runParts_of_split` with the
`CoreDataG` branch replaced by a supplied `RunParts`, and `bitfalse_of_campaign` is verbatim the
internal step of that stroke (`RefutedM3.bit_false_of_emptyBody`).  The payoff is
`hdProp_of_campaign_parts`, whose conclusion `AssemblyM5.HdProp` is consumed by the already-banked
verbatim ending `AssemblyM5.endgame_of_hd` / `endgame_of_hd_statement`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.PartsM2

open QuantumMaxCutEnergy

/-- **The corrected residual**: `RunParts` on the nonempty-body stratum only.  No `CoreDataG`
anywhere, hence no drift obligation, hence no pinch ceiling. -/
abbrev ResidParts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    (∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((Pfam G).dq : ℚ) : ℝ) X) →
    QMCLeafB.FinalStroke.RunParts o G t (Pfam G)

/-- **The branch split at the leaf's own interface.**  Empty real body ⇒
`RefutedM3.runParts_of_emptyBody` (bit `false`, drift-free); nonempty ⇒ the supplied `RunParts`.
This replaces `Audit2M5.runParts_of_split`'s `CoreDataG` route, which
`AnchorFactsM2.not_coreDataG_G₁` shows cannot be inhabited at the sliver. -/
def hdProp_of_parts
    (H : ResidParts QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2)
    (hbitfalse : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      QMCLeafB.Audit2M5.campaignBit G t = false) :
    QMCLeafB.AssemblyM5.HdProp := by
  intro G t hn hlo hhi
  by_cases hbody : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn (hbitfalse G t hbody) hbody
  · have hbl : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X := by
      obtain ⟨X, hX⟩ := not_forall.mp hbody
      exact ⟨X, Classical.not_not.mp hX⟩
    exact H G t hn hlo hhi hbl

#print axioms QMCLeafB.PartsM2.hdProp_of_parts

/-- **The bit is `false` on the empty stratum**: `RefutedM3.bit_false_of_emptyBody` against the
campaign's own read-out data (`rb`, `cXp`, `hbit`, `hok`, `hemptyR`).  This is exactly the internal
step of `Audit2M5.runParts_of_split`, exposed as a named slot. -/
theorem bitfalse_of_campaign
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      QMCLeafB.Audit2M5.campaignBit G t = false :=
  fun G t hbody =>
    QMCLeafB.RefutedM3.bit_false_of_emptyBody (hbit G t) (hok G t) (hemptyR G t hbody)

#print axioms QMCLeafB.PartsM2.bitfalse_of_campaign

/-- **THE CORRECTED CAMPAIGN RESIDUAL, AND ITS STROKE.**  From the campaign's own read-out data and
`ResidParts` — `RunParts` off the empty stratum — the leaf's `HdProp`, hence (by the banked verbatim
ending `AssemblyM5.endgame_of_hd`) the `d9f601e5` sentence.  Note what is *absent*: `CoreDataG`,
`ResidSplit`, and with them the whole-window drift pair and the pinch ceiling. -/
def hdProp_of_campaign_parts
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidParts QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  hdProp_of_parts H (bitfalse_of_campaign rb cXp hbit hok hemptyR)

#print axioms QMCLeafB.PartsM2.hdProp_of_campaign_parts

end QMCLeafB.PartsM2


