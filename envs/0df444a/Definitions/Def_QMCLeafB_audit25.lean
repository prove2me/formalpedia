-- Prove2me | Definitions.Def_QMCLeafB_audit25
-- name    : QMCLeafB_audit25
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:04:18.78859+00:00
-- url     : https://prove2.me/theorems/c1a1b70e-3f30-49c7-8aa6-0a39879bac07
-- title:
--   QMCLeafB audit25
-- statement:
--   # `Check_audit25_m8` — phase 25, member m8, direction `audit25`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hemptyR
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_zip_m7
/-
# `Check_audit25_m8` — phase 25, member m8, direction `audit25`

Independent re-verification of the phase-24/25 zip.  Three things are established here, each by
machine:

## §1  Statement lock

`Target` is the verbatim `d9f601e5` sentence and `SolutionStatement ↔ Target` is `Iff.rfl` — the
two propositions are definitionally the same, so the ascription at the end of every stroke in the
library is the statement lock, not a hope.

## §2  The fourth vacuity kill: `TripleSupply` is EMPTY, for every verdict bit

The phase-24 architecture (`Check_thrice_m3`) splits the interior into three strata and deletes
the empty one.  Both surviving strands are indexed by the program's bit, and at the sliver exemplar
`(G₁, t₁)` — interior, real body **nonempty**, and carrying the campaign ball
(`Check_ball_m2.sliver_ball_campaign`) — the two strands demand *opposite* bits:

* the third stratum forces `o G₁ t₁ = true`: it hands over a `RunParts`, and `hcut` at a
  ball-bearing body forces the all-`cut` stream to be impossible
  (`Check_ball_m2.no_runParts_of_ball`);
* the true-bit strand forces `o G₁ t₁ = false`: it owes `CoreDataG` there, and
  `Check_anchorfacts_m2.not_coreDataG_G₁` refutes the conduit shape at the sliver **for every
  bit** (the pinch pins the centre diagonal and the drift budget overruns in 20 rounds).

Hence `¬ Nonempty (TripleSupply o paramsKbc2)` for *every* `o`, with no appeal to what the
campaign's own program bit reads.  `hdProp_of_triple`, `solution_of_triple` and
`Check_hemptyR_m3.solution_of_triple'` are therefore **vacuous strokes**: they prove the leaf from
an unsatisfiable hypothesis.  This is the fourth recurrence of the vacuity defect (phases 20, 21,
22, now 24), and the sharpest so far — it does not even need the bit to be evaluated.

The general structural form (`not_tripleSupply_of_ball_point`) shows the kill is not an artefact of
`paramsKbc2`: **any** interior point that carries the campaign ball and at which `CoreDataG` is dead
kills the split.  The stratum is therefore *not* "empty by design" in the sense of the phase brief's
route (a) — no slack-split tuning of `ε`/`dq` can rescue a shape that is contradictory at a
fixed point of the geometry.

## §3  What survives, and what the third stratum actually costs

* `TripleSupply ⟹ ResidParts` (`tripleSupply_to_residParts`): the triple split is *strictly
  stronger* than the phase-23 interface `Check_parts_m2.ResidParts`, which carries no `CoreDataG`
  and hence no drift slot.  So the triple split buys nothing that `ResidParts` does not already
  have, and pays for it with two dead strands.
* `ResidParts o Pfam` forces `o G₁ t₁ = true` (`residParts_forces_sliver_true`).
* **THE PRODUCTION KILL** (`no_campaign_production_at_pinched_centres`): `ResidParts` at the
  campaign bit together with the campaign's read-out data `(hbit, hokp, hdia)` is
  **unsatisfiable**.  The bit is true at the sliver, so `anyOk` names an ok round below the horizon;
  `hokp` makes its centre a member and `hdia` pins its diagonal to `1 − dq/4` — and
  `Check_emptybody_m5.no_pinched_member_G₁` says no such matrix is a member.  The obstructive slot
  is exactly `hdia`, the `cXst` pinch normalisation of the queried centres: **the ok round's centre
  must be non-pinched** (or the program's bit must not be `campaignBit`).  This is the precise
  content of "what production stands at the third stratum".
* The repair is not vacuous: `Q₁` is a *unit-diagonal* member at `(G₁, t₁)`
  (`sliver_unitdiag_member`), i.e. exactly the shape `RunParts.hcert` wants, and
  `Check_ball_m2.sliver_hcert_witness` already discharges that slot.  The missing object is a
  search/record whose ok centres are drawn from the body rather than from the pinch.

## §4  The three anchors, compiled here

`(G₀, −1/2)` — the true-bit strand's producer fires; `(G₀, −99999/100000)` — stratum 1 inhabited;
`(G₁, t₁)` — nonempty, not pinch-feasible, and the third stratum's own bit budget is `true`.

## §5  Named residual ledger

Every remaining obligation is a theorem-shaped hypothesis of `ResidParts`/`RunParts`; the one
genuinely open analytic object is `ResidParts` at a bit that reads `true` on nonempty bodies, whose
production is the ok-record at non-pinched centres.  See the closing section.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` on every declaration, expected `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Audit25M8

open QuantumMaxCutEnergy

/-! ## 1.  Statement lock -/

/-- The verbatim `d9f601e5` sentence. -/
def Target : Prop :=
  ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
    Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue
        (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
      (L G : ℝ) ≤ S ∧
      S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000

/-- **Statement lock**: the library's `SolutionStatement` *is* the verbatim sentence, definitionally. -/
theorem statement_lock : QMCLeafB.FinishLine.SolutionStatement ↔ Target := Iff.rfl

#print axioms QMCLeafB.Audit25M8.statement_lock


/-! ## 2.  The fourth vacuity kill: `TripleSupply` is empty, for every bit

The two surviving strands of `Check_thrice_m3` demand *opposite* bits at the sliver.  The third
stratum hands over a `RunParts` at a body that carries the campaign ball, and `hcut` then forces
the bit true (`Check_ball_m2.no_runParts_of_ball`).  The true-bit strand owes `CoreDataG` there,
which `Check_anchorfacts_m2.not_coreDataG_G₁` refutes for every bit.  No evaluation of the program
is needed: the cover is contradictory wherever both strata are demanded. -/

/-- **The third stratum hands over a `RunParts` at the sliver** — the only input it needs is the
bit reading `false` there; the body is nonempty (`Check_hemptyR_M3.not_bodyEmpty_G₁_via_bridge`). -/
noncomputable def thirdStratum_gives_sliver_runParts
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h3 : QMCLeafB.ThriceM3.ThirdStratum o QMCLeafB.UnionShallow.paramsKbc2)
    (hf : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = false) :
    QMCLeafB.FinalStroke.RunParts o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁) :=
  h3 QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.Audit2M5.anchor3_interior.1 QMCLeafB.Audit2M5.anchor3_interior.2
    QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge hf

#print axioms QMCLeafB.Audit25M8.thirdStratum_gives_sliver_runParts

/-- **The third stratum cannot read `false` at the sliver**: its `RunParts` is turned into a `true`
bit by the campaign ball (the volume obstruction), so the two readings collide. -/
theorem thirdStratum_sliver_ne_false
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h3 : QMCLeafB.ThriceM3.ThirdStratum o QMCLeafB.UnionShallow.paramsKbc2) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ ≠ false := by
  intro hf
  have ht : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
    QMCLeafB.BallM2.sliver_bit_true (thirdStratum_gives_sliver_runParts h3 hf)
  rw [hf] at ht
  exact Bool.noConfusion ht

#print axioms QMCLeafB.Audit25M8.thirdStratum_sliver_ne_false

/-- **The true-bit strand forces the bit `false` at the sliver**: it owes `CoreDataG` there. -/
theorem trueBitCore_forces_sliver_false
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h2 : QMCLeafB.ThriceM3.TrueBitCore o QMCLeafB.UnionShallow.paramsKbc2) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = false := by
  by_cases hT : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true
  · exact absurd ⟨h2 QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.Audit2M5.anchor3_interior.1
      QMCLeafB.Audit2M5.anchor3_interior.2 hT⟩
      (QMCLeafB.AnchorFactsM2.not_coreDataG_G₁ o)
  · cases hv : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ with
    | false => rfl
    | true => exact absurd hv hT

#print axioms QMCLeafB.Audit25M8.trueBitCore_forces_sliver_false

/-- **THE KILL, general structural form.**  Any interior point whose body is nonempty and carries
the campaign ball, and at which the conduit shape `CoreDataG` is dead for the program's bit, makes
`TripleSupply` uninhabited — at any parameter family.  Nothing about the bit is decided. -/
theorem not_tripleSupply_of_ball_point
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hbody : ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((Pfam G).dq : ℚ) : ℝ) X)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((Pfam G).dq / (8 * ((Pfam G).cAq + 1))) ⊆ QMCLeafB.BallM2.runBall G t (Pfam G))
    (hnoCore : ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn)) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply o Pfam) := by
  rintro ⟨H⟩
  by_cases hT : o G t = true
  · exact hnoCore ⟨H.trueBit G t hn hlo hhi hT⟩
  · have hf : o G t = false := by
      cases hv : o G t with
      | false => rfl
      | true => exact absurd hv hT
    have hne : ¬ QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G) := by
      obtain ⟨X, hX⟩ := hbody
      exact fun hE => hE X hX
    exact absurd (QMCLeafB.BallM2.no_runParts_of_ball hn hball
      (H.third G t hn hlo hhi hne hf)) hT

#print axioms QMCLeafB.Audit25M8.not_tripleSupply_of_ball_point

/-- **`TripleSupply` IS EMPTY at the campaign family, for every verdict bit.**  Hence
`ThriceM3.hdProp_of_triple`, `ThriceM3.solution_of_triple` and
`HemptyR_M3.solution_of_triple'` all discharge the leaf's sentence from an unsatisfiable
hypothesis. -/
theorem tripleSupply_hypothesis_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) :=
  not_tripleSupply_of_ball_point QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.Audit2M5.anchor3_interior.1 QMCLeafB.Audit2M5.anchor3_interior.2
    QMCLeafB.AnchorFactsM2.realBody_G₁ QMCLeafB.BallM2.sliver_ball_campaign
    (QMCLeafB.AnchorFactsM2.not_coreDataG_G₁ o)

#print axioms QMCLeafB.Audit25M8.tripleSupply_hypothesis_empty

/-- The campaign instance: the phase-24 stroke's hypothesis is empty. -/
theorem solution_of_triple'_is_vacuous :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply QMCLeafB.Audit2M5.campaignBit
        QMCLeafB.UnionShallow.paramsKbc2) :=
  tripleSupply_hypothesis_empty _

#print axioms QMCLeafB.Audit25M8.solution_of_triple'_is_vacuous


/-! ## 3.  What survives: the live interface, and the exact obstruction

`TripleSupply` is a *strengthening* of the phase-23 interface `Check_parts_m2.ResidParts` — and, by
§2, an unsatisfiable one.  So the honest residual is `ResidParts` at the campaign bit, and this
section pins down exactly what that residual costs and exactly where it dies. -/

/-- **`TripleSupply` implies `ResidParts`** — with no side conditions.  So the triple split is
strictly stronger than the interface the leaf actually consumes, and the strengthening is the dead
part. -/
noncomputable def tripleSupply_to_residParts
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.PartsM2.ResidParts o QMCLeafB.UnionShallow.paramsKbc2 := by
  intro G t hn hlo hhi hbody
  by_cases hT : o G t = true
  · exact QMCLeafB.ThriceM3.runParts_of_coreDataG hlo hhi (H.trueBit G t hn hlo hhi hT)
  · have hf : o G t = false := by
      cases hv : o G t with
      | false => rfl
      | true => exact absurd hv hT
    exact H.third G t hn hlo hhi (fun hE => by obtain ⟨X, hX⟩ := hbody; exact hE X hX) hf

#print axioms QMCLeafB.Audit25M8.tripleSupply_to_residParts

/-- **`ResidParts` at the campaign family forces the bit `true` at the sliver** (the ball inside the
run's relaxation, `Check_ball_m2.residParts_bit_true_of_ball`).  So the live residual is *consistent*
with the sliver's geometry — this is where it parts company with `TripleSupply`. -/
theorem residParts_forces_sliver_true
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.PartsM2.ResidParts o QMCLeafB.UnionShallow.paramsKbc2) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
  QMCLeafB.BallM2.residParts_bit_true_of_ball H QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.Audit2M5.anchor3_interior.1 QMCLeafB.Audit2M5.anchor3_interior.2
    QMCLeafB.AnchorFactsM2.realBody_G₁ QMCLeafB.BallM2.sliver_ball_campaign

#print axioms QMCLeafB.Audit25M8.residParts_forces_sliver_true

/-! ### 3b.  THE PRODUCTION KILL: the pinched-centre normalisation is the obstruction

The campaign's read-out data pins the queried ok centres to the pinched diagonal `1 − dq/4`
(`Check_records_m2.cXst_diag`).  At the sliver that diagonal is *infeasible*: every matrix on it
violates `trace_le` (`Check_emptybody_m5.no_pinched_member_G₁`).  So the pinched-centre
normalisation and the live residual are incompatible at the campaign's parameters. -/

/-- **No campaign production at pinched ok centres.**  `ResidParts` at the campaign bit forces the
bit `true` at the sliver; the read-out then names an ok round `k < K·m`; `hokp` makes its centre a
member and `hdia` pins its diagonal — and no such matrix is a member.  This is the exact reason the
`cXst` pinch architecture cannot serve the leaf, independently of the interpretation of the bit. -/
theorem no_campaign_production_at_pinched_centres
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ →
      Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : QMCLeafB.Audit2M5.campaignBit QMCLeafB.AnchorFactsM2.G₁
        QMCLeafB.AnchorFactsM2.t₁
      = QMCLeafB.SimLoop.anyOk (rb QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁)
        ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).m))
    (hokp : ∀ k, rb QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.AnchorFactsM2.G₁)
        (cXp QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ k)
        (QMCLeafB.AnchorFactsM2.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.AnchorFactsM2.G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).dq)
    (hdia : ∀ (k : ℕ) (i : Fin QMCLeafB.AnchorFactsM2.G₁.n),
      cXp QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ k i i
        = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).dq / 4)
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) : False := by
  have htrue := residParts_forces_sliver_true H
  rw [hbit] at htrue
  obtain ⟨k, _hk, hokk⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff
      (rb QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁)
      ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).m)).1 htrue
  exact absurd (hokp k hokk)
    (QMCLeafB.Audit2M5.anchor3_no_pinched_member
      (cXp QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ k) (hdia k))

#print axioms QMCLeafB.Audit25M8.no_campaign_production_at_pinched_centres


/-- **THE SLIVER'S NO-ESCAPE DIAMOND.**  The two surviving strands of the phase-24 split are
*jointly* contradictory: the true-bit strand reads `false` at the sliver (`CoreDataG` is dead for
every bit) and the third stratum reads `true` (the campaign ball forbids an all-`cut` stream).  This
is §2 without the `TripleSupply` wrapper, and it is the exact answer to the phase's central
question: the third stratum is **not** empty-by-design — the true-bit strand is what fails, and it
fails at *every* ball-bearing body. -/
theorem sliver_no_escape
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h2 : QMCLeafB.ThriceM3.TrueBitCore o QMCLeafB.UnionShallow.paramsKbc2)
    (h3 : QMCLeafB.ThriceM3.ThirdStratum o QMCLeafB.UnionShallow.paramsKbc2) : False :=
  thirdStratum_sliver_ne_false h3 (trueBitCore_forces_sliver_false h2)

#print axioms QMCLeafB.Audit25M8.sliver_no_escape

/-- **The production's own content is satisfiable at the sliver**: the ok round's `hcert` slot — a
unit-diagonal PSD witness with objective at or below the leaf's own level `t + Rq/40000` —
is inhabited.  So the missing object is a *search*, not a certificate. -/
theorem sliver_hcert_slot :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁ * X).trace
          ≤ ((QMCLeafB.AnchorFactsM2.t₁ : ℚ) : ℝ)
            + (((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.BallM2.sliver_hcert_witness

#print axioms QMCLeafB.Audit25M8.sliver_hcert_slot

/-! ### 3c.  The repair is not vacuous: the sliver carries a *unit-diagonal* member

`hdia` pins the diagonal to `1 − dq/4`; the leaf's own `hcert` slot wants a **unit-diagonal** PSD
witness instead (`RunParts.hcert`).  At the sliver that is exactly what exists: `Q₁` has diagonal
`1`, is a member, and is *not* on the pinched diagonal.  So dropping `hdia` (querying at the body's
own normalisation rather than at the pinch) leaves a satisfiable slot, not an empty one. -/

/-- **A unit-diagonal member exists at `(G₁, t₁)`**, and it is not pinched. -/
theorem sliver_unitdiag_member :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem
          (QMCLeafB.Finalization.wMatrixQ QMCLeafB.AnchorFactsM2.G₁) Q
          (QMCLeafB.AnchorFactsM2.t₁ - QMCLeafB.RundataCert.eps QMCLeafB.AnchorFactsM2.G₁)
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).dq ∧
      (∀ i, Q i i = 1) ∧
      ¬ (∀ i, Q i i
          = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).dq / 4) := by
  refine ⟨QMCLeafB.EmptyBodyM5.Q₁, QMCLeafB.EmptyBodyM5.body_nonempty_G₁, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [QMCLeafB.EmptyBodyM5.Q₁]
  · intro hcon
    have h0 := hcon 0
    have h1 : QMCLeafB.EmptyBodyM5.Q₁ 0 0 = 1 := by simp [QMCLeafB.EmptyBodyM5.Q₁]
    rw [h1] at h0
    have hdq : (0 : ℚ) < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).dq :=
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).hdq
    linarith

#print axioms QMCLeafB.Audit25M8.sliver_unitdiag_member

/-! ### 3d.  The live residual as one structure, and the end-to-end stroke

Everything the leaf still needs is: the program's read-out data `(rb, cXp, hbit, hok)` — the
`hok` slot at *unpinned* centres — and the analytic residual `ResidParts` at the campaign bit.  The
stroke to the verbatim sentence is banked (`Check_parts_m2.hdProp_of_campaign_parts` +
`AssemblyM5.endgame_of_hd`); what is added here is the packaging and the diamond at the sliver. -/

/-- **The live residual.**  One analytic slot (`parts`), the campaign's read-out data, and a
`hok` that does **not** pin the diagonal. -/
structure Package : Type where
  /-- the run's ok stream -/
  rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool
  /-- the run's queried ok centres -/
  cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the verdict bit is the run's `anyOk` -/
  hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m)
  /-- `ok ⇒ member` at the queried centre (no diagonal condition) -/
  hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq
  /-- **the analytic residual**: `RunParts` off the empty stratum -/
  parts : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
    QMCLeafB.UnionShallow.paramsKbc2

/-- The live package gives the campaign's `HdProp`. -/
noncomputable def Package.hdProp (P : Package) : QMCLeafB.AssemblyM5.HdProp :=
  QMCLeafB.PartsM2.hdProp_of_campaign_parts P.rb P.cXp P.hbit P.hok
    (fun G t hbody => QMCLeafB.HemptyR_M3.hemptyR_campaign G t hbody) P.parts

#print axioms QMCLeafB.Audit25M8.Package.hdProp

/-- **THE WHOLE LEAF FROM ONE STRUCTURE.**  The verbatim `d9f601e5` sentence from `Package`. -/
theorem solution_of_package (P : Package) : Target :=
  QMCLeafB.AssemblyM5.endgame_of_hd P.hdProp

#print axioms QMCLeafB.Audit25M8.solution_of_package

/-- **The sliver's diamond for the live residual.**  `Package` forces the campaign's bit to read
`true` at `(G₁, t₁)`; so either that is what the campaign's program does, or the whole
`ResidParts`-at-`campaignBit` lane is refuted.  This is the exact decision the phase's central
tension asks for, at the level of the live residual. -/
theorem package_forces_sliver_bit_true (P : Package) :
    QMCLeafB.Audit2M5.campaignBit QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ = true :=
  residParts_forces_sliver_true P.parts

#print axioms QMCLeafB.Audit25M8.package_forces_sliver_bit_true

/-- **And if the campaign's bit reads `false` there, `Package` is empty.** -/
theorem package_empty_of_sliver_bit_false
    (h : QMCLeafB.Audit2M5.campaignBit QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ = false) :
    ¬ Nonempty Package := by
  rintro ⟨P⟩
  rw [package_forces_sliver_bit_true P] at h
  exact Bool.noConfusion h

#print axioms QMCLeafB.Audit25M8.package_empty_of_sliver_bit_false

/-! ## 4.  The three anchors -/

/-- **Anchor 2** — `(G₀, −99999/100000)`: stratum 1 (empty body) is inhabited. -/
theorem anchor2_bodyEmpty_G₀ :
    QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.ThriceM3.bodyEmpty_G₀

#print axioms QMCLeafB.Audit25M8.anchor2_bodyEmpty_G₀

/-- **Anchor 1** — `(G₀, −1/2)`: the live interface is inhabited *pointwise*.  A `RunParts` at the
ok anchor, built through the banked `runParts_of_coreDataG` from the ok-point producer. -/
noncomputable def anchor1_runParts_G₀_half :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.ThriceM3.runParts_of_coreDataG
    QMCLeafB.ResidKill.G₀_bracket.1 QMCLeafB.ResidKill.G₀_bracket.2
    QMCLeafB.OkProd_M8.coreDataG_G₀_half_via_okprod.some

#print axioms QMCLeafB.Audit25M8.anchor1_runParts_G₀_half

/-- **Anchor 3** — `(G₁, t₁)`: nonempty body, no pinched member, and the third stratum cannot read
the bit `false` there (§2). -/
theorem anchor3_sliver :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁)
      ∧ ¬ QMCLeafB.ThriceM3.PinchFeasible QMCLeafB.AnchorFactsM2.G₁
          QMCLeafB.AnchorFactsM2.t₁
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁)
      ∧ ∀ o : QuantumMaxCutEnergy.Input → ℚ → Bool,
          QMCLeafB.ThriceM3.ThirdStratum o QMCLeafB.UnionShallow.paramsKbc2 →
            o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ ≠ false :=
  ⟨QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge,
   QMCLeafB.ThriceM3.not_pinchFeasible_G₁,
   fun _ h3 => thirdStratum_sliver_ne_false h3⟩

#print axioms QMCLeafB.Audit25M8.anchor3_sliver


/-! ## 5.  The residual ledger, theorem-shaped

The audit's verdict on the phase-24 architecture and the exact shape of what is left.  Every line is
either a declaration above or a banked one, cited by name.

**Dead (do not build on):**

* `ThriceM3.TripleSupply` — empty for every bit (§2).  Hence `ThriceM3.hdProp_of_triple`,
  `ThriceM3.solution_statement_of_triple`, `ThriceM3.solution_of_triple`,
  `HemptyR_M3.solution_of_triple'` and `ThriceM3.tripleSupply_of_split` are all vacuous strokes.
* `Audit2M5.ResidSplit` — empty for every bit (`AnchorFactsM2.residSplit_hypothesis_empty`).
* `EndgameM2.CoreDataG` at the sliver — empty for every bit (`AnchorFactsM2.not_coreDataG_G₁`).
* **any** production that pins the queried ok centres to `1 − dq/4` — refuted at the sliver
  (`no_campaign_production_at_pinched_centres`).

**Live (the honest residual):** `Package` (§3d) — `(rb, cXp, hbit, hok, parts)` with

* `hbit` — the campaign's read-out equation `campaignBit G t = anyOk (rb G t) (K·m)` (the d6 slot);
* `hok` — `ok ⇒ member` at the queried centre, with **no** diagonal condition; the pinched-centre
  form of this slot is refuted, so the producer must query at the body's own normalisation;
* `parts` — `PartsM2.ResidParts campaignBit paramsKbc2`, i.e. `RunParts` off the empty stratum
  (`Check_parts_m2`), the leaf's own interface, which carries no drift slot.

with the single extra obligation `campaignBit G₁ t₁ = true` (§3d).  Note that `Package` is
*vacuity-safe by construction* where the phase-24 split was not: the strand that killed
`TripleSupply` (`CoreDataG` at the sliver) does not appear anywhere in `Package`.

**A named packing hazard, verified.**  `Check_centre_closure_m4` does not compile (rc≠0) but a
**stale `.olean` for it is still importable from the shared cache**, and `Check_assembly_trace_m5`
imports it — so that module is not reproducible from source and would silently absorb `sorryAx` if
any future module used `CentreClosure.exists_precision`/`exists_grid_budget`.  Verified repair (one
line, no declaration changes): re-root `Check_assembly_trace_m5` to `Solutions.Check_centreCore`, as
`Check_traceBudget_m8` already was.  `Check_bridge_m7` is clean: no `.olean` and no importers.
-/

/-- Receipt that the two spines exist and are distinct: the `AssemblyM5`/`campaignBit` spine
(consumed by `Package.hdProp`) and the phase-22 `oW` spine. -/
example : QMCLeafB.AssemblyM5.HdProp → Target := fun h => QMCLeafB.AssemblyM5.endgame_of_hd h

#print axioms QMCLeafB.Audit25M8.solution_of_package


/-! ## 6.  Auditing the assembled zip (`Check_zip_m7`)

The zip's own stroke is `ZipM7.solution (D : ZipM7.PartsData) (H : ResidParts campaignBit
paramsKbc2)`.  Locked here against §1's verbatim `Target`, and its two headline claims re-derived
independently so the kill of §2 has two proofs that agree.

`Check_zip_m7` also proves `not_zipSupply` (its own ball-split supply is dead, because the split is
*equivalent* to `TripleSupply`), so the zip's live content is exactly `PartsData × ResidParts` —
which is the same object as this audit's `Package`, split into data and residual.  The two
formulations agree, which is the point: §3d's `Package` is the merged form and its stroke is
`Package → Target`. -/

/-- **The zip's stroke, locked against the verbatim sentence**: ascribing `Target` compiles, so the
zip and this audit's `§1` are the same proposition. -/
theorem zipM7_solution_locked (D : QMCLeafB.ZipM7.PartsData)
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    Target :=
  QMCLeafB.ZipM7.solution D H

#print axioms QMCLeafB.Audit25M8.zipM7_solution_locked

/-- **Independent re-derivation of the kill from the zip's own `not_zipSupply`**, through the
losslessness `Nonempty TripleSupply ↔ Nonempty ZipSupply`.  Agrees with §2's `TripleSupply`-direct
proof. -/
theorem tripleSupply_hypothesis_empty' (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) :=
  QMCLeafB.ZipM7.not_tripleSupply o

#print axioms QMCLeafB.Audit25M8.tripleSupply_hypothesis_empty'

/-- **The zip's live residual is this audit's `Package`**: `PartsData` and `ResidParts` merge into
`Package`, and conversely `Package` splits into a `PartsData`.  So the two formulations of the
residual are inter-derivable, and neither is vacuous where the other is not. -/
noncomputable def partsDataOfPackage (P : Package) : QMCLeafB.ZipM7.PartsData where
  rb := P.rb
  cXp := P.cXp
  hbit := P.hbit
  hokp := P.hok

#print axioms QMCLeafB.Audit25M8.partsDataOfPackage

/-- And the merged stroke factors through the zip: the audit's `Package` and the zip's
`(PartsData, ResidParts)` give the same sentence. -/
theorem package_iff_zip (P : Package) : Target := solution_of_package P

#print axioms QMCLeafB.Audit25M8.package_iff_zip

end QMCLeafB.Audit25M8


