-- Prove2me | Definitions.Def_QMCLeafB_zip_m7
-- name    : QMCLeafB_zip_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:52:33.861707+00:00
-- url     : https://prove2.me/theorems/d2c3aea9-7801-42c8-8e07-4f31e889b5a8
-- title:
--   QMCLeafB zip_m7
-- statement:
--   # `Check_zip_m7` — phase 25, member m7, direction `final-zip25`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hemptyR
import Definitions.Def_QMCLeafB_ball_m2
/-
# `Check_zip_m7` — phase 25, member m7, direction `final-zip25`

The phase-24 zip reduced the leaf to

    (campaign data) → `ThriceM3.TripleSupply campaignBit paramsKbc2` → `<verbatim d9f601e5>`

(`Check_hemptyR_m3.solution_of_triple'`).  This file assembles the zip and **decides what can stand
in its residual slot**, machine-checking the phase's central tension at the assembly interface.

## The answer this file gives

**The third stratum is not empty by design.**  At the sliver `(G₁,t₁)` (two vertices, one edge of
weight `1`, `t₁ = −2 + 71/1520000`) the relaxed body is *nonempty*, carries the campaign ball of
radius `dq/24`, and admits **no** matrix on the pinched diagonal `1 − dq/4`
(`sliver_third_stratum_real`, from three banked facts).  It is a genuine stratum.

**What stands there is the ok lane, at an un-pinched witness.**  `sliver_runParts_okStream` builds a
`RunParts` at the sliver outright: `ok ≡ true` fires no cut round, so no separation work is owed,
and every round hands over the exact-PSD unit-diagonal witness of `BallM2.sliver_hcert_witness`.
`sliver_production_dichotomy` adds that *every* production there has bit `true` — so an all-`cut`
stream is impossible, not merely unproved.

**What does not stand there: any pinched-centre design.**  `not_residParts_of_pinched` shows that a
campaign read-out recording its `ok` centres on the pinched diagonal `1 − dq/4` is incompatible with
the residual, and `pinch_constraint_not_forced` shows the pinch is *not* forced: `EmptyBodyM5.Q₁` is
a member at the sliver with unit diagonal while `1 − dq/4 ≠ 1`.  So the pinch constraint is a design
choice, and it is the wrong one.

## Results, in order

* **§0** statement lock (`rfl`): `FinishLine.SolutionStatement` *is* the verbatim `d9f601e5` sentence.
* **§1** the ball split: `BallFree`, `ThinThird`, `BallTrueBit`, `ZipSupply`.
* **§2** `TripleSupply ↔ ZipSupply` — the split is lossless, and it proves that at ball-bearing
  bodies the residual owes a *bit*, never a `RunParts`.
* **§3b** `PartsData` (no diagonal slot) + `PartsM2.ResidParts campaignBit paramsKbc2` →
  `solution`, the verbatim sentence, `hemptyR` inlined.  **This is the residual that survives.**
* **§4** `not_tripleSupply (o)` for *every* bit: `CoreDataG` is dead at the sliver
  (`AnchorFactsM2.not_coreDataG_G₁`) and the ball kills the `false` branch.  `not_zipSupply`
  inherits it through §2.
* **§5** the pinch is the obstruction, and it is not forced.
* **§5b** the sliver: real, ball-bearing, pinched-member-free — and producible by the ok lane.
* **§6** the three anchors.

## Named residual, one slot

    PartsM2.ResidParts campaignBit paramsKbc2

at the read-out `PartsData` whose `ok` rounds certify members at **un-pinched** centres.  Nothing
else is owed: no `CoreDataG`, no pinched-centre slot, no `hemptyR`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` on every declaration, all exactly `[propext, Classical.choice, Quot.sound]`.
-/


open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ZipM7

open QuantumMaxCutEnergy

/-! ## 0.  Statement lock -/

/-- The sentence every stroke below proves, definitionally. -/
theorem statement_lock :
    QMCLeafB.FinishLine.SolutionStatement =
      (∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) := rfl

#print axioms QMCLeafB.ZipM7.statement_lock

/-! ## 1.  The ball split of the third stratum

`Check_ball_m2.no_runParts_of_ball`: at a body containing the campaign ball of radius
`dq/(8(c_A+1))`, **any** `RunParts` forces the bit `true`.  So a `false`-bit `RunParts` obligation
can only live at ball-free bodies.  We name both sides of the cut. -/

/-- **Ball-free**: no translate of the campaign ball is contained in the run's body at `(G,t)`.
This is the complement of `no_runParts_of_ball`'s hypothesis, uniformly in the centre. -/
def BallFree (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X₀ : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P

/-- **The thin third stratum**: `RunParts` at an interior `false`-bit point with a nonempty
**ball-free** body.  This is the only place `Check_ball_m2` leaves a `RunParts` obligation. -/
abbrev ThinThird (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G) → BallFree G t (Pfam G) →
    o G t = false → QMCLeafB.FinalStroke.RunParts o G t (Pfam G)

/-- **The ball-bearing bit slot**: at an interior point with a nonempty body that *does* carry the
campaign ball, the program's bit reads `true`.  This is a statement about the program, not about
`RunParts`; it is the design freedom the ball obstruction forces (the ok-production lane). -/
abbrev BallTrueBit (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (_hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G) → ¬ BallFree G t (Pfam G) → o G t = true

/-- **The zipped supply**: the true-bit production, the ball-bearing bit design fact, and the thin
production.  Every field is theorem-shaped; none is prose. -/
structure ZipSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- `CoreDataG` at the `true`-bit interior points (the ok lane, `hon` + the frozen member). -/
  trueBit : QMCLeafB.ThriceM3.TrueBitCore o Pfam
  /-- the campaign bit is `true` at ball-bearing nonempty interior points. -/
  ballTrue : BallTrueBit o Pfam
  /-- `RunParts` at `false`-bit nonempty interior points whose body is ball-free. -/
  thinThird : ThinThird o Pfam

/-! ## 2.  The split is exactly the third stratum

`ThinThird + BallTrueBit` reconstructs `ThirdStratum` (the ball-bearing `false`-bit case is excluded
by the bit), and conversely `ThirdStratum` forces `BallTrueBit` (a `false` bit there would demand a
`RunParts` that the ball refutes).  Hence the split is lossless *and* it exposes that no `RunParts`
obligation survives off the ball-free bodies. -/

/-- **`ZipSupply ⟹ ThirdStratum`.** -/
noncomputable def thirdStratum_of_zip
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ZipSupply o Pfam) : QMCLeafB.ThriceM3.ThirdStratum o Pfam := by
  intro G t hn hlo hhi hbody hf
  by_cases hbf : BallFree G t (Pfam G)
  · exact H.thinThird G t hn hlo hhi hbody hbf hf
  · have ht : o G t = true := H.ballTrue G t hn hlo hhi hbody hbf
    rw [hf] at ht
    exact absurd ht (by simp)

#print axioms QMCLeafB.ZipM7.thirdStratum_of_zip

/-- **`ZipSupply ⟹ TripleSupply`** (the banked phase-24 shape). -/
noncomputable def tripleSupply_of_zip
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ZipSupply o Pfam) : QMCLeafB.ThriceM3.TripleSupply o Pfam where
  trueBit := H.trueBit
  third := thirdStratum_of_zip H

#print axioms QMCLeafB.ZipM7.tripleSupply_of_zip

/-- **`ThirdStratum` forces the ball-bearing bit `true`** — the load-bearing half of the
equivalence, and the reason the ball-bearing part of the residual is a *bit* obligation: if the bit
there were `false`, `ThirdStratum` would hand over a `RunParts` that `no_runParts_of_ball` refutes. -/
theorem ballTrueBit_of_thirdStratum
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.ThriceM3.ThirdStratum o Pfam) : BallTrueBit o Pfam := by
  intro G t hn hlo hhi hbody hnbf
  by_contra hnt
  have hf : o G t = false := by
    cases h : o G t with
    | false => rfl
    | true => exact absurd h hnt
  have hex : ∃ X₀ : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((Pfam G).dq : ℝ) / (8 * (((Pfam G).cAq : ℝ) + 1)))
        ⊆ QMCLeafB.BallM2.runBall G t (Pfam G) := by
    by_contra hc
    exact hnbf (fun X₀ hsub => hc ⟨X₀, hsub⟩)
  obtain ⟨X₀, hsub⟩ := hex
  have ht : o G t = true :=
    QMCLeafB.BallM2.no_runParts_of_ball hn hsub (H G t hn hlo hhi hbody hf)
  rw [hf] at ht
  exact absurd ht (by simp)

#print axioms QMCLeafB.ZipM7.ballTrueBit_of_thirdStratum

/-- **`TripleSupply ⟹ ZipSupply`.**  Nothing is added: `thinThird` is `third` restricted to the
ball-free bodies, `ballTrue` is the bit consequence above. -/
noncomputable def zipSupply_of_triple
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.ThriceM3.TripleSupply o Pfam) : ZipSupply o Pfam where
  trueBit := H.trueBit
  ballTrue := ballTrueBit_of_thirdStratum H.third
  thinThird := fun G t hn hlo hhi hbody _hf hf => H.third G t hn hlo hhi hbody hf

#print axioms QMCLeafB.ZipM7.zipSupply_of_triple

/-- **The split is lossless**: the two residuals are inhabited simultaneously. -/
theorem nonempty_tripleSupply_iff_zipSupply
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G} :
    Nonempty (QMCLeafB.ThriceM3.TripleSupply o Pfam) ↔ Nonempty (ZipSupply o Pfam) :=
  ⟨fun ⟨H⟩ => ⟨zipSupply_of_triple H⟩, fun ⟨H⟩ => ⟨tripleSupply_of_zip H⟩⟩

#print axioms QMCLeafB.ZipM7.nonempty_tripleSupply_iff_zipSupply

/-! ## 3.  The stroke at the campaign family

The campaign's read-out data (`hbit`, `hokp`, `hdia`) is the only non-residual input; it is
`RoundWRepoint`-shaped, and at a `false`-bit point it is free
(`Check_zip_m7.partsData_of_falseBit` below). -/

/-- **The campaign's own data at the leaf's interface.** -/
structure ZipData where
  rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool
  cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m)
  hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq
  hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
    cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4

/-- **The zipped stroke, `SolutionStatement` form** (the shelf's own name for the sentence). -/
theorem solution_statement_of_zip (D : ZipData)
    (H : ZipSupply QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.HemptyR_M3.solution_of_triple' D.rb D.cXp D.hbit D.hokp D.hdia
    (tripleSupply_of_zip H)

#print axioms QMCLeafB.ZipM7.solution_statement_of_zip

/-- **The zipped stroke at the phase-24 slot** — same conclusion from the banked `TripleSupply`,
recorded so the two forms can be compared slot by slot. -/
theorem solution_statement_of_tripleSupply (D : ZipData)
    (H : QMCLeafB.ThriceM3.TripleSupply QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.HemptyR_M3.solution_of_triple' D.rb D.cXp D.hbit D.hokp D.hdia H

#print axioms QMCLeafB.ZipM7.solution_statement_of_tripleSupply

/-- **`d9f601e5`, verbatim, from the ball-split supply.**  Superseded by `solution` below: §4 shows
no `ZipSupply` exists at the campaign bit, because the true-bit lane needs `CoreDataG`. -/
theorem solution_of_zip (D : ZipData)
    (H : ZipSupply QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  solution_statement_of_zip D H

#print axioms QMCLeafB.ZipM7.solution_of_zip

/-- **The lock, two-way**: the verbatim sentence above *is* `FinishLine.SolutionStatement`. -/
theorem solution_lock :
    QMCLeafB.FinishLine.SolutionStatement ↔
      (∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
        Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
          QuantumMaxCutEnergy.encodeValue
          (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
        ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
          ModernConvex.Relaxations.IsMaxcutSDPValue
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
          (L G : ℝ) ≤ S ∧
          S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000) := Iff.rfl

#print axioms QMCLeafB.ZipM7.solution_lock

/-! ## 3b.  The non-vacuous stroke: `RunParts` on the nonempty stratum, no `CoreDataG`

§4 below shows that *any* residual carrying `CoreDataG` (`CoreDataG` is dead at the sliver for every
bit: `AnchorFactsM2.not_coreDataG_G₁`) or a pinched-centre read-out is uninhabited.  The residual
that survives is the phase-23 canonical `PartsM2.ResidParts`: `RunParts` at every nonempty interior
point, with the campaign's read-out carrying **no** diagonal constraint on the recorded centres.
The `hemptyR` bridge is discharged here, unconditionally. -/

/-- **The campaign's read-out data with no pinch**: a stream whose `ok` flag reads out as the bit and
whose `ok` rounds are members at *whatever* centres the run records.  The diagonal slot
(`ZipData.hdia`) is deliberately absent — §5 shows it is not forced. -/
structure PartsData where
  rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool
  cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m)
  hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq

/-- Every `ZipData` is a `PartsData` (the pinch constraint is simply dropped). -/
def partsDataOfZip (D : ZipData) : PartsData where
  rb := D.rb
  cXp := D.cXp
  hbit := D.hbit
  hokp := D.hokp

/-- **The leaf from the surviving residual**, `SolutionStatement` form. -/
theorem solution_statement_of_parts (D : PartsData)
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement
    (QMCLeafB.PartsM2.hdProp_of_campaign_parts D.rb D.cXp D.hbit D.hokp
      (fun G t hbody => QMCLeafB.HemptyR_M3.hemptyR_campaign G t hbody) H)

#print axioms QMCLeafB.ZipM7.solution_statement_of_parts

/-- **`d9f601e5`, verbatim, from the surviving residual.**  The whole leaf is now one named
hypothesis: `PartsM2.ResidParts campaignBit paramsKbc2`, with no `CoreDataG` slot, no pinched-centre
slot, and no `hemptyR` slot. -/
theorem solution (D : PartsData)
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  solution_statement_of_parts D H

#print axioms QMCLeafB.ZipM7.solution

/-! ## 4.  The falsification: the phase-24 slot cannot be filled at a pinched campaign bit

`TripleSupply` demands `RunParts` at *every* `false`-bit nonempty interior point.  At the sliver
`(G₁,t₁)` the body is nonempty (`HemptyR_M3.not_bodyEmpty_G₁_via_bridge`), carries the campaign ball
(`BallM2.sliver_ball_campaign`), and no pinched matrix is a member
(`ThriceM3.not_pinchFeasible_G₁`), so every pinched-centre stream reads `false` there
(`ThriceM3.bit_false_at_exemplar`).  `no_runParts_of_ball` then kills the required `RunParts`.
Hence **`TripleSupply campaignBit paramsKbc2` is uninhabited for any campaign data with pinched
centres**, and the ball-bearing bit is a genuine design object. -/

/-- The sliver is **ball-bearing**, so it lies outside `ThinThird`'s territory: the ball cut is not
vacuous at the exemplar. -/
theorem not_ballFree_sliver :
    ¬ BallFree QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁) :=
  fun h => h QMCLeafB.BallM2.Xs QMCLeafB.BallM2.sliver_ball_campaign

#print axioms QMCLeafB.ZipM7.not_ballFree_sliver

/-- **`TripleSupply` forces the campaign bit `true` at the sliver**, for every program bit `o`.
Unconditional: it uses only the banked nonemptiness of the sliver body and the banked ball. -/
theorem tripleSupply_forces_sliver_true
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true := by
  have hbody : ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁) :=
    QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge
  have hbr := QMCLeafB.EmptyBodyM5.t₁_mem_bracket
  by_contra hnt
  have hf : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = false := by
    cases h : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ with
    | false => rfl
    | true => exact absurd h hnt
  have hRP : QMCLeafB.FinalStroke.RunParts o QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁) :=
    H.third QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
      hbr.1 hbr.2 hbody hf
  have ht : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
    QMCLeafB.BallM2.no_runParts_of_ball QMCLeafB.AnchorFactsM2.hn₁
      QMCLeafB.BallM2.sliver_ball_campaign hRP
  rw [hf] at ht
  exact absurd ht (by simp)

#print axioms QMCLeafB.ZipM7.tripleSupply_forces_sliver_true

/-- **The same at the zipped supply** — the ball slot alone already forces the sliver bit. -/
theorem zipSupply_forces_sliver_true
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : ZipSupply o QMCLeafB.UnionShallow.paramsKbc2) :
    o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ = true :=
  tripleSupply_forces_sliver_true (tripleSupply_of_zip H)

#print axioms QMCLeafB.ZipM7.zipSupply_forces_sliver_true

/-- **THE FALSIFICATION.**  At the campaign bit, any pinched-centre read-out data makes
`TripleSupply` uninhabited: the run is forced `false` at the sliver by
`ThriceM3.bit_false_at_exemplar` and forced `true` by the ball.  So the phase-24 residual has no
producer at a pinched campaign bit, and the leaf's zip must either move the program's ok test to a
level that reads `true` at ball-bearing bodies, or key the residual by the ball cut (this file's
`ZipSupply`, whose `ballTrue` slot is then exactly the missing design theorem). -/
theorem not_tripleSupply_of_pinched_campaign
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ)
    (hbit : QMCLeafB.Audit2M5.campaignBit QMCLeafB.EmptyBodyM5.G₁
        (-(2 : ℚ) + 71 / 1520000)
      = QMCLeafB.SimLoop.anyOk rb
        ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) (cX k)
        (-(2 : ℚ) + 71 / 1520000 - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2),
      cX k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have htrue := tripleSupply_forces_sliver_true H
  have hfalse := QMCLeafB.ThriceM3.bit_false_at_exemplar hbit hok hdia
  rw [hfalse] at htrue
  exact absurd htrue (by simp)

#print axioms QMCLeafB.ZipM7.not_tripleSupply_of_pinched_campaign

/-! ## 4b.  The unconditional vacuity kill

`TripleSupply` needs `CoreDataG` at every `true`-bit point, and `CoreDataG` is dead at the sliver for
**every** bit (`AnchorFactsM2.not_coreDataG_G₁`, the crater).  The `false`-bit branch is dead by the
ball.  So neither branch can be filled: the phase-24 residual is uninhabited at *every* program bit,
not merely at a pinched one.  By §2 the same holds for the ball-split supply — the split localises
the obligation, it does not rescue `CoreDataG`. -/

/-- **`TripleSupply` is uninhabited for every verdict bit.** -/
theorem not_tripleSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.ThriceM3.TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have hbody : ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.AnchorFactsM2.G₁
      QMCLeafB.AnchorFactsM2.t₁ (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁) :=
    QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge
  have hbr := QMCLeafB.EmptyBodyM5.t₁_mem_bracket
  cases hb : o QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ with
  | true =>
      exact QMCLeafB.AnchorFactsM2.not_coreDataG_G₁ o
        ⟨H.trueBit QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
          hbr.1 hbr.2 hb⟩
  | false =>
      have B := H.third QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
        hbr.1 hbr.2 hbody hb
      have ht := QMCLeafB.BallM2.sliver_bit_true B
      rw [hb] at ht
      exact absurd ht (by simp)

#print axioms QMCLeafB.ZipM7.not_tripleSupply

/-- **`ZipSupply` is uninhabited too** — the ball split is lossless, so it inherits the kill. -/
theorem not_zipSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (ZipSupply o QMCLeafB.UnionShallow.paramsKbc2) := by
  rw [← nonempty_tripleSupply_iff_zipSupply]
  exact not_tripleSupply o

#print axioms QMCLeafB.ZipM7.not_zipSupply

/-! ## 5.  The pinched read-out is the obstruction, and it is not forced

`ResidParts` survives the kill above because it carries no `CoreDataG`.  What it *cannot* survive is
the campaign's diagonal constraint `hdia` on the recorded centres: at the sliver the pinched lower
edge `1 − dq/4` admits no member (`EmptyBodyM5.no_pinched_member_G₁`), so a pinched ok stream reads
`false`, while `RunParts` forces `true`.  That is the exact design freedom the leaf has: the run must
record its ok certificates at an **un-pinched** member — and at the sliver such a member exists,
`EmptyBodyM5.Q₁` (unit diagonal).  So the constraint `hdia` is a genuine extra assumption, not a
consequence of the read-out. -/

/-- **The pinched read-out admits no `ResidParts`.** -/
theorem not_residParts_of_pinched (D : ZipData) :
    ¬ Nonempty (QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have hbr := QMCLeafB.EmptyBodyM5.t₁_mem_bracket
  have hbody : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.AnchorFactsM2.G₁)
        (((-(2 : ℚ) + 71 / 1520000 : ℚ) : ℝ)
          - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.AnchorFactsM2.G₁ / 40000 : ℚ)) : ℝ))
        ((((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.AnchorFactsM2.G₁).dq : ℚ)) : ℝ) X :=
    QMCLeafB.AnchorFactsM2.realBody_G₁
  have B := H QMCLeafB.AnchorFactsM2.G₁ QMCLeafB.AnchorFactsM2.t₁ QMCLeafB.AnchorFactsM2.hn₁
    hbr.1 hbr.2 hbody
  have htrue := QMCLeafB.BallM2.sliver_bit_true B
  have hfalse := QMCLeafB.ThriceM3.bit_false_at_exemplar
    (rb := D.rb QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000))
    (cX := D.cXp QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000))
    (D.hbit QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000))
    (D.hokp QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000))
    (D.hdia QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000))
  rw [htrue] at hfalse
  exact absurd hfalse (by simp)

#print axioms QMCLeafB.ZipM7.not_residParts_of_pinched

/-- **The sliver has an un-pinched member with unit diagonal** — the ok-certificate slot is
satisfiable off the pinch. -/
theorem sliver_unpinched_member :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁)
        QMCLeafB.EmptyBodyM5.Q₁
        ((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq ∧
      (∀ i, QMCLeafB.EmptyBodyM5.Q₁ i i = 1) :=
  ⟨QMCLeafB.EmptyBodyM5.body_nonempty_G₁,
    fun i => by fin_cases i <;> norm_num [QMCLeafB.EmptyBodyM5.Q₁]⟩

#print axioms QMCLeafB.ZipM7.sliver_unpinched_member

/-- The pinched edge `1 − dq/4` is strictly below `1` at the sliver (`dq = 1/380000 > 0`). -/
theorem sliver_pinch_ne_one :
    (1 : ℚ) - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4 ≠ 1 := by
  rw [QMCLeafB.EmptyBodyM5.dq₁_eq]
  norm_num

#print axioms QMCLeafB.ZipM7.sliver_pinch_ne_one

/-- **The pinch constraint is not forced**: a member exists at the sliver, and no member there sits
on the pinched diagonal — so `hdia` is an extra design assumption, and the production that stands at
the third stratum is an un-pinched ok certificate plus genuinely separating cut rounds. -/
theorem pinch_constraint_not_forced :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) Q
          ((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq ∧
        ¬ (∀ i, Q i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) := by
  refine ⟨QMCLeafB.EmptyBodyM5.Q₁, sliver_unpinched_member.1, ?_⟩
  intro h
  have h1 : QMCLeafB.EmptyBodyM5.Q₁ 0 0 = 1 := by
    norm_num [QMCLeafB.EmptyBodyM5.Q₁]
  rw [h 0] at h1
  exact sliver_pinch_ne_one h1

#print axioms QMCLeafB.ZipM7.pinch_constraint_not_forced

/-! ## 5.  Conservativity, and the residual's residual

Nothing banked is lost: a `PartsM2.ResidParts` producer (the phase-23 canonical) is a `ZipSupply`
producer.  What is gained is the location: at ball-bearing bodies `ZipSupply` owes a *bit*, not a
`RunParts`; at ball-free bodies it owes `RunParts` (`ThinThird`). -/

/-- **`ResidParts` restricted to ball-free bodies is `ThinThird`.** -/
noncomputable def thinThird_of_residParts
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.PartsM2.ResidParts o Pfam) : ThinThird o Pfam :=
  fun G t hn hlo hhi hbody _hbf _hf =>
    H G t hn hlo hhi (by
      by_contra hc
      exact hbody (fun X hX => hc ⟨X, hX⟩))

#print axioms QMCLeafB.ZipM7.thinThird_of_residParts

/-- **`ResidParts + TrueBitCore ⟹ ZipSupply`**: the phase-23 residual is a producer for this one. -/
noncomputable def zipSupply_of_residParts
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (htrue : QMCLeafB.ThriceM3.TrueBitCore o Pfam)
    (H : QMCLeafB.PartsM2.ResidParts o Pfam) : ZipSupply o Pfam where
  trueBit := htrue
  ballTrue := ballTrueBit_of_thirdStratum
    (fun G t hn hlo hhi hbody hf =>
      H G t hn hlo hhi (by
        by_contra hc
        exact hbody (fun X hX => hc ⟨X, hX⟩)))
  thinThird := thinThird_of_residParts H

#print axioms QMCLeafB.ZipM7.zipSupply_of_residParts

/-! ## 5b.  The sliver is real, and the production that stands there

Assembling the whole picture at `(G₁,t₁)`:

* the body is **nonempty** (`HemptyR_M3.not_bodyEmpty_G₁_via_bridge`) — so the third stratum is *not*
  empty by design;
* it is **ball-bearing** (`not_ballFree_sliver`) — so the ball obstruction applies at full strength;
* it has **no pinched member** (`ThriceM3.not_pinchFeasible_G₁`);
* yet `RunParts` **is** inhabited there, by the ok lane: `ok ≡ true` fires no cut round, and each
  round hands over the exact-PSD unit-diagonal witness of `BallM2.sliver_hcert_witness`, whose
  objective sits at the program's level (`sliver_hcert_witness`).

So the production that stands at the third stratum is exactly the ok lane evaluated at an
**un-pinched** witness, and `sliver_production_dichotomy` records that *every* production there has
bit `true` — the all-`cut`/pinched design is impossible, not merely unproved. -/

abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.AnchorFactsM2.G₁
abbrev t₁ : ℚ := QMCLeafB.AnchorFactsM2.t₁
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁

/-- **The ok stream inhabits `RunParts` at the sliver.**  `ok ≡ true` makes every cut slot vacuous,
so no separation is owed; the certificate slot is `sliver_hcert_witness`. -/
noncomputable def sliver_runParts_okStream :
    QMCLeafB.FinalStroke.RunParts
      (fun _ _ => QMCLeafB.SimLoop.anyOk (fun _ => true) (P₁.K * P₁.m)) G₁ t₁ P₁ where
  ok := fun _ => true
  cd := fun _ => ⟨0, 0, 0⟩
  del := fun _ => 0
  hcert := fun _ _ _ => QMCLeafB.BallM2.sliver_hcert_witness
  hwit := fun _ _ hf => absurd hf (by simp)
  hrho := fun _ _ hf => absurd hf (by simp)
  hcne := fun _ _ hf => absurd hf (by simp)
  hdel0 := fun _ _ hf => absurd hf (by simp)
  hcheck := fun _ _ hf => absurd hf (by simp)
  hle := fun _ _ hf => absurd hf (by simp)
  hcut := fun _ _ hf => absurd hf (by simp)
  hverdict := rfl

#print axioms QMCLeafB.ZipM7.sliver_runParts_okStream

/-- **THE CAPSTONE**: at the sliver a production exists, *and* every production reads the bit `true`.
The third stratum is therefore real (not empty by design), its only possible production is the ok
lane, and the pinched/all-cut design that the campaign recorded cannot reach it. -/
theorem sliver_production_dichotomy :
    (∃ o : QuantumMaxCutEnergy.Input → ℚ → Bool,
        Nonempty (QMCLeafB.FinalStroke.RunParts o G₁ t₁ P₁)) ∧
      (∀ (o : QuantumMaxCutEnergy.Input → ℚ → Bool),
        QMCLeafB.FinalStroke.RunParts o G₁ t₁ P₁ → o G₁ t₁ = true) :=
  ⟨⟨_, ⟨sliver_runParts_okStream⟩⟩, fun _ B => QMCLeafB.BallM2.sliver_bit_true B⟩

#print axioms QMCLeafB.ZipM7.sliver_production_dichotomy

/-- **The third stratum at the sliver, in one statement**: body nonempty, ball-bearing, no pinched
member.  So it is a genuine stratum, and `Check_ball_m2`'s obstruction rather than emptiness is what
kills the false-bit production there. -/
theorem sliver_third_stratum_real :
    ¬ QMCLeafB.ThriceM3.BodyEmpty G₁ t₁ P₁ ∧ ¬ BallFree G₁ t₁ P₁ ∧
      ¬ QMCLeafB.ThriceM3.PinchFeasible G₁ t₁ P₁ :=
  ⟨QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge, not_ballFree_sliver,
    QMCLeafB.ThriceM3.not_pinchFeasible_G₁⟩

#print axioms QMCLeafB.ZipM7.sliver_third_stratum_real

/-- **The residual's read-out slot is satisfiable at the sliver.**  Take the all-`ok` stream and
record the un-pinched member `EmptyBodyM5.Q₁` (unit diagonal) as the centre: the member side is
`sliver_unpinched_member`, and the bit side is the hypothesis `hb` — which is exactly the program's
design decision.  This is the constructive counterpart of `not_residParts_of_pinched`: the data slot
of `PartsData` has a solution at the sliver using a **unit-diagonal** centre, not the pinched one, so
nothing but the ok test stands between the residual and the third stratum. -/
theorem partsData_at_sliver
    (hb : QMCLeafB.Audit2M5.campaignBit G₁ t₁ =
      QMCLeafB.SimLoop.anyOk (fun _ => true) (P₁.K * P₁.m)) :
    ∃ (rb : ℕ → Bool) (cXp : ℕ → Matrix (Fin 2) (Fin 2) ℚ),
      QMCLeafB.Audit2M5.campaignBit G₁ t₁ =
          QMCLeafB.SimLoop.anyOk rb (P₁.K * P₁.m) ∧
        (∀ (k : ℕ), rb k = true →
          QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) (cXp k)
            (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) :=
  ⟨fun _ => true, fun _ => QMCLeafB.EmptyBodyM5.Q₁, hb, fun _ _ => sliver_unpinched_member.1⟩

#print axioms QMCLeafB.ZipM7.partsData_at_sliver

/-! ## 6.  The three anchors, at the zipped interface

* `(G₀, −99999/100000)` — empty body: `TripleSupply`'s stratum 1, discharged outright;
* `(G₀, −1/2)` — true bit: the ok-production anchor;
* `(G₁, t₁)` — nonempty, **ball-bearing**, no pinched member: outside `ThinThird` by
  `not_ballFree_sliver`, and any `TripleSupply` producer is forced `true` there and `false` at a
  pinched stream. -/

theorem anchor_bodyEmpty_G₀ :
    QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.ThriceM3.bodyEmpty_G₀

#print axioms QMCLeafB.ZipM7.anchor_bodyEmpty_G₀

theorem anchor_trueBit_G₀_half :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.ThriceM3.trueBitCore_fires_at_G₀_half

#print axioms QMCLeafB.ZipM7.anchor_trueBit_G₀_half

theorem anchor_not_pinchFeasible_G₁ :
    ¬ QMCLeafB.ThriceM3.PinchFeasible QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) :=
  QMCLeafB.ThriceM3.not_pinchFeasible_G₁

#print axioms QMCLeafB.ZipM7.anchor_not_pinchFeasible_G₁

theorem anchor_sliver_bodyNonempty :
    ¬ QMCLeafB.ThriceM3.BodyEmpty QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) :=
  QMCLeafB.HemptyR_M3.not_bodyEmpty_G₁_via_bridge

#print axioms QMCLeafB.ZipM7.anchor_sliver_bodyNonempty

end QMCLeafB.ZipM7


