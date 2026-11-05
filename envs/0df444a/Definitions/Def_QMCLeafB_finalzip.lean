-- Prove2me | Definitions.Def_QMCLeafB_finalzip
-- name    : QMCLeafB_finalzip
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:17:31.334992+00:00
-- url     : https://prove2.me/theorems/59147cea-bfb5-47d1-990f-061d5e1c42d5
-- title:
--   QMCLeafB finalzip
-- statement:
--   # Leaf B phase 24 — m7, direction `final-zip`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_parts_m2
import Definitions.Def_QMCLeafB_hemptyR
/-
# Leaf B phase 24 — m7, direction `final-zip`

**The deliverable, assembled at the sharpest residual.**  Phase 23 left the leaf at

    ResidParts campaignBit paramsKbc2        (QMCLeafB.PartsM2, `Check_parts_m2`)

i.e. one `FinalStroke.RunParts` bundle per interior `(G,t)` whose *real* relaxed body is nonempty,
at the campaign bit.  The empty stratum, the `hemptyR` bridge, the campaign's `hd`-stroke and the
verbatim ending are all on the shelf.  This file is the composition and nothing else:

* §1 **statement lock**: the inlined type used throughout is `FinishLine.SolutionStatement` by
  `rfl` (and `SolutionStatement` is the platform's `d9f601e5` body token for token);
* §2 **`ResidParts` ⟺ `AssemblyM5.HdProp`** — the residual is the campaign's own `hd` in disguise
  (`residParts_of_hdProp` one way; `hdProp_of_parts` the other, already banked).  So the
  composition below consumes exactly the object phase 23 named, not a lookalike;
* §3 **the campaign data** (`rb`, `cXp`, `hbit`, `hok`) as one structure, field types copied
  verbatim from `PartsM2.hdProp_of_campaign_parts` — this is what direction d5 owes;
* §4 **`hemptyR` discharged**, not assumed: `Check_hemptyR_m3.hemptyR_campaign` (proved
  unconditionally, general rational→real cast bridge) replaces the fifth plug;
* §5 **the zip**: `ResidParts`-producer + campaign data ⇒ `HdProp` ⇒ `endgame_of_hd` ⇒ the
  verbatim `d9f601e5` sentence.  Two forms: `solution_statement_of_parts` (at
  `FinishLine.SolutionStatement`) and `solution_of_parts` (the sentence written out);
* §6 **the bit-split refinement**: `ResidParts` from a `true`-bit `RunParts` supply plus
  `ThriceM3.ThirdStratum` (the `false`-bit nonempty-body stratum), so d2 (sliver) and d4
  (true-bit) plug in independently, each at its own stratum;
* §7 axiom audit.

No new geometry, no new arithmetic.  Discipline: `set_option autoImplicit false`; no
`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.FinalZipM7

open QuantumMaxCutEnergy

/-- The request coding the leaf's `TM2` statement is elaborated at (as in
`Check_brick_finish_line` / `Check_assembly_m5`). -/
local instance instRequestCodingZip : OAI.MetricKMedian.Binary.Automatic.Coding
    (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  Statement lock

`FinishLine.SolutionStatement` is `d9f601e5`'s sentence verbatim (`Check_brick_finish_line.lean`,
generated from the platform's own `formal_statement`).  This `rfl` is the machine check that the
type spelled out below — the type of every stroke in this file — is that sentence. -/

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

#print axioms QMCLeafB.FinalZipM7.statement_lock

/-! ## 2.  The residual is the campaign's `hd`

`AssemblyM5.HdProp` demands a `RunParts` at *every* interior point, at the loop bit of
`InitDq.init0`/`RoundProgram.round` with count `Tbc2`.  `Audit2M5.campaignBit` abbreviates that
same loop bit, so `HdProp ⇒ ResidParts` is `fun G t hn hlo hhi _ => …`: the residual phase 23
named is the campaign's whole content with the body hypothesis *added*, hence weaker as a demand
and the honest resting point.  (The converse is `PartsM2.hdProp_of_parts`, banked.) -/

/-- **`HdProp` gives the phase-23 residual** (drop the body hypothesis; same bit by definition). -/
def residParts_of_hdProp (h : QMCLeafB.AssemblyM5.HdProp) :
    QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2 :=
  fun G t hn hlo hhi _ => h G t hn hlo hhi

#print axioms QMCLeafB.FinalZipM7.residParts_of_hdProp

/-! ## 3.  The campaign data (direction d5's plug set)

Field types verbatim from `PartsM2.hdProp_of_campaign_parts` (`Check_parts_m2.lean`).  `rb`/`cXp`
are the run's own `ok`-read-out and its pinched centre stream; `hbit` is the program-bit equation
(`VerdictBridge.hverdict_at_roundW`'s shape, `Check_roundwrepoint_m4.hverdict_at_roundW0`); `hok`
is `ok ⇒ RelaxMem` at the pinched frozen centre (`VerdictBridge.flag_true_of_okV` + the freeze). -/

structure PartsData where
  /-- the run's `ok` stream -/
  rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool
  /-- its (pinched) centre stream -/
  cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the program bit is `anyOk` of that stream over the window `K·m` -/
  hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
    QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m)
  /-- an `ok` round hands a rational member certificate -/
  hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq

/-- **A consequence of the campaign data that every producer must meet.**  A `true` program bit at
`(G,t)` forces the *rational* relaxed body at the record's level `t − eps G` to be nonempty: the
read-out (`hbit`) hands an `ok` index below the horizon, and `hok` turns it into a member.  Nothing
else in `RunParts` reads `rb`/`cXp`, so this is the whole price of the data plug — and it is exactly
the condition the empty stratum must fail (there `hemptyR` forbids any member). -/
theorem exists_member_of_bit_true (D : PartsData) (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hbit : QMCLeafB.Audit2M5.campaignBit G t = true) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq := by
  have h1 : QMCLeafB.SimLoop.anyOk (D.rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m) = true := by
    rw [← D.hbit G t]
    exact hbit
  obtain ⟨k, _hk, hokk⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff (D.rb G t)
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m)).1 h1
  exact ⟨D.cXp G t k, D.hok G t k hokk⟩

#print axioms QMCLeafB.FinalZipM7.exists_member_of_bit_true

/-! ## 4.  `hemptyR`, discharged

`Check_hemptyR_m3` proves the rational→real bridge in general form
(`HemptyR_M3.relaxBodyLE_of_relaxMem`: `RelaxMem A Q u δ → relaxBodyLE (castMat A) ↑u ↑δ (castMat Q)`)
and hence the campaign's `hemptyR` unconditionally.  `ThriceM3.BodyEmpty` is the very hypothesis
`ResidParts` carries, so the fifth plug of the banked stroke is *deleted* here, not assumed. -/

/-- The campaign's `hemptyR`, in the exact shape `PartsM2.hdProp_of_campaign_parts` asks for. -/
theorem hemptyR_parts :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq :=
  fun G t hbody => QMCLeafB.HemptyR_M3.hemptyR_campaign G t hbody

#print axioms QMCLeafB.FinalZipM7.hemptyR_parts

/-- **The campaign data is FREE at a `false`-bit point** (same one-liner as at `oW`): the sliver
class therefore owes `ResidParts` and nothing else. -/
theorem partsData_pointwise_of_falseBit (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hbit : QMCLeafB.Audit2M5.campaignBit G t = false) :
    ∃ (rb : ℕ → Bool) (cXp : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk rb
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m) ∧
      (∀ (k : ℕ), rb k = true →
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp k)
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq) :=
  ⟨fun _ => false, fun _ => 0,
    by
      rw [hbit]
      exact (QMCLeafB.ResidRefute.anyOk_all_false (fun _ => false)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m) (fun _ _ => rfl)).symm,
    by intro k hk; simp at hk⟩

#print axioms QMCLeafB.FinalZipM7.partsData_pointwise_of_falseBit

/-! ## 5.  THE ZIP

`PartsM2.hdProp_of_campaign_parts` (banked, `Check_parts_m2`) with its `hemptyR` plug supplied by
§4, then the banked verbatim ending `AssemblyM5.endgame_of_hd`.  The only open object is the
`ResidParts` argument. -/

/-- `AssemblyM5.HdProp` from the campaign data and the phase-23 residual — `hemptyR` discharged. -/
def hdProp_of_data (D : PartsData)
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  QMCLeafB.PartsM2.hdProp_of_campaign_parts D.rb D.cXp D.hbit D.hok hemptyR_parts H

#print axioms QMCLeafB.FinalZipM7.hdProp_of_data

/-- **The leaf at the shelf's own sentence.**  Campaign data + `ResidParts` ⇒
`FinishLine.SolutionStatement`. -/
theorem solution_statement_of_parts (D : PartsData)
    (H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hdProp_of_data D H)

#print axioms QMCLeafB.FinalZipM7.solution_statement_of_parts

/-- **`d9f601e5`, verbatim**, from the campaign data and the phase-23 residual.  This is the
coordinator's last node: fix a `PartsData` and a `ResidParts` producer, and the theorem is one
application. -/
theorem solution_of_parts (D : PartsData)
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hdProp_of_data D H)

#print axioms QMCLeafB.FinalZipM7.solution_of_parts

/-! ## 6.  The bit-split refinement

d2 (sliver) and d4 (true-bit) produce at different strata.  `ResidParts` demands `RunParts` at
every nonempty-body point regardless of the bit, so it splits by `by_cases` on the bit: a
`true`-bit supply (`TrueBitStratum`) and `ThriceM3.ThirdStratum` (the `false`-bit nonempty-body
stratum, verbatim `Check_thrice_m3`'s named residual) together give it.  Neither half can be
skipped: the sliver class is `false`-bit and nonempty-body. -/

/-- `RunParts` at the `true`-bit nonempty-body points. -/
abbrev TrueBitStratum (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true →
    QMCLeafB.FinalStroke.RunParts o G t (Pfam G)

/-- **`ResidParts` from the two bit strata.**  The `false`-bit half is `ThirdStratum` (which also
carries the nonempty-body hypothesis), the `true`-bit half is the supply. -/
def residParts_of_bit_split (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hT : TrueBitStratum o Pfam) (hF : QMCLeafB.ThriceM3.ThirdStratum o Pfam) :
    QMCLeafB.PartsM2.ResidParts o Pfam :=
  fun G t hn hlo hhi hne =>
    if hbit : o G t = true then hT G t hn hlo hhi hbit
    else
      hF G t hn hlo hhi
        (fun hbe => by
          obtain ⟨X, hX⟩ := hne
          exact hbe X hX)
        (by
          cases hb : o G t with
          | false => rfl
          | true => exact absurd hb hbit)

#print axioms QMCLeafB.FinalZipM7.residParts_of_bit_split

/-- **The leaf from the two bit strata**: campaign data, a `true`-bit supply and the
`false`-bit nonempty-body stratum. -/
theorem solution_of_bit_split (D : PartsData)
    (hT : TrueBitStratum QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2)
    (hF : QMCLeafB.ThriceM3.ThirdStratum QMCLeafB.Audit2M5.campaignBit
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
  solution_of_parts D
    (residParts_of_bit_split QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2 hT hF)

#print axioms QMCLeafB.FinalZipM7.solution_of_bit_split

end QMCLeafB.FinalZipM7

/-! ## 7.  The final line (to uncomment when a `PartsData` and a `ResidParts` producer exist)

```
theorem solution :
<the inlined type of `QMCLeafB.FinalZipM7.solution_of_parts`> :=
  QMCLeafB.FinalZipM7.solution_of_parts campaignData residPartsProducer
```

The platform requires a **top-level** `theorem solution`, so this must sit outside any namespace.
`PartsData.CampaignData` has no inhabitant on the shelf yet (direction d5's `hbit`/`hok` need the
round-`W` run read-outs); `ResidParts` is the phase-23 residual itself.
-/


