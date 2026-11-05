-- Prove2me | Definitions.Def_QMCLeafB_residrunparts
-- name    : QMCLeafB_residrunparts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:24:24.605529+00:00
-- url     : https://prove2.me/theorems/a991ffcc-7c38-48e6-b2e8-71a5d8085cf4
-- title:
--   QMCLeafB residrunparts
-- statement:
--   # `Check_residrunparts_m3` — the weakest residual shape: `RunParts` on the nonempty stratum
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_hemptyR
/-
# `Check_residrunparts_m3` — the weakest residual shape: `RunParts` on the nonempty stratum

`Check_audit2_m5` §6 draws the right conclusion but does not implement it: *the endgame residual
must be stated at `RunParts`/`RunData`, not at `CoreDataG`*.  This file implements exactly that, on
top of `Check_hemptyR_m3`'s bridge (so the empty stratum is discharged with no `hemptyR`
hypothesis):

    ResidRunParts o Pfam := ∀ (G,t) interior, ¬ BodyEmpty G t (Pfam G) → RunParts o G t (Pfam G)

One hypothesis, at the leaf's own interface, off the settled empty stratum.  It is the **weakest**
of the three shapes on the board, in the strict sense:

* `ResidSplit ⇒ ResidRunParts` (`residRunParts_of_split`) — via the conduit and the locked
  `runParts_of_bundleH` stroke;
* `TripleSupply ⇒ ResidRunParts` given the campaign's read-out data and the empty-stratum bit
  (`residRunParts_of_triple`, on top of `Check_thrice_m3.runParts_of_triple`);
* `ResidRunParts ⇒ HdProp ⇒ SolutionStatement` (`hdProp_of_residRunParts`,
  `solution_statement_of_residRunParts`) and the verbatim d9f601e5 `solution_of_residRunParts`,
  which needs only the campaign data `rb`, `cXp`, `hbit`, `hokp` — **no `hdia`, no `hemptyR`,
  no `ResidSplit`, no `CoreDataG`.**

So whatever a production lane delivers — a `dM = −1` re-derivation, a genuine-separation stream, a
frozen-member certificate — it can be submitted at this shape, and the zip needs nothing else.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ResidRunParts_M3

open QuantumMaxCutEnergy

/-- **The residual, at the leaf's own interface**: the run record at every interior point whose
real relaxed body is nonempty.  The empty stratum is settled (`Check_emptyC_m3`,
`Check_refuted_m3`), so this is the whole remaining content of `hd`. -/
abbrev ResidRunParts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ QMCLeafB.ThriceM3.BodyEmpty G t (Pfam G) →
    QMCLeafB.FinalStroke.RunParts o G t (Pfam G)

/-- **`ResidSplit ⇒ ResidRunParts`**: the audit's conduit shape feeds the weakest shape. -/
noncomputable def residRunParts_of_split {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.Audit2M5.ResidSplit o QMCLeafB.UnionShallow.paramsKbc2) :
    ResidRunParts o QMCLeafB.UnionShallow.paramsKbc2 :=
  fun G t hn hlo hhi hbody =>
    QMCLeafB.ThriceM3.runParts_of_coreDataG hlo hhi (H G t hn hlo hhi hbody)

#print axioms QMCLeafB.ResidRunParts_M3.residRunParts_of_split

/-- **`TripleSupply ⇒ ResidRunParts`** given the campaign's own read-out data: the empty stratum is
discharged by the bridge, the `true`-bit strand by the frozen member, the third stratum by `H`. -/
noncomputable def residRunParts_of_triple
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (H : QMCLeafB.ThriceM3.TripleSupply QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    ResidRunParts QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2 :=
  fun G t hn hlo hhi _ =>
    QMCLeafB.ThriceM3.runParts_of_triple rb cXp hbit hokp hdia
      (fun G' t' hb => QMCLeafB.HemptyR_M3.hemptyR_campaign G' t' hb) H G t hn hlo hhi

#print axioms QMCLeafB.ResidRunParts_M3.residRunParts_of_triple

/-- **`ResidRunParts` gives `HdProp`** — the campaign's whole `hd`, with the empty stratum
discharged by the bridge and the empty-stratum bit by the program's read-out. -/
noncomputable def hdProp_of_residRunParts
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidRunParts QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp := by
  intro G t hn hlo hhi
  by_cases hbody : QMCLeafB.ThriceM3.BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G)
  · have hf : QMCLeafB.Audit2M5.campaignBit G t = false :=
      QMCLeafB.ThriceM3.bit_false_of_bodyEmpty (hbit G t) (hokp G t)
        (QMCLeafB.HemptyR_M3.hemptyR_campaign G t) hbody
    exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn hf hbody
  · exact H G t hn hlo hhi hbody

#print axioms QMCLeafB.ResidRunParts_M3.hdProp_of_residRunParts

/-- **`SolutionStatement` from the weakest residual.** -/
theorem solution_statement_of_residRunParts
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidRunParts QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement
    (hdProp_of_residRunParts rb cXp hbit hokp H)

#print axioms QMCLeafB.ResidRunParts_M3.solution_statement_of_residRunParts

/-- **The verbatim `d9f601e5` sentence from `ResidRunParts`** — the closing stroke with the fewest
hypotheses on the board: campaign read-out (`rb`, `cXp`, `hbit`, `hokp`) and one `RunParts`
production off the empty stratum. -/
theorem solution_of_residRunParts
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidRunParts QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
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
  QMCLeafB.AssemblyM5.endgame_of_hd
    (hdProp_of_residRunParts rb cXp hbit hokp H)

#print axioms QMCLeafB.ResidRunParts_M3.solution_of_residRunParts

end QMCLeafB.ResidRunParts_M3


