-- Prove2me | Definitions.Def_QMCLeafB_assembly_m5
-- name    : QMCLeafB_assembly_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:03:05.900611+00:00
-- url     : https://prove2.me/theorems/7d10b8fa-409f-4895-add7-b097a85060fe
-- title:
--   QMCLeafB assembly_m5
-- statement:
--   # leaf B phase 17 — the one-stroke ending (swarm `smw1gfajf`, member m5, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_solution_lock_m7
import Definitions.Def_QMCLeafB_initdq_m1
/-
# leaf B phase 17 — the one-stroke ending (swarm `smw1gfajf`, member m5, direction d4)

The campaign stands at ONE hypothesis, `hd`: one `FinalStroke.RunParts` bundle per interior
`(G, t)`, at the **shelf round** `RoundProgram.round`, the campaign parameter family
`UnionShallow.paramsKbc2 G` and the campaign initial state `InitDq.init0`.  This file makes the last
step of the leaf a *single application*: everything else in
`QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round` is discharged here, from the frozen
shelf, and the conclusion is written out in the verbatim `d9f601e5` sentence.

What is discharged here (all of it already on the shelf, so this file proves nothing new
mathematically — it is the wiring, checked):

* `init := QMCLeafB.InitDq.init0`, tape exponent `k = 20`;
* `hinit : Automatic.Poly init0`                — `InitDq.poly_init0`
* `hnorm : |stX| = stN · stN`                   — `InitDq.init_normalised`
* `hstT  : stT (init0 p) = p.2`                 — `InitDq.stT_init0`
* `hinitTape : init0 p = init0 (noTape …)`      — `InitDq.init0_tape`
* `hfv   : fvR (init0 p) = 0`                   — `InitDq.fvR_init0` + tape-freeness (§1)
* `hmass : epsOf (init0 p) = Rq G / 40000`      — `HtopFinish.epsOf_init0` + `stA` agreement (§1)

Two additional services for the `hd` producer:

* §2 `Rq_pos_of_interior_bracket`: the interior bracket itself forces `0 < Rq G`.  Every producer of
  `hd` needs this, because the campaign family's rounding budget (`paramsKbc2_budget`) is a
  statement about the *positive* regime — at `Rq = 0` the bracket is simply empty.
* §3 `HdPropPos`: the same residual with `0 < Rq G` made an explicit hypothesis, i.e. the shape
  `RunPartsStream.runParts_of_stream_data` wants at `P := paramsKbc2 G`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`.  `set_option autoImplicit false`;
axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open QuantumMaxCutEnergy

local instance instRequestCodingAssembly : OAI.MetricKMedian.Binary.Automatic.Coding
    (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

namespace QMCLeafB.AssemblyM5

/-! ## 1.  The two init readings that are not one-liners on the shelf -/

/-- `InitDq.init0` and `RStInit.init0` pack the *same* weight code (the tolerance `dq` enters only
through `stX`, via `Boundary.initShapeOf _ M`). -/
theorem stA_init0_eq (p : QMCLeafB.FuelWire.Pkg) :
    QMCLeafB.RoundProgram.stA (QMCLeafB.InitDq.init0 p)
      = QMCLeafB.RoundProgram.stA (QMCLeafB.RStInit.init0 p) := rfl

/-- **The `hfv` slot at `InitDq.init0`**: `fvR` vanishes at the campaign initial state on *any*
tape, since the state is tape-free and `fvR_init0` holds on the tape-free representative. -/
theorem fvR_init0_any (p : QMCLeafB.FuelWire.Pkg) :
    QMCLeafB.RoundProgram.fvR (QMCLeafB.InitDq.init0 p) = 0 := by
  rw [QMCLeafB.InitDq.init0_tape p]
  exact QMCLeafB.InitDq.fvR_init0 p.1.1 p.2

/-- **The `hmass` slot at `InitDq.init0`**: the state's slack is `Rq G / 40000`.  `epsOf` reads the
weight code only (`HtopFinish.epsOf_congr`), and the campaign state's weight code is `RStInit.init0`'s. -/
theorem epsOf_init0_any (p : QMCLeafB.FuelWire.Pkg) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.InitDq.init0 p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 :=
  (QMCLeafB.HtopFinish.epsOf_congr (s := QMCLeafB.InitDq.init0 p)
    (s' := QMCLeafB.RStInit.init0 p) (stA_init0_eq p)).trans
    (QMCLeafB.HtopFinish.epsOf_init0 p)

/-- The tape exponent used by the ending: `20 ≤ 2^20`, so `k := 20` carries the fuel slot. -/
theorem hk_twenty : 20 ≤ 2 ^ 20 := by norm_num

/-! ## 2.  The interior bracket forces `Rq > 0`

`RunParams.hbudget` at the campaign family is `paramsKbc2_budget`, whose hypothesis is `0 < Rq G`
(`RundataParams.dqShallow_budget` is a statement about the *positive* regime).  The bracket
`-Rq ≤ t < -Rq/40000` cannot be inhabited with `Rq ≤ 0`: from `-Rq ≤ t < -Rq/40000` one gets
`Rq·(1 − 1/40000) > 0`, hence `Rq > 0`.  So no producer of `hd` ever faces the degenerate case, and
this lemma is what turns the bracket into the hypothesis the budget wants. -/
theorem Rq_pos_of_interior_bracket (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    0 < QMCLeafB.EngineRuntime.Rq G := by
  have h1 : ((-QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    have h2 : ((-QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hlo
    linarith
  have h3 : (-QMCLeafB.EngineRuntime.Rq G : ℚ) < -(QMCLeafB.EngineRuntime.Rq G / 40000) := by
    exact_mod_cast h1
  linarith

/-- The degenerate half: at `Rq G ≤ 0` there is no interior `t` at all — `hd` is vacuous there. -/
theorem interior_bracket_empty_of_Rq_nonpos (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hRq : QMCLeafB.EngineRuntime.Rq G ≤ 0)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) : False :=
  absurd (Rq_pos_of_interior_bracket G t hlo hhi) (not_lt.mpr hRq)

/-- Conversely: inside the bracket, the *positive* rounding budget of the campaign family holds.
This is the `hbudP` hypothesis of `RunPartsStream.runParts_of_stream_data` at `P := paramsKbc2 G`,
available for free at every `(G, t)` where `hd` is asked. -/
theorem budget_at_interior (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
      + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G :=
  QMCLeafB.UnionShallow.paramsKbc2_budget G hn (Rq_pos_of_interior_bracket G t hlo hhi)

/-- The ceiling is positive at the bracket — the other scalar input of the stream producer. -/
theorem rmax_pos_at_interior (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    0 < (QMCLeafB.UnionShallow.paramsKbc2 G).rmax :=
  QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn

/-- The ceiling is at most `1` as well (`rmaxOf (n·n) = 1/(4·n²)`). -/
theorem rmax_le_one (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).rmax ≤ 1 := by
  have hN : 1 ≤ G.n * G.n := by nlinarith
  have h : (QMCLeafB.UnionShallow.paramsKbc2 G).rmax
      = QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := rfl
  rw [h, QMCLeafB.RundataHalving.rmaxOf, div_le_one (by positivity)]
  have hq : (1 : ℚ) ≤ ((G.n * G.n : ℕ) : ℚ) := by exact_mod_cast hN
  linarith

/-! ## 3.  The residual, stated once

`HdProp` is the leaf's entire remaining content: one `RunParts` bundle per interior `(G, t)`, at the
shelf round, the shelf verdict, the campaign family and the campaign state.  `HdPropPos` is the same
with the bracket's `0 < Rq G` exposed. -/

/-- The tape-free round count of the campaign ending: `Kbc2 (mHalve (n·n)) G · mHalve (n·n)`. -/
noncomputable def Tbc2 (G : QuantumMaxCutEnergy.Input) (_t : ℚ) : ℕ :=
  QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
    * QMCLeafB.HalvePerG.mHalve (G.n * G.n)

/-- The loop whose output bit is the leaf's `L`-decider, at the campaign state and count. -/
noncomputable def loopCampaign : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
    QMCLeafB.RoundProgram.verdict Tbc2

/-- **The one remaining hypothesis of the leaf.**  (Sort `Type`, not `Prop`: `RunParts` is a
structure in `Type`, so the `∀`-closure is a type of data, not a proposition.) -/
abbrev HdProp : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    QMCLeafB.FinalStroke.RunParts
      (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.UnionShallow.Kbc2
          (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
          * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
      (QMCLeafB.UnionShallow.paramsKbc2 G)

/-- `HdProp` with the bracket's positivity exposed.  Inter-derivable with `HdProp` (§3). -/
abbrev HdPropPos : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    0 < QMCLeafB.EngineRuntime.Rq G →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    QMCLeafB.FinalStroke.RunParts
      (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => QMCLeafB.UnionShallow.Kbc2
          (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
          * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))) G t
      (QMCLeafB.UnionShallow.paramsKbc2 G)

/-- The positive-bracket spelling is the weaker one: it drops a hypothesis and is therefore
stronger as a supply.  Both directions, so a producer may land on either. -/
def HdProp_of_HdPropPos (h : HdPropPos) : HdProp :=
  fun G t hn hlo hhi => h G t hn (Rq_pos_of_interior_bracket G t hlo hhi) hlo hhi

def HdPropPos_of_HdProp (h : HdProp) : HdPropPos :=
  fun G t hn _ hlo hhi => h G t hn hlo hhi

/-! ## 4.  The one-stroke ending

`QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round` at `init := InitDq.init0`, with every
init slot discharged above and `k = 20`.  The conclusion is written out in the **verbatim**
`d9f601e5` sentence, so the coordinator's last node is `endgame_of_hd hd` — one application. -/

/-- **`d9f601e5` from `hd` alone.** -/
theorem endgame_of_hd (hd : HdProp) :
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
  QMCLeafB.RoundGUEndgame.solution_roundGU_of_init_hd_round
    QMCLeafB.InitDq.init0 20 hk_twenty QMCLeafB.InitDq.poly_init0
    QMCLeafB.InitDq.init_normalised fvR_init0_any QMCLeafB.InitDq.stT_init0
    epsOf_init0_any QMCLeafB.InitDq.init0_tape hd

/-- The same ending at the shelf's own name for the sentence. -/
theorem endgame_of_hd_statement (hd : HdProp) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_hd hd

/-- **The ending from the positive-bracket spelling** — the form a stream producer lands on. -/
theorem endgame_of_hd_pos (hd : HdPropPos) :
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
  endgame_of_hd (HdProp_of_HdPropPos hd)

/-- **Cross-check against the campaign's documented final node.**  `solution_of_hd`
(`Check_htop_solution_lock_m7`) is the same ending with `init` still abstract; at
`init := InitDq.init0` it consumes exactly `HdProp`, so the two files agree and the coordinator may
use either.  (This is the check that the `hd` type pinned here is the campaign's residual and not a
lookalike.) -/
theorem endgame_of_hd_via_campaign_node (hd : HdProp) :
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
  solution_of_hd QMCLeafB.InitDq.init0 20 hk_twenty QMCLeafB.InitDq.poly_init0
    QMCLeafB.InitDq.init_normalised fvR_init0_any QMCLeafB.InitDq.stT_init0
    epsOf_init0_any QMCLeafB.InitDq.init0_tape hd

/-! ## 5.  Consistency check on the residual

`hd` is not a hypothesis about the degenerate regime: below the campaign slack, the interior bracket
is inhabited only when `Rq G > 0`, and there the family's own scalar inputs (`0 < rmax ≤ 1`, `hbudP`)
are already theorems (`rmax_pos_at_interior`, `rmax_le_one`, `budget_at_interior`).  So the residual
is exactly `RunPartsStream.runParts_of_stream_data`'s stream data on `{G | 2 ≤ G.n, 0 < Rq G}`. -/

/-- An inhabited bracket forces `Rq G > 0`. -/
theorem Rq_pos_of_bracket_inhabited (G : QuantumMaxCutEnergy.Input)
    (h : ∃ t' : ℚ, -QMCLeafB.EngineRuntime.Rq G ≤ t'
        ∧ (t' : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    0 < QMCLeafB.EngineRuntime.Rq G := by
  obtain ⟨t', hlo, hhi⟩ := h
  exact Rq_pos_of_interior_bracket G t' hlo hhi

end QMCLeafB.AssemblyM5

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.AssemblyM5.stA_init0_eq
#print axioms QMCLeafB.AssemblyM5.fvR_init0_any
#print axioms QMCLeafB.AssemblyM5.epsOf_init0_any
#print axioms QMCLeafB.AssemblyM5.hk_twenty
#print axioms QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket
#print axioms QMCLeafB.AssemblyM5.interior_bracket_empty_of_Rq_nonpos
#print axioms QMCLeafB.AssemblyM5.budget_at_interior
#print axioms QMCLeafB.AssemblyM5.rmax_pos_at_interior
#print axioms QMCLeafB.AssemblyM5.rmax_le_one
#print axioms QMCLeafB.AssemblyM5.HdProp_of_HdPropPos
#print axioms QMCLeafB.AssemblyM5.HdPropPos_of_HdProp
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd_statement
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd_pos
#print axioms QMCLeafB.AssemblyM5.endgame_of_hd_via_campaign_node
#print axioms QMCLeafB.AssemblyM5.Rq_pos_of_bracket_inhabited


