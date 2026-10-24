-- Prove2me | Definitions.Def_PricingWithTips3DM_85ee3faad979da50ac66d6e2
-- name    : PricingWithTips3DM_85ee3faad979da50ac66d6e2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:41:52.104999+00:00
-- url     : https://prove2.me/theorems/23518501-f1d6-43b7-8ba2-c82e43a1616c
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchSeed
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bf5f0a221840f4cf1d613e10
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Seed-complete transition dispatch artifacts

The label dispatch is reconstructed here without any proof-carrying builders.
Each artifact contains the complete recursive statement script and the full
whole-row mux operand frames; the accumulated fallback is the arithmetic mux
output row from the preceding label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Builder-free artifact recursion for an arbitrary suffix of fixed program
labels.  The source row is unchanged across labels, while `fallback` advances
to each preceding arithmetic mux output row. -/
def transitionDispatchLabelArtifacts (tm : _root_.Turing.FinTM2)
    (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    (start : Nat) → CfgWires tm (workHeight tm height) → List tm.Λ →
      List (TransitionDispatchLabelArtifact tm)
  | _, _, [] => []
  | start, fallback, label :: labels =>
      let statement := transitionStmtScript tm (workHeight tm height)
        falseWire trueWire start source (tm.m label)
        (stmtPushSet_program_subset tm label)
      let statementWires := transitionStmtOutputWires tm
        (workHeight tm height) falseWire trueWire start source (tm.m label)
        (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      let muxStart := start +
        compileStmtGateCost tm (workHeight tm height) (tm.m label)
      { label := label
        start := start
        statement := statement
        selector := selector
        muxFrames := affineMuxFinCanonicalFrames muxStart selector _
          (fun coordinate => statementWires
            ((cfgSlotEquivFin tm (workHeight tm height)).symm coordinate))
          (fun coordinate => fallback
            ((cfgSlotEquivFin tm (workHeight tm height)).symm coordinate)) } ::
        transitionDispatchLabelArtifacts tm height falseWire trueWire source
          (muxStart + (3 * cfgBitCount tm (workHeight tm height) + 1))
          (arithmeticMuxCfgWires tm (workHeight tm height) muxStart) labels

/-- The proof-carrying label recursion is exactly the builder-free artifact
recursion, including every nested statement operand and every mux arm. -/
theorem compileDispatchLabelsListArtifacts_eq_arithmetic
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm height))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    compileDispatchLabelsListArtifacts tm height base pool source fallback
        hsource hfallback labels =
      transitionDispatchLabelArtifacts tm height pool.falseWire pool.trueWire
        source base.gates.length fallback labels := by
  induction labels generalizing base fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListArtifacts,
        transitionDispatchLabelArtifacts]
      rw [compileStmtScript_eq_transitionStmtScript]
      congr 1
      · rw [compileStmt_gate_delta]
        rw [compileStmt_wires_eq_transitionStmtOutputWires]
      · rw [ih]
        rw [cfgMux_wires_eq_arithmetic]
        rw [cfgMux_gate_delta, compileStmt_gate_delta]
        simp only [CircuitBuilder.BoolWirePool.mono_falseWire,
          CircuitBuilder.BoolWirePool.mono_trueWire, Nat.add_assoc]

/-- Complete canonical-label artifact family decoded directly from one raw
transition-row seed. -/
def transitionDispatchArtifactsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (TransitionDispatchLabelArtifact tm) :=
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  transitionDispatchLabelArtifacts tm seed.height seed.start (seed.start + 1)
    source (seed.start + 2) source (programLabels tm)

/-- Actual widening plus complete proof-carrying dispatch artifacts are equal,
not merely projectionwise equal, to the raw-seed reconstruction. -/
theorem arithmeticWidening_dispatchArtifacts_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    let widened := widenCfg base (arithmeticCfgWires tm height rowBase) hvalid
    compileDispatchArtifacts tm height widened.builder widened.constants
        widened.wires widened.valid =
      transitionDispatchArtifactsFromSeed tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  dsimp only [compileDispatchArtifacts]
  rw [compileDispatchLabelsListArtifacts_eq_arithmetic]
  unfold transitionDispatchArtifactsFromSeed
  rw [widenCfg_falseWire_eq, widenCfg_trueWire_eq,
    widenCfg_arithmetic_wires_eq, widenCfg_gate_delta]

end CLRS.Chapter34.Turing.CookLevin


