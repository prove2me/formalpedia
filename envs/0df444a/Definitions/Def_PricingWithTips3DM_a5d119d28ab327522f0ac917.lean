-- Prove2me | Definitions.Def_PricingWithTips3DM_a5d119d28ab327522f0ac917
-- name    : PricingWithTips3DM_a5d119d28ab327522f0ac917
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:38:01.176992+00:00
-- url     : https://prove2.me/theorems/6ec311a5-b901-42a8-b89a-c505c56ea000
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanCellFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3230e773e85f1714115ecdbd
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input compiler for compact stack-cell spans

This is the cell-row counterpart of the compact height compiler.  A fixed
affine segment source and fixed prefix-drop controller emit one marked,
flattened cell block for every verifier transition seed in polynomial time.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Generated marked flattened cell rows for one verifier-fixed compact span.
-/
noncomputable def verifierTransitionStackAffineSpanCellFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm))
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (transitionStackAffineSpanCellDropAmounts W.machine.tm k span)
    (transitionStackAffineSpanCellDropAmounts_nonempty W.machine.tm k span)
    (verifierTransitionAffineSegmentRowFrames W
      (transitionStackAffineSpanCellSegments W.machine.tm k span) input)

/-- Exact fixed-group semantics of the generated cell-row compiler. -/
theorem verifierTransitionStackAffineSpanCellFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm))
    (input : List Γ) :
    verifierTransitionStackAffineSpanCellFrames W k span input =
      encodeUnaryFrameFixedGroupPrefixDropOutput
        (transitionStackAffineSpanCellDropAmounts W.machine.tm k span)
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionAffineSegmentValueRows seed
            (transitionStackAffineSpanCellSegments W.machine.tm k span)) := by
  unfold verifierTransitionStackAffineSpanCellFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  apply rewriteUnaryFrameFixedGroupPrefixDrop_groups
  intro group hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  unfold transitionAffineSegmentValueRows
  rw [List.length_map]
  exact (transitionStackAffineSpanCellDropAmounts_length W.machine.tm k
    span).symm

/-- One fixed polynomial-time TM2 compiles all marked flattened cell rows
directly from the original verifier input. -/
noncomputable def
    verifierTransitionStackAffineSpanCellFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (span : TransitionRouteSpan (List AffineUnaryTripleForm)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackAffineSpanCellFrames W k span) := by
  let source := verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    (transitionStackAffineSpanCellSegments W.machine.tm k span)
  let rewritten :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (transitionStackAffineSpanCellDropAmounts W.machine.tm k span)
        (transitionStackAffineSpanCellDropAmounts_nonempty W.machine.tm k span))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (transitionStackAffineSpanCellDropAmounts W.machine.tm k span)
      (transitionStackAffineSpanCellDropAmounts_nonempty W.machine.tm k span)
      (verifierTransitionAffineSegmentRowFrames W
        (transitionStackAffineSpanCellSegments W.machine.tm k span) input))
  simpa [Function.comp_def] using Classical.choice rewritten

/-- For an actual terminal row, the raw-input compiler emits exactly the
flattened cell component of the complete normalized affine route. -/
theorem TransitionStmtTerminalRowLayout.verifierStackAffineSpanCellFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (label : W.machine.tm.Λ)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout)
    (k : W.machine.tm.K) :
    verifierTransitionStackAffineSpanCellFrames W k
        (layout.stackAffineSpanRoute W.machine.tm k labelOffset).cellSpan input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (((layout.stackAffineSpanRoute W.machine.tm k labelOffset).eval
              seed (transitionStackRouteSourceBlock W.machine.tm seed k)
              ).cellRows.flatten) ++ [.frameEnd] := by
  rw [verifierTransitionStackAffineSpanCellFrames_eq]
  unfold encodeUnaryFrameFixedGroupPrefixDropOutput
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [layout.stackAffineSpanCellSegments_values W input seed hseed label
    labelOffset hlayout k]

end CLRS.Chapter34.Turing.CookLevin


