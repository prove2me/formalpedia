-- Prove2me | Definitions.Def_PricingWithTips3DM_5a2dd8815216c377c022b769
-- name    : PricingWithTips3DM_5a2dd8815216c377c022b769
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:01:19.970995+00:00
-- url     : https://prove2.me/theorems/10b3cb87-55ce-42ab-8912-1c40d5bc9a73
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementFinalBranch
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bf5f0a221840f4cf1d613e10
import Definitions.Def_PricingWithTips3DM_3d06fdaba09255b5d609af60
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Final-branch output of a transition statement

A bundled TM2 statement is a linear sequence of stack/state updates until it
reaches `halt`, `goto`, or `branch`.  Whenever it reaches `branch`, the
complete output row is the final whole-row mux, so all earlier updates cease
to affect the output coordinates.  This module computes that mux offset as a
fixed affine function and proves the exact builder-free output equation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Affine gate offset of the final whole-row mux when the statement's linear
spine terminates in `branch`.  `none` means that the spine terminates in
`halt` or `goto` instead. -/
noncomputable def transitionStmtFinalBranchMuxOffsetAffine
    (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Option TransitionAffineNat
  | halt => none
  | goto _ => none
  | load _ continuation =>
      (transitionStmtFinalBranchMuxOffsetAffine tm continuation).map
        ((TransitionAffineNat.const
          (stateCount tm + stateCount tm)).add ·)
  | push k _ continuation =>
      (transitionStmtFinalBranchMuxOffsetAffine tm continuation).map
        ((TransitionAffineNat.const
          (stateCount tm + (reachableAlphabet tm k).card)).add ·)
  | peek k _ continuation =>
      (transitionStmtFinalBranchMuxOffsetAffine tm continuation).map
        ((TransitionAffineNat.const
          (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
            stateCount tm)).add ·)
  | pop k _ continuation =>
      (transitionStmtFinalBranchMuxOffsetAffine tm continuation).map
        ((TransitionAffineNat.const
          (1 + 2 * stateCount tm *
            ((reachableAlphabet tm k).card + 1) + stateCount tm)).add ·)
  | branch test whenTrue whenFalse =>
      some <|
        (TransitionAffineNat.const
          ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1)).add
        ((compileStmtGateAffine tm whenTrue).add
          (compileStmtGateAffine tm whenFalse))

/-- If the fixed statement spine ends in `branch`, its complete output is
exactly the arithmetic whole-row mux at the affine offset above. -/
theorem transitionStmtOutputWires_eq_finalBranchMux
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire start : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (offset : TransitionAffineNat)
    (hoffset : transitionStmtFinalBranchMuxOffsetAffine tm q = some offset) :
    transitionStmtOutputWires tm height falseWire trueWire start source q
        hsupport =
      arithmeticMuxCfgWires tm height (start + offset.eval height) := by
  induction q generalizing start source offset with
  | halt => simp [transitionStmtFinalBranchMuxOffsetAffine] at hoffset
  | goto jump => simp [transitionStmtFinalBranchMuxOffsetAffine] at hoffset
  | load update continuation ih =>
      have hsupportContinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtFinalBranchMuxOffsetAffine] at hoffset
      cases hcontinuation :
          transitionStmtFinalBranchMuxOffsetAffine tm continuation with
      | none => simp [hcontinuation] at hoffset
      | some continuationOffset =>
          rw [hcontinuation] at hoffset
          simp only [Option.map_some, Option.some.injEq] at hoffset
          subst offset
          simp only [transitionStmtOutputWires]
          rw [ih (start := start + stateCount tm + stateCount tm)
            (source := source.replaceState
              (oneHotMapGateTrace start source.state
                (stmtStateTable tm update)).wires)
            (hsupport := hsupportContinuation)
            (offset := continuationOffset) (hoffset := hcontinuation)]
          apply congrArg (arithmeticMuxCfgWires tm height)
          simp [TransitionAffineNat.eval_add]
          omega
  | push k emit continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      simp only [transitionStmtFinalBranchMuxOffsetAffine] at hoffset
      cases hcontinuation :
          transitionStmtFinalBranchMuxOffsetAffine tm continuation with
      | none => simp [hcontinuation] at hoffset
      | some continuationOffset =>
          rw [hcontinuation] at hoffset
          simp only [Option.map_some, Option.some.injEq] at hoffset
          subst offset
          simp only [transitionStmtOutputWires]
          rw [ih (hsupport := hsupportContinuation)
            (offset := continuationOffset) (hoffset := hcontinuation)]
          apply congrArg (arithmeticMuxCfgWires tm height)
          simp [TransitionAffineNat.eval_add]
          omega
  | peek k update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtFinalBranchMuxOffsetAffine] at hoffset
      cases hcontinuation :
          transitionStmtFinalBranchMuxOffsetAffine tm continuation with
      | none => simp [hcontinuation] at hoffset
      | some continuationOffset =>
          rw [hcontinuation] at hoffset
          simp only [Option.map_some, Option.some.injEq] at hoffset
          subst offset
          simp only [transitionStmtOutputWires]
          rw [ih (hsupport := hsupportContinuation)
            (offset := continuationOffset) (hoffset := hcontinuation)]
          apply congrArg (arithmeticMuxCfgWires tm height)
          simp [TransitionAffineNat.eval_add]
          omega
  | pop k update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtFinalBranchMuxOffsetAffine] at hoffset
      cases hcontinuation :
          transitionStmtFinalBranchMuxOffsetAffine tm continuation with
      | none => simp [hcontinuation] at hoffset
      | some continuationOffset =>
          rw [hcontinuation] at hoffset
          simp only [Option.map_some, Option.some.injEq] at hoffset
          subst offset
          simp only [transitionStmtOutputWires]
          rw [ih (hsupport := hsupportContinuation)
            (offset := continuationOffset) (hoffset := hcontinuation)]
          apply congrArg (arithmeticMuxCfgWires tm height)
          cases height with
          | zero => omega
          | succ height =>
              simp [TransitionAffineNat.eval_add, popStackWireGateCost]
              omega
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp only [transitionStmtFinalBranchMuxOffsetAffine,
        Option.some.injEq] at hoffset
      subst offset
      simp only [transitionStmtOutputWires]
      apply congrArg (arithmeticMuxCfgWires tm height)
      simp only [TransitionAffineNat.eval_add,
        TransitionAffineNat.eval_const]
      rw [compileStmtGateAffine_eval tm whenTrue height hheight,
        compileStmtGateAffine_eval tm whenFalse height hheight]
      omega

end CLRS.Chapter34.Turing.CookLevin


