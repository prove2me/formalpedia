-- Prove2me | Definitions.Def_PricingWithTips3DM_dd1ab7708e2774dc36bdad0c
-- name    : PricingWithTips3DM_dd1ab7708e2774dc36bdad0c
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T03:03:59.37333+00:00
-- url     : https://prove2.me/theorems/ceecf699-95cb-4845-8149-66f98289c788
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveLabels
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_437c204810c3cbe698cd91bd
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Recursive statement-controller streams for all dispatch labels

One local transition dispatch compiles every fixed program label at a distinct
affine offset.  This module folds the unrestricted recursive statement source
over the canonical label order and proves exact agreement with the semantic
statement scripts for the whole label family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Interleaved recursive controller output for an arbitrary label suffix. -/
noncomputable def
    transitionDispatchRecursiveStatementControllerFramesForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List UnaryFrameSym
  | _, [] => []
  | labelOffset, label :: labels =>
      transitionStmtRecursiveControllerFrames tm seed labelOffset
          (TransitionStmtAffineContext.initial tm) (tm.m label)
          (stmtPushSet_program_subset tm label) ++
        transitionDispatchRecursiveStatementControllerFramesForLabels tm seed
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

/-- Semantic controller encodings of the same statement-script family. -/
def transitionDispatchRecursiveStatementSemanticFramesForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List UnaryFrameSym
  | _, [] => []
  | labelOffset, label :: labels =>
      encodeAffineStmtControllerScript
          (transitionStmtScript tm (workHeight tm seed.height) seed.start
            (seed.start + 1)
            (seed.start + labelOffset.eval seed.height)
            (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
            (tm.m label) (stmtPushSet_program_subset tm label)) ++
        transitionDispatchRecursiveStatementSemanticFramesForLabels tm seed
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

/-- Complete recursive statement-controller output in canonical label order. -/
def transitionDispatchRecursiveStatementControllerFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  transitionDispatchRecursiveStatementControllerFramesForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Complete semantic statement-script encoding in canonical label order. -/
def transitionDispatchRecursiveStatementSemanticFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  transitionDispatchRecursiveStatementSemanticFramesForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Every verifier label suffix is generated exactly. -/
theorem
    verifierTransitionDispatchRecursiveStatementControllerFramesForLabels_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length) :
    ∀ (labelOffset : TransitionAffineNat)
      (labels : List W.machine.tm.Λ),
      transitionDispatchRecursiveStatementControllerFramesForLabels
          W.machine.tm seed labelOffset labels =
        transitionDispatchRecursiveStatementSemanticFramesForLabels
          W.machine.tm seed labelOffset labels := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      simp only [
        transitionDispatchRecursiveStatementControllerFramesForLabels,
        transitionDispatchRecursiveStatementSemanticFramesForLabels]
      rw [transitionStmtRecursiveInitialControllerFrames_eq_script W input
        seed hseed labelOffset label]
      rw [ih]

/-- Hence the complete canonical label family has no residual statement-shape
restriction. -/
theorem verifierTransitionDispatchRecursiveStatementControllerFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length) :
    transitionDispatchRecursiveStatementControllerFrames W.machine.tm seed =
      transitionDispatchRecursiveStatementSemanticFrames W.machine.tm
        seed := by
  exact
    verifierTransitionDispatchRecursiveStatementControllerFramesForLabels_eq
      W input seed hseed (TransitionAffineNat.const 2)
      (programLabels W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin


