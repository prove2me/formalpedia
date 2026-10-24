-- Prove2me | Definitions.Def_PricingWithTips3DM_4c39eb86d371b61789f95a71
-- name    : PricingWithTips3DM_4c39eb86d371b61789f95a71
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:08:34.386688+00:00
-- url     : https://prove2.me/theorems/2227f32c-8e50-4795-b6d2-cac4c6840198
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionRecursiveBranchDescriptorPipeline
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3cd84b37957a30eb7c7d76c9
import Definitions.Def_PricingWithTips3DM_14bd4b072646c5a202db88b2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# End-to-end recursive-branch descriptor pipeline

The raw descriptor generator, fixed length-prefixed interpreter, periodic
packet preparation, packet assembler, and mux progression expander are
composed here.  This validates the descriptor-driven route independently of
the older four-source branch packet construction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw verifier input to unprepared four-row recursive-branch packets,
factored through the concrete length-prefixed descriptor interpreter. -/
noncomputable def
    verifierTransitionRecursiveBranchDescriptorLabelPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htrueBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
        (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (hfalseBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        whenFalse
        (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (htruePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport))
    (hfalsePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport)) :
    _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      (verifierTransitionRecursiveBranchAlignedViewFamily W labelOffset context
        test whenTrue whenFalse hsupport htruePadding hfalsePadding) := by
  let descriptorSource :=
    verifierTransitionRecursiveBranchLengthPrefixedDescriptorFrames_computableInPolyTime
      W labelOffset context test whenTrue whenFalse hsupport htrueBounds
      hfalseBounds htruePadding hfalsePadding
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      descriptorSource
      transitionDispatchMuxInvocationLengthPrefixedDescriptorInterpreter_computableInPolyTime
  simpa only [Function.comp_def, id_eq] using Classical.choice composed

/-- The descriptor-driven physical route computes the complete recursive
branch mux frames in polynomial time from the original verifier input. -/
noncomputable def
    verifierTransitionRecursiveBranchMuxFrames_viaDescriptor_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htrueBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
        (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (hfalseBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        whenFalse
        (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (htruePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport))
    (hfalsePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionRecursiveBranchMuxFrames W labelOffset context test
        whenTrue whenFalse hsupport htruePadding hfalsePadding) := by
  let packetSource :=
    verifierTransitionRecursiveBranchDescriptorLabelPacketFrames_computableInPolyTime
      W labelOffset context test whenTrue whenFalse hsupport htrueBounds
      hfalseBounds htruePadding hfalsePadding
  let preparedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch packetSource
      transitionDispatchMuxInvocationLabelPacketPrepareAligned_computableInPolyTime
  let prepared := Classical.choice preparedExists
  let framesExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch prepared
      transitionDispatchMuxInvocationFrames_fromAlignedViews_computableInPolyTime
  let result := Classical.choice framesExists
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        simpa only [Function.comp_def, id_eq,
          verifierTransitionRecursiveBranchMuxFrames] using
            result.outputsFun input }

end CLRS.Chapter34.Turing.CookLevin


