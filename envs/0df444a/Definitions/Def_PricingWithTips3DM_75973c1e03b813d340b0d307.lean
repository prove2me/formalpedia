-- Prove2me | Definitions.Def_PricingWithTips3DM_75973c1e03b813d340b0d307
-- name    : PricingWithTips3DM_75973c1e03b813d340b0d307
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:57:09.796196+00:00
-- url     : https://prove2.me/theorems/ca9b9e8a-f8d7-42f5-b348-3723069ae0c0
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveSegments
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_d22a635ef5089e07420b2f48
import Definitions.Def_PricingWithTips3DM_e5e62b28da238a1360e67ab0
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Progression-controller segments for recursive statement muxes

Each nested branch mux is lowered to the same fixed generic progression
controller already used by the shallow compiler.  The arm rows now come from
the total recursive route, but the segment expansion and controller alphabet
are unchanged.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Singleton progression segments for one recursively routed branch mux. -/
def transitionStmtRecursiveBranchMuxInvocationSegments
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) : List AffineMuxInvocationProgression :=
  let view := transitionStmtRecursiveBranchMuxInvocationView tm seed
    labelOffset context test whenTrue whenFalse hsupport
  affineMuxInvocationSingletonSegments view.selector view.frames

/-- The generic progression controller expands those segments to the exact
tagged mux payload used by the recursive statement phases. -/
theorem transitionStmtRecursiveBranchMuxInvocationSegments_frames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (htruePadding : transitionStmtRecursiveContextPadding tm seed
      (transitionStmtBranchTrueContext tm context test) whenTrue
      (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport))
    (hfalsePadding : transitionStmtRecursiveContextPadding tm seed
      (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
      (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
        hsupport)) :
    affineMuxInvocationProgressionFamilyFrames
        (transitionStmtRecursiveBranchMuxInvocationSegments tm seed
          labelOffset context test whenTrue whenFalse hsupport) =
      (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
        context test whenTrue whenFalse hsupport).encode := by
  have htrueCapacity :=
    transitionStmtRecursiveContextPadding_linearResult_capacity tm seed
      (transitionStmtBranchTrueContext tm context test) whenTrue
      (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)
      htruePadding
  have hfalseCapacity :=
    transitionStmtRecursiveContextPadding_linearResult_capacity tm seed
      (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
      (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)
      hfalsePadding
  have hframes :=
    transitionStmtRecursiveBranchMuxInvocationView_frames tm seed hwork
      labelOffset context test whenTrue whenFalse hsupport htrueCapacity
      hfalseCapacity
  have hselector := transitionStmtBranchSelectorForm_value tm seed
    labelOffset context test
  have hviewSelector :
      (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
        context test whenTrue whenFalse hsupport).selector =
        transitionStmtBranchSemanticSelector tm seed labelOffset context
          test := by
    simpa [transitionStmtRecursiveBranchMuxInvocationView,
      transitionStmtBranchSemanticSelector] using hselector
  unfold transitionStmtRecursiveBranchMuxInvocationSegments
    TransitionDispatchMuxInvocationView.encode
  dsimp only
  rw [hviewSelector, hframes]
  apply affineMuxInvocationSingletonSegments_frames
  · exact affineMuxFinCanonicalFrames_selector _ _ _ _ _
  · exact affineMuxFinCanonicalFrames_falseArm _ _ _ _ _

end CLRS.Chapter34.Turing.CookLevin


