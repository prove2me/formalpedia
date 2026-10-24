-- Prove2me | Definitions.Def_PricingWithTips3DM_027690d1f1e5f4efd7f01904
-- name    : PricingWithTips3DM_027690d1f1e5f4efd7f01904
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:27:37.706737+00:00
-- url     : https://prove2.me/theorems/76193c30-1449-463d-aa98-e32f59059e8b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInitialStatementQuotedRowSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0bd84d3bd51393b618e343c5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quoted controller rows for one verifier program label

The general recursive source is instantiated here with the verifier's initial
statement context, its uniform route theorem, and its public-row padding
theorem.  The resulting concrete TM2 source directly targets the textbook
statement script for a fixed program label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Initial-context recursive padding, uniform over all canonical seeds. -/
theorem verifierTransitionInitialStmtPadding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (label : W.machine.tm.Λ) :
    VerifierTransitionRecursiveStmtPadding W
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) := by
  intro input seed hseed
  exact transitionStmtRecursiveContextPadding_initial_verifier W input seed
    (verifierTransitionRowSeeds_height_eq W input seed hseed) label

/-- Concrete quoted statement source for one fixed verifier label. -/
noncomputable def verifierTransitionInitialStmtQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    VerifierTransitionSeedRowSource W :=
  verifierTransitionStmtQuotedSeedRowSource W labelOffset
    (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label)
    (stmtPushSet_program_subset W.machine.tm label)
    (verifierTransitionRecursivePlan_uniformLinearRouteBounds W labelOffset
      label)
    (verifierTransitionInitialStmtPadding W label)

/-- On every canonical seed, the physical row is exactly the quotation of
the canonical statement-controller script for this label. -/
theorem verifierTransitionInitialStmtQuotedSeedRowSource_row_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionInitialStmtQuotedSeedRowSource W labelOffset label).row
        seed =
      quoteUnaryFrameStream
        (encodeAffineStmtControllerScript
          (transitionStmtScript W.machine.tm
            (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
            (seed.start + labelOffset.eval seed.height)
            (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
              seed.rowBase)
            (W.machine.tm.m label)
            (stmtPushSet_program_subset W.machine.tm label))) := by
  unfold verifierTransitionInitialStmtQuotedSeedRowSource
  rw [verifierTransitionStmtQuotedSeedRowSource_row_eq W labelOffset
    (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    (verifierTransitionRecursivePlan_uniformLinearRouteBounds W labelOffset
      label)
    (verifierTransitionInitialStmtPadding W label) input seed hseed]
  rw [transitionStmtRecursiveInitialControllerFrames_eq_script W input seed
    (verifierTransitionRowSeeds_height_eq W input seed hseed) labelOffset
    label]

end CLRS.Chapter34.Turing.CookLevin


