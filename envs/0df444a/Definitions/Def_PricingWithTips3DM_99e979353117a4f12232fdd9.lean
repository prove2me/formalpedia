-- Prove2me | Definitions.Def_PricingWithTips3DM_99e979353117a4f12232fdd9
-- name    : PricingWithTips3DM_99e979353117a4f12232fdd9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:15:13.276189+00:00
-- url     : https://prove2.me/theorems/19ffff05-6d2f-42c7-9628-2229a35bc5bb
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmRouteFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_aee87cb5b1ae90b59d1556c3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact raw-input frame target for complete dispatch true arms

The branch-ending true arms already have a concrete affine source.  The
terminal-ending arms now have exact descriptor-derived stack routes.  This
module freezes their common raw-input unary-frame target and proves that it is
byte-for-byte the complete semantic true-arm operand stream.  The separate
controller-realization theorem will consume this exact target.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Unary encoding of the complete descriptor-derived true-arm route family,
in transition-row order and then verifier program-label order. -/
noncomputable def verifierTransitionDispatchTrueArmRouteValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchTrueArmDescriptorRoutes W.machine.tm seed).flatten)

/-- The descriptor-derived frame target is exactly the already verified
complete value-route stream. -/
theorem verifierTransitionDispatchTrueArmRouteValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmRouteValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmValueRoutes W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchTrueArmRouteValueFrames
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  congr 1
  apply transitionDispatchTrueArmDescriptorRoutes_eq
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

/-- Consequently the frozen byte target is the semantic true-arm family used
by dispatch, with no descriptor or routing abstraction left in the statement.
-/
theorem verifierTransitionDispatchTrueArmRouteValueFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmRouteValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmRowsFromSeed W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchTrueArmRouteValueFrames
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  congr 1
  apply transitionDispatchTrueArmDescriptorRoutes_eq_seed
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

end CLRS.Chapter34.Turing.CookLevin


