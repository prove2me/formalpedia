-- Prove2me | Definitions.Def_PricingWithTips3DM_6890a8cc8d21d05e1c974e9b
-- name    : PricingWithTips3DM_6890a8cc8d21d05e1c974e9b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T03:06:12.301423+00:00
-- url     : https://prove2.me/theorems/7cc3e810-3620-43d3-a6b8-c7568e705ea3
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveRows
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_dd1ab7708e2774dc36bdad0c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Recursive statement streams for every transition row

The canonical transition-row seed family supplies one dispatch start and one
public row base for each adjacent tableau pair.  Flattening the recursive
all-label statement stream over those seeds therefore covers every statement
subscript in the complete transition family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All generated recursive statement-controller frames, in row-major order. -/
def verifierTransitionRecursiveStatementControllerTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchRecursiveStatementControllerFrames W.machine.tm)

/-- All corresponding semantic statement-script frames, in row-major order. -/
def verifierTransitionRecursiveStatementSemanticTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchRecursiveStatementSemanticFrames W.machine.tm)

/-- The unrestricted recursive generator covers every label of every local
transition row. -/
theorem verifierTransitionRecursiveStatementControllerTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRecursiveStatementControllerTarget W input =
      verifierTransitionRecursiveStatementSemanticTarget W input := by
  unfold verifierTransitionRecursiveStatementControllerTarget
    verifierTransitionRecursiveStatementSemanticTarget
  apply List.flatMap_congr
  intro seed hseed
  apply verifierTransitionDispatchRecursiveStatementControllerFrames_eq
    W input seed
  exact verifierTransitionRowSeeds_height_eq W input seed hseed

end CLRS.Chapter34.Turing.CookLevin


