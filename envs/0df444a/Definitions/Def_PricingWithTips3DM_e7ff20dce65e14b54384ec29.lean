-- Prove2me | Definitions.Def_PricingWithTips3DM_e7ff20dce65e14b54384ec29
-- name    : PricingWithTips3DM_e7ff20dce65e14b54384ec29
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:02:04.095315+00:00
-- url     : https://prove2.me/theorems/d9bb1a89-9a5b-42c1-84bd-30837bd52b0d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrLayout
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_62b1ab943426d8c092ff20f0
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Arithmetic layout of the verifier-input final disjunction

The input arms are followed by one false-seeded OR fold.  This module gives
its start and every source wire without referring to the recursive circuit
builder.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Pure arithmetic start of the final input-arm disjunction. -/
def verifierInputFinalOrStart
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  (verifierInputArmsStartPolynomial W).eval input.length +
    verifierInputArmPrefixCost W input.length
      (W.certificateBound.eval input.length + 1)

/-- Pure output wire of the conjunction for one candidate length. -/
def verifierInputArmOutputWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) : Nat :=
  (verifierInputArmsStartPolynomial W).eval input.length +
    verifierInputArmPrefixCost W input.length arm.val +
      arm.val + input.length + 2

/-- Pure ordered source family of the final input-arm disjunction. -/
def verifierInputFinalOrWires
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
    verifierInputArmOutputWire W input arm

/-- The semantic recursive arm builder ends at the pure final-OR start. -/
theorem verifierInputBoundaryScript_finalOrStart_eq_arithmetic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).finalOrStart =
      verifierInputFinalOrStart W input := by
  unfold verifierInputFinalOrStart
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  dsimp only
  rw [VerifierInput.InputArmsResult.gate_delta]
  rw [verifierInputArmsStartPolynomial_eval_eq_separatorBuilder]
  rfl

/-- The semantic final-OR source list is exactly the arithmetic conjunction
output family. -/
theorem verifierInputBoundaryScript_finalOrWires_eq_arithmetic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).finalOrWires =
      verifierInputFinalOrWires W input := by
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  dsimp only
  unfold verifierInputFinalOrWires
  apply List.ofFn_inj.mpr
  funext arm
  rw [VerifierInput.buildInputArms_wires_eq]
  · unfold verifierInputArmOutputWire verifierInputArmPrefixCost
    rw [verifierInputArmsStartPolynomial_eval_eq_separatorBuilder]
  · exact verifierInputArm_fits W input arm

end CLRS.Chapter34.Turing.CookLevin


