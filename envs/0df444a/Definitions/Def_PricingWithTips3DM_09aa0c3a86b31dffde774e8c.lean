-- Prove2me | Definitions.Def_PricingWithTips3DM_09aa0c3a86b31dffde774e8c
-- name    : PricingWithTips3DM_09aa0c3a86b31dffde774e8c
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:06:11.365006+00:00
-- url     : https://prove2.me/theorems/7809eae6-5de3-459c-b7e6-cdd6efdd3933
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmSingletonRowsSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bb4dfff051b6cd83a923236f
import Definitions.Def_PricingWithTips3DM_47f4839a20fc6c9c7cebd9d4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Marked singleton rows of verifier-input arms

The height and blank-separator operands are already available as ordinary
unary-frame progressions.  This module puts one value in every marked row so
that the two streams can be combined pointwise with the other arm channels.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One marked singleton height operand for every candidate-length arm. -/
def verifierInputArmHeightWireFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows
    (List.ofFn fun arm :
        Fin (W.certificateBound.eval input.length + 1) =>
      verifierInputArmHeightWire W input arm)

/-- One marked singleton blank-separator operand for every arm. -/
def verifierInputArmSeparatorWireFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows
    (List.ofFn fun arm :
        Fin (W.certificateBound.eval input.length + 1) =>
      verifierInputArmSeparatorWire W input arm)

@[simp] theorem verifierInputArmHeightWireFamily_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmHeightWireFamily W input).rows.length =
      W.certificateBound.eval input.length + 1 := by
  simp [verifierInputArmHeightWireFamily]

@[simp] theorem verifierInputArmSeparatorWireFamily_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmSeparatorWireFamily W input).rows.length =
      W.certificateBound.eval input.length + 1 := by
  simp [verifierInputArmSeparatorWireFamily]

/-- The existing height progression followed by the fixed one-field marker
is a concrete polynomial-time source for the typed height rows. -/
noncomputable def verifierInputArmHeightWireFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmHeightWireFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source := verifierInputArmHeightWireFrames_computableInPolyTime W
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [verifierInputArmHeightWireFrames_eq_encode W input,
          markUnaryFrameSingleFieldRows_encode] at run
        simpa only [id_eq, verifierInputArmHeightWireFamily] using run }

/-- The existing separator progression followed by the same fixed marker is
a concrete polynomial-time source for the typed separator rows. -/
noncomputable def verifierInputArmSeparatorWireFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmSeparatorWireFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source := verifierInputArmSeparatorWireFrames_computableInPolyTime W
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [verifierInputArmSeparatorWireFrames_eq_encode W input,
          markUnaryFrameSingleFieldRows_encode] at run
        simpa only [id_eq, verifierInputArmSeparatorWireFamily] using run }

end CLRS.Chapter34.Turing.CookLevin


