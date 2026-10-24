-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part14
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part14
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:53:22.509485+00:00
-- url     : https://prove2.me/theorems/7421d301-0b63-47d9-bb8d-332dcd5fae20
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part14
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part13
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fully expanded row packets emitted by the one continuous prefixed-tail
controller. -/
noncomputable def verifierValidityRowCompleteInputFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineValidityTailPrefixedSourceOutput
    (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
    (verifierValidityRowPrefixedTailSourceFamily W input)

/-- Expanding every compact source invocation recovers the exact recursive
complete-row target, including all row boundaries. -/
theorem verifierValidityRowCompleteInputFrames_eq_target
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowCompleteInputFrames W input =
      verifierValidityRowFamilyInputTarget W input := by
  unfold verifierValidityRowCompleteInputFrames
    encodeAffineValidityTailPrefixedSourceOutput
    verifierValidityRowPrefixedTailSourceFamily
    verifierValidityRowFamilyInputTarget
  rw [List.flatMap_map]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => simp [validityRowSeedFamilyInput]
  | cons seed rest ih =>
      dsimp only at ih
      simp only [List.flatMap_cons, validityRowSeedFamilyInput]
      rw [arithmeticValidityTailSourceFrame_eq]
      simp only [List.append_assoc] at ih ⊢
      rw [ih]
      simp [encodeAffineValidityRowFrame, expandValidityRowSeed,
        arithmeticValidityRowFrame, validityRowSeedOneHotFrames,
        List.append_assoc]

/-- The raw verifier word is transformed by one fixed polynomial-time TM2
into the exact complete validity-row family input. -/
noncomputable def
    verifierValidityRowCompleteInputFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowCompleteInputFrames W) := by
  let compactSource :=
    verifierValidityRowCompactSourceFrames_computableInPolyTime W
  let typedCompactSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineValidityTailPrefixedSourceInput
        (verifierValidityRowPrefixedTailSourceFamily W) :=
    { tm := compactSource.tm
      inputAlphabet := compactSource.inputAlphabet
      outputAlphabet := compactSource.outputAlphabet
      time := compactSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowPrefixedTailSourceFamily_encoding_eq W input]
          using compactSource.outputsFun input }
  let familySource := affineValidityTailPrefixedSource_computableInPolyTime
    (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedCompactSource familySource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      encodeAffineValidityTailPrefixedSourceOutput
        (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
        (verifierValidityRowPrefixedTailSourceFamily W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Public polynomial-time interface for the canonical validity-row family
input expected by the already verified row gate controller. -/
noncomputable def
    verifierValidityRowFamilyInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowFamilyInputTarget W) := by
  let source := verifierValidityRowCompleteInputFrames_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowCompleteInputFrames_eq_target W input]
          using source.outputsFun input }

/-- Running the canonical row-family controller over the generated input
produces exactly the verifier's semantic validity gate stream. -/
theorem verifierValidityRowFamilyGateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineValidityRowFamilyGateStream
        (verifierValidityRowFramesByLength W input.length) =
      verifierValidityGateStream W input := by
  rw [verifierValidityGateStream_eq_byLength]
  unfold verifierValidityRowFramesByLength
    verifierValidityGateStreamByLength
  exact arithmeticValidityRowsGateStream_eq_semantic W.machine.tm
    ((verifierHeight W).eval input.length)
    ((verifierHorizon W).eval input.length)

/-- Concrete polynomial-time validity-phase generator from the raw verifier
word to the exact forward circuit-gate encoding. -/
noncomputable def verifierValidityGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityGateStream W) := by
  let inputSource :=
    verifierValidityRowFamilyInputTarget_computableInPolyTime W
  let typedInputSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineValidityRowFamilyInput
        (fun input : List Γ =>
          verifierValidityRowFramesByLength W input.length) :=
    { tm := inputSource.tm
      inputAlphabet := inputSource.inputAlphabet
      outputAlphabet := inputSource.outputAlphabet
      time := inputSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowFamilyInputTarget_eq_canonical W input]
          using inputSource.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedInputSource
      affineValidityRowFamilyGateStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierValidityRowFamilyGateStream_eq W input] using run }
end CLRS.Chapter34.Turing.CookLevin


