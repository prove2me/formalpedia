-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part4
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:56:14.879854+00:00
-- url     : https://prove2.me/theorems/4d54b83d-cc52-499c-b5d1-35fa5f2fbc32
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Row-major compact invocations for the already verified continuous
validity-tail source. -/
noncomputable def verifierValidityRowTailSourceInvocationFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierValidityRowSeeds W input).flatMap fun seed =>
    encodeAffineValidityTailSourceInvocation
      (arithmeticValidityTailSourceFrame W.machine.tm
        seed.height seed.start seed.rowBase)

/-- The constructed spliced stream is byte-for-byte the established compact
tail-source invocation family. -/
theorem verifierValidityRowTailSplicedSourceFrames_eq_invocations
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailSplicedSourceFrames W input =
      verifierValidityRowTailSourceInvocationFrames W input := by
  rw [verifierValidityRowTailSplicedSourceFrames_eq_rows]
  unfold verifierValidityRowTailSourceInvocationFrames
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [encodeUnaryFrameFixedPrefixSpliceOutputFamily,
        List.flatMap_cons]
      rw [show
        encodeUnaryFrameWithFixedDelimiters
              (arithmeticValidityTailFixedOperandValues W.machine.tm
                seed.height seed.start seed.rowBase)
              (arithmeticValidityTailFixedOperandDelimiters W.machine.tm) ++
            encodeAffineExactlyOneOutputSourceInvocationFamily
                (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
              [.frameEnd] =
          encodeAffineValidityTailSourceInvocation
            (arithmeticValidityTailSourceFrame W.machine.tm
              seed.height seed.start seed.rowBase) by
        simpa [validityRowSeedOneHotFrames] using
          arithmeticValidityTailSplicedRow_eq_sourceInvocation
            W.machine.tm seed.height seed.start seed.rowBase]
      rw [ih]

/-- The raw verifier word polynomially computes the complete compact input
stream for every continuous validity-tail source invocation. -/
noncomputable def
    verifierValidityRowTailSourceInvocationFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailSourceInvocationFrames W) := by
  let source :=
    verifierValidityRowTailSplicedSourceFrames_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailSplicedSourceFrames_eq_invocations W input]
          using source.outputsFun input }

/-! ## Continuous tail-family execution -/

/-- Typed verifier family consumed by the reusable continuous tail-source
wrapper. -/
noncomputable def verifierValidityRowTailSourceFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AffineValidityTailSourceFamily
      (arithmeticRuntimeStackSourceBlankSteps W.machine.tm) :=
  { frames := (verifierValidityRowSeeds W input).map fun seed =>
      arithmeticValidityTailSourceFrame W.machine.tm
        seed.height seed.start seed.rowBase
    stack_lengths := by
      intro frame hframe
      rw [List.mem_map] at hframe
      rcases hframe with ⟨seed, hseed, rfl⟩
      exact arithmeticRuntimeStackSourceSeeds_length
        W.machine.tm seed.height seed.start seed.rowBase }

/-- The typed family encoding is exactly the compact invocation stream
constructed above from the raw verifier input. -/
theorem verifierValidityRowTailSourceFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineValidityTailSourceFamily
        (verifierValidityRowTailSourceFamily W input) =
      verifierValidityRowTailSourceInvocationFrames W input := by
  unfold encodeAffineValidityTailSourceFamily
  change encodeAffineValidityTailSourceInvocationFamily
      ((verifierValidityRowSeeds W input).map fun seed =>
        arithmeticValidityTailSourceFrame W.machine.tm
          seed.height seed.start seed.rowBase) = _
  unfold verifierValidityRowTailSourceInvocationFrames
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineValidityTailSourceInvocationFamily, ih]

/-- Executing the continuous compact source family yields exactly the
pre-existing canonical validity-tail operand stream. -/
theorem verifierValidityRowTailSourceFamilyStream_eq_operands
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineValidityTailSourceFamilyStream
        (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
        (verifierValidityRowTailSourceFamily W input).frames =
      verifierValidityRowTailOperandFrames W input := by
  change affineValidityTailSourceFamilyStream
      (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
      ((verifierValidityRowSeeds W input).map fun seed =>
        arithmeticValidityTailSourceFrame W.machine.tm
          seed.height seed.start seed.rowBase) = _
  unfold verifierValidityRowTailOperandFrames validityRowSeedTailFamily
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, affineValidityTailSourceFamilyStream,
        List.flatMap_cons]
      rw [arithmeticValidityTailSourceFrame_eq, ih]
      rfl

/-- The raw verifier word polynomially computes all canonical post-halted
validity-row tail operands.  This closes the former gap between the
seed/one-hot compiler and the established continuous tail controller. -/
noncomputable def verifierValidityRowTailOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailOperandFrames W) := by
  let invocationSource :=
    verifierValidityRowTailSourceInvocationFrames_computableInPolyTime W
  let typedInvocationSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineValidityTailSourceFamily
        (verifierValidityRowTailSourceFamily W) :=
    { tm := invocationSource.tm
      inputAlphabet := invocationSource.inputAlphabet
      outputAlphabet := invocationSource.outputAlphabet
      time := invocationSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowTailSourceFamily_encoding_eq W input] using
          invocationSource.outputsFun input }
  let familySource := affineValidityTailSourceFamily_computableInPolyTime
    (arithmeticRuntimeStackSourceBlankSteps W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedInvocationSource familySource
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierValidityRowTailSourceFamilyStream_eq_operands W input]
          using run }
end CLRS.Chapter34.Turing.CookLevin


