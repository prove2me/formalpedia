-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part11
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part11
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:40:48.18981+00:00
-- url     : https://prove2.me/theorems/6324909b-24d0-4689-a6d7-f5d794019379
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part11
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part10
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Typed delimiter-splice view of the projected rows. -/
noncomputable def verifierValidityRowProjectedFixedPrefixFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    UnaryFrameLeadingSegmentFixedPrefixFamily
      (arithmeticValidityRowFixedOperandDelimiters W.machine.tm) :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      { leading := .tick :: encodeAffineExactlyOneFamily
          (validityRowSeedOneHotFrames W.machine.tm seed)
        values := arithmeticValidityRowFixedOperandValues W.machine.tm
          seed.height seed.start seed.rowBase
        payload := encodeAffineExactlyOneOutputSourceInvocationFamily
          (validityRowSeedOneHotFrames W.machine.tm seed).reverse }
    values_lengths := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact arithmeticValidityRowFixedOperandValues_length
        W.machine.tm seed.height seed.start seed.rowBase
    leading_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      simp only [List.mem_cons] at hsymbol
      rcases hsymbol with rfl | hfamily
      · simp
      · exact inputCompiler_exactlyOneFamily_no_frameEnd _ symbol hfamily
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact inputCompiler_outputInvocationFamily_no_frameEnd
        _ symbol hsymbol }

/-- The delimiter-splice input is exactly the projected row stream. -/
theorem verifierValidityRowProjectedFixedPrefixFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameLeadingSegmentFixedPrefixInput
        (verifierValidityRowProjectedFixedPrefixFamily W input) =
      verifierValidityRowProjectedOperandFrames W input := by
  rw [verifierValidityRowProjectedOperandFrames_eq_rows]
  unfold encodeUnaryFrameLeadingSegmentFixedPrefixInput
    verifierValidityRowProjectedFixedPrefixFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- Complete compact source invocation rows: the fixed halted/tail fields now
carry their final delimiter table, while the projected one-hot invocations
remain unchanged. -/
noncomputable def verifierValidityRowCompactSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameLeadingSegmentFixedPrefixOutput
    (verifierValidityRowProjectedFixedPrefixFamily W input)

/-- Exact row-major form before exposing the semantic halted/tail boundary. -/
theorem verifierValidityRowCompactSourceFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowCompactSourceFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        .tick ::
          (encodeAffineExactlyOneFamily
              (validityRowSeedOneHotFrames W.machine.tm seed) ++
            .frameEnd ::
              (encodeUnaryFrameWithFixedDelimiters
                  (arithmeticValidityRowFixedOperandValues W.machine.tm
                    seed.height seed.start seed.rowBase)
                  (arithmeticValidityRowFixedOperandDelimiters W.machine.tm) ++
                encodeAffineExactlyOneOutputSourceInvocationFamily
                  (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
                [.frameEnd])) := by
  unfold verifierValidityRowCompactSourceFrames
    encodeUnaryFrameLeadingSegmentFixedPrefixOutput
    verifierValidityRowProjectedFixedPrefixFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- The compact source rows have exactly the established public outer
one-hot and halted fields, followed by one complete validity-tail source
invocation. -/
theorem verifierValidityRowCompactSourceFrames_eq_explicit
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowCompactSourceFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        .tick ::
          (encodeAffineExactlyOneFamily
              (validityRowSeedOneHotFrames W.machine.tm seed) ++
            .frameEnd ::
              (encodeUnaryFrame
                    [ arithmeticHaltedMatchStart W.machine.tm
                        seed.height seed.start,
                      seed.rowBase,
                      arithmeticNoneLabelWire W.machine.tm seed.rowBase ] ++
                [.frameEnd] ++
                encodeUnaryFrameWithFixedDelimiters
                  (arithmeticValidityTailFixedOperandValues W.machine.tm
                    seed.height seed.start seed.rowBase)
                  (arithmeticValidityTailFixedOperandDelimiters W.machine.tm) ++
                encodeAffineExactlyOneOutputSourceInvocationFamily
                  (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
                [.frameEnd])) := by
  rw [verifierValidityRowCompactSourceFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [arithmeticValidityRowFixedEncoding_eq, ih]

/-- Each compact row now contains one atomic invocation of the already
verified continuous validity-tail source. -/
theorem verifierValidityRowCompactSourceFrames_eq_invocations
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowCompactSourceFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        .tick ::
          (encodeAffineExactlyOneFamily
              (validityRowSeedOneHotFrames W.machine.tm seed) ++
            .frameEnd ::
              (encodeUnaryFrame
                    [ arithmeticHaltedMatchStart W.machine.tm
                        seed.height seed.start,
                      seed.rowBase,
                      arithmeticNoneLabelWire W.machine.tm seed.rowBase ] ++
                [.frameEnd] ++
                encodeAffineValidityTailSourceInvocation
                  (arithmeticValidityTailSourceFrame W.machine.tm
                    seed.height seed.start seed.rowBase))) := by
  rw [verifierValidityRowCompactSourceFrames_eq_explicit]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      have htail :
        encodeUnaryFrameWithFixedDelimiters
              (arithmeticValidityTailFixedOperandValues W.machine.tm
                seed.height seed.start seed.rowBase)
              (arithmeticValidityTailFixedOperandDelimiters W.machine.tm) ++
            encodeAffineExactlyOneOutputSourceInvocationFamily
                (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
              [.frameEnd] =
          encodeAffineValidityTailSourceInvocation
            (arithmeticValidityTailSourceFrame W.machine.tm
              seed.height seed.start seed.rowBase) := by
        simpa [validityRowSeedOneHotFrames] using
          arithmeticValidityTailSplicedRow_eq_sourceInvocation
            W.machine.tm seed.height seed.start seed.rowBase
      rw [ih]
      simp [List.append_assoc, htail]

/-- End-to-end polynomial-time construction of the compact source rows from
the raw verifier word. -/
noncomputable def
    verifierValidityRowCompactSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowCompactSourceFrames W) := by
  let projectedSource :=
    verifierValidityRowProjectedOperandFrames_computableInPolyTime W
  let typedProjectedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeUnaryFrameLeadingSegmentFixedPrefixInput
        (verifierValidityRowProjectedFixedPrefixFamily W) :=
    { tm := projectedSource.tm
      inputAlphabet := projectedSource.inputAlphabet
      outputAlphabet := projectedSource.outputAlphabet
      time := projectedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowProjectedFixedPrefixFamily_encoding_eq W input]
          using projectedSource.outputsFun input }
  let spliceSource :=
    unaryFrameLeadingSegmentFixedPrefix_computableInPolyTime
      (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
  let typedSpliceSource :
      _root_.Turing.TM2ComputableInPolyTime
        encodeUnaryFrameLeadingSegmentFixedPrefixInput id
        (fun family : UnaryFrameLeadingSegmentFixedPrefixFamily
            (arithmeticValidityRowFixedOperandDelimiters W.machine.tm) =>
          rewriteUnaryFrameLeadingSegmentFixedPrefix
            (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
            (encodeUnaryFrameLeadingSegmentFixedPrefixInput family)) :=
    { tm := spliceSource.tm
      inputAlphabet := spliceSource.inputAlphabet
      outputAlphabet := spliceSource.outputAlphabet
      time := spliceSource.time
      outputsFun := fun family => by
        simpa only [id_eq] using spliceSource.outputsFun
          (encodeUnaryFrameLeadingSegmentFixedPrefixInput family) }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedProjectedSource typedSpliceSource
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [rewriteUnaryFrameLeadingSegmentFixedPrefix_family
          (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
          (verifierValidityRowProjectedFixedPrefixFamily W input)
          (arithmeticValidityRowFixedOperandDelimiters_nonempty W.machine.tm)]
          at run
        simpa only [id_eq, verifierValidityRowCompactSourceFrames]
          using run }
end CLRS.Chapter34.Turing.CookLevin


