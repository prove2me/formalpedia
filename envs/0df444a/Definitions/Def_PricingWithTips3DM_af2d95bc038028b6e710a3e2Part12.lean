-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part12
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part12
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:42:54.12005+00:00
-- url     : https://prove2.me/theorems/c096df45-976b-4b92-a278-1d1366219b15
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part12
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part11
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Typed view for rewriting only the fixed prefix of the retained second
row, while preserving the canonical one-hot leading segment. -/
noncomputable def verifierValidityRowLeadingFixedPrefixFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    UnaryFrameLeadingSegmentFixedPrefixFamily
      (arithmeticValidityRowFixedOperandDelimiters W.machine.tm) :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      { leading := .tick :: encodeAffineExactlyOneFamily
          (validityRowSeedOneHotFrames W.machine.tm seed)
        values := arithmeticValidityRowFixedOperandValues W.machine.tm
          seed.height seed.start seed.rowBase
        payload := encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFrames W.machine.tm seed) }
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
      exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol }

/-- The typed fixed-prefix input is exactly the expanded-prefix stream. -/
theorem verifierValidityRowLeadingFixedPrefixFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameLeadingSegmentFixedPrefixInput
        (verifierValidityRowLeadingFixedPrefixFamily W input) =
      verifierValidityRowExpandedPrefixPayloadFrames W input := by
  rw [verifierValidityRowExpandedPrefixPayloadFrames_eq_rows]
  unfold encodeUnaryFrameLeadingSegmentFixedPrefixInput
    verifierValidityRowLeadingFixedPrefixFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- Canonical one-hot prefixes followed by delimiter-materialized fixed
halted/tail operands and the retained compact one-hot suffix. -/
noncomputable def verifierValidityRowFixedPrefixMaterializedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameLeadingSegmentFixedPrefixOutput
    (verifierValidityRowLeadingFixedPrefixFamily W input)

/-- Exact row-major semantics after the fixed delimiter rewrite. -/
theorem verifierValidityRowFixedPrefixMaterializedFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowFixedPrefixMaterializedFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        .tick ::
          (encodeAffineExactlyOneFamily
              (validityRowSeedOneHotFrames W.machine.tm seed) ++
            .frameEnd ::
              (encodeUnaryFrameWithFixedDelimiters
                  (arithmeticValidityRowFixedOperandValues W.machine.tm
                    seed.height seed.start seed.rowBase)
                  (arithmeticValidityRowFixedOperandDelimiters W.machine.tm) ++
                encodeAffineExactlyOneCompactFamily
                  (validityRowSeedOneHotFrames W.machine.tm seed) ++
                [.frameEnd])) := by
  unfold verifierValidityRowFixedPrefixMaterializedFrames
    encodeUnaryFrameLeadingSegmentFixedPrefixOutput
    verifierValidityRowLeadingFixedPrefixFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- The materialized second-row prefix exposes the exact halted boundary and
the complete established tail-prefix delimiter table. -/
theorem verifierValidityRowFixedPrefixMaterializedFrames_eq_explicit
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowFixedPrefixMaterializedFrames W input =
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
                encodeAffineExactlyOneCompactFamily
                  (validityRowSeedOneHotFrames W.machine.tm seed) ++
                [.frameEnd])) := by
  rw [verifierValidityRowFixedPrefixMaterializedFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons]
      rw [arithmeticValidityRowFixedEncoding_eq, ih]

/-- The raw verifier word computes the delimiter-materialized row stream by
one fixed polynomial-time composition. -/
noncomputable def
    verifierValidityRowFixedPrefixMaterializedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowFixedPrefixMaterializedFrames W) := by
  let expandedSource :=
    verifierValidityRowExpandedPrefixPayloadFrames_computableInPolyTime W
  let typedExpandedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeUnaryFrameLeadingSegmentFixedPrefixInput
        (verifierValidityRowLeadingFixedPrefixFamily W) :=
    { tm := expandedSource.tm
      inputAlphabet := expandedSource.inputAlphabet
      outputAlphabet := expandedSource.outputAlphabet
      time := expandedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowLeadingFixedPrefixFamily_encoding_eq W input]
          using expandedSource.outputsFun input }
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
      typedExpandedSource typedSpliceSource
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
          (verifierValidityRowLeadingFixedPrefixFamily W input)
          (arithmeticValidityRowFixedOperandDelimiters_nonempty W.machine.tm)]
          at run
        simpa only [id_eq,
          verifierValidityRowFixedPrefixMaterializedFrames]
          using run }
end CLRS.Chapter34.Turing.CookLevin


