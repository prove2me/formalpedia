-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part9
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:37:30.783117+00:00
-- url     : https://prove2.me/theorems/b62b89d5-766e-4d1d-9024-e1a6ef058cb5
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part9
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Expand the first compact one-hot copy without losing the second row -/

/-- Typed payload-preserving expansion family induced by the routed verifier
rows.  Its opaque payload is the complete second plain row. -/
noncomputable def verifierValidityRowExpandedPrefixPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineExactlyOneMarkedPrefixPayloadFamily :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      (validityRowSeedOneHotFrames W.machine.tm seed,
        encodeUnaryFrame
            (arithmeticValidityRowFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase) ++
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed))
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      rw [List.mem_append] at hsymbol
      rcases hsymbol with hfixed | hcompact
      · exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hfixed
      · exact inputCompiler_compactFamily_no_frameEnd _ symbol hcompact }

/-- The typed prefix-expander input is byte-for-byte the routed stream. -/
theorem verifierValidityRowExpandedPrefixPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineExactlyOneMarkedPrefixPayloadInput
        (verifierValidityRowExpandedPrefixPayloadFamily W input) =
      verifierValidityRowRoutedOperandPayloadFrames W input := by
  rw [verifierValidityRowRoutedOperandPayloadFrames_eq_rows]
  unfold encodeAffineExactlyOneMarkedPrefixPayloadInput
    verifierValidityRowExpandedPrefixPayloadFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- Concrete stream after the first compact copy has become the canonical
one-hot prefix expected by the outer validity-row controller. -/
noncomputable def verifierValidityRowExpandedPrefixPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineExactlyOneMarkedPrefixPayloadOutput
    (verifierValidityRowExpandedPrefixPayloadFamily W input)

/-- Exact row-major semantics after canonical one-hot expansion. -/
theorem verifierValidityRowExpandedPrefixPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowExpandedPrefixPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        .tick ::
          (encodeAffineExactlyOneFamily
              (validityRowSeedOneHotFrames W.machine.tm seed) ++
            .frameEnd ::
              (encodeUnaryFrame
                  (arithmeticValidityRowFixedOperandValues W.machine.tm
                    seed.height seed.start seed.rowBase) ++
                encodeAffineExactlyOneCompactFamily
                  (validityRowSeedOneHotFrames W.machine.tm seed) ++
                [.frameEnd])) := by
  unfold verifierValidityRowExpandedPrefixPayloadFrames
    encodeAffineExactlyOneMarkedPrefixPayloadOutput
    verifierValidityRowExpandedPrefixPayloadFamily
  rw [List.flatMap_map]

/-- From the original verifier word, one fixed polynomial-time pipeline now
computes the canonical one-hot prefix while retaining every later row-local
operand in the same physical stream. -/
noncomputable def
    verifierValidityRowExpandedPrefixPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowExpandedPrefixPayloadFrames W) := by
  let routedSource :=
    verifierValidityRowRoutedOperandPayloadFrames_computableInPolyTime W
  let typedRoutedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineExactlyOneMarkedPrefixPayloadInput
        (verifierValidityRowExpandedPrefixPayloadFamily W) :=
    { tm := routedSource.tm
      inputAlphabet := routedSource.inputAlphabet
      outputAlphabet := routedSource.outputAlphabet
      time := routedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowExpandedPrefixPayloadFamily_encoding_eq W input]
          using routedSource.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedRoutedSource
      affineExactlyOneMarkedPrefixPayload_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      encodeAffineExactlyOneMarkedPrefixPayloadOutput
        (verifierValidityRowExpandedPrefixPayloadFamily W input))
  simpa [Function.comp_def] using Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin


