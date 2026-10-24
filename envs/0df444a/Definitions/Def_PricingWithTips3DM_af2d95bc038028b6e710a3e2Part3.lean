-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part3
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:27:03.904025+00:00
-- url     : https://prove2.me/theorems/e614fe90-664f-4ab0-8233-177621c8bbb7
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One seed plus its full compact one-hot row, before any projection to
final-conjunction output invocations. -/
noncomputable def verifierValidityRowUnifiedPayloadRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTriplePayloadRow :=
  (verifierValidityRowSeeds W input).map fun seed =>
    { seed := validityRowUnifiedAffineSeed
        seed.height seed.start seed.rowBase
      payload := encodeAffineExactlyOneCompactFamily
        (validityRowSeedOneHotFrames W.machine.tm seed) }

theorem inputCompiler_encodeUnaryFrame_no_frameEnd
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

theorem inputCompiler_compactFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneCompactFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction frames with
  | nil => simp [encodeAffineExactlyOneCompactFamily] at hsymbol
  | cons frame rest ih =>
      simp only [encodeAffineExactlyOneCompactFamily,
        List.mem_append] at hsymbol
      rcases hsymbol with hframe | hrest
      · exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hframe
      · exact ih hrest

/-- Typed well-formed domain for the single-source affine compiler. -/
noncomputable def verifierValidityRowUnifiedPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTriplePayloadFamily :=
  { rows := verifierValidityRowUnifiedPayloadRows W input
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [verifierValidityRowUnifiedPayloadRows, List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol }

/-- The typed affine-family input is byte-for-byte the existing concrete
seed-preserving compact one-hot stream. -/
theorem verifierValidityRowUnifiedPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowUnifiedPayloadFamily W input) =
      verifierValidityRowSeedMarkedOneHotFrames W input := by
  rw [verifierValidityRowSeedMarkedOneHotFrames_eq_rows]
  unfold encodeAffineUnaryTriplePayloadFamily
  change encodeAffineUnaryTriplePayloadRowFamily
      (verifierValidityRowUnifiedPayloadRows W input) = _
  unfold verifierValidityRowUnifiedPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTriplePayloadRowFamily,
        encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed,
        validityRowUnifiedAffineSeed, List.append_assoc]
      simpa [encodeAffineUnaryTriplePayloadRowFamily,
        encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed,
        validityRowUnifiedAffineSeed] using ih

/-- Concrete output of the single-source affine stage.  Every row contains
all fixed halted/tail values, an internal marker, the untouched compact
one-hot payload, and its outer row marker. -/
noncomputable def verifierValidityRowUnifiedOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTriplePayloadRowOutputFamily
    (arithmeticValidityRowFixedOperandForms W.machine.tm)
    (verifierValidityRowUnifiedPayloadRows W input)

/-- Exact semantic row layout of the unified source. -/
theorem verifierValidityRowUnifiedOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowUnifiedOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
          ([ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
             seed.rowBase,
             arithmeticNoneLabelWire W.machine.tm seed.rowBase,
             0 ] ++
            arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase) ++
        [.frameEnd] ++
        encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFrames W.machine.tm seed) ++
        [.frameEnd] := by
  unfold verifierValidityRowUnifiedOperandPayloadFrames
    verifierValidityRowUnifiedPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, List.flatMap_cons,
        affineUnaryTriplePayloadRowOutputFamily,
        affineUnaryTriplePayloadRowOutput]
      rw [arithmeticValidityRowFixedOperandForms_eq, ih]

/-- The unified row packets are compiled from the original verifier word by
one honest source pipeline; no fan-out or oracle-side zip is used. -/
noncomputable def
    verifierValidityRowUnifiedOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowUnifiedOperandPayloadFrames W) := by
  let seedSource :=
    verifierValidityRowSeedMarkedOneHotStructuredSeeds_computableInPolyTime W
  let typedSeedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowUnifiedPayloadFamily W) :=
    { tm := seedSource.tm
      inputAlphabet := seedSource.inputAlphabet
      outputAlphabet := seedSource.outputAlphabet
      time := seedSource.time
      outputsFun := fun input => by
        rw [verifierValidityRowUnifiedPayloadFamily_encoding_eq]
        simpa only [id_eq,
          verifierValidityRowSeedMarkedOneHotFrames] using
            seedSource.outputsFun input }
  let affineSource := affineUnaryTriplePayloadFamily_computableInPolyTime
    (arithmeticValidityRowFixedOperandForms W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedSeedSource affineSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      affineUnaryTriplePayloadRowOutputFamily
        (arithmeticValidityRowFixedOperandForms W.machine.tm)
        (verifierValidityRowUnifiedPayloadRows W input))
  simpa [Function.comp_def, verifierValidityRowUnifiedPayloadFamily] using
    Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin


