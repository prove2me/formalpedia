-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part8
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:35:37.793082+00:00
-- url     : https://prove2.me/theorems/9637d171-b091-4898-87b9-a0082e243ee1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part8
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part7
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Route the two physical copies to their row-local consumers -/

/-- Typed duplicated-row domain for the fixed verifier operand table.  The
first component is the complete fixed halted/tail prefix and the second is
the compact one-hot payload retained byte-for-byte. -/
noncomputable def verifierValidityRowDuplicatedRouteFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    UnaryFrameDuplicatedRowRouteFamily
      (arithmeticValidityRowFixedOperandForms W.machine.tm).length :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      (arithmeticValidityRowFixedOperandValues W.machine.tm
          seed.height seed.start seed.rowBase,
        encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFrames W.machine.tm seed))
    prefix_lengths := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      rw [arithmeticValidityRowFixedOperandValues_length,
        arithmeticValidityRowFixedOperandDelimiters_length]
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol }

/-- The typed router input is exactly the already compiled duplicated stream. -/
theorem verifierValidityRowDuplicatedRouteFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameDuplicatedRowRouteInput
        (verifierValidityRowDuplicatedRouteFamily W input) =
      verifierValidityRowDuplicatedPlainOperandPayloadFrames W input := by
  rw [verifierValidityRowDuplicatedPlainOperandPayloadFrames_eq_rows]
  unfold encodeUnaryFrameDuplicatedRowRouteInput
    verifierValidityRowDuplicatedRouteFamily
  rw [List.flatMap_map]

/-- Routed row packets: the first copy contributes only its compact one-hot
payload, while the second copy retains the complete fixed operand prefix and
the same compact payload. -/
noncomputable def verifierValidityRowRoutedOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDuplicatedRowRoute
    (arithmeticValidityRowFixedOperandForms W.machine.tm).length
    (verifierValidityRowDuplicatedPlainOperandPayloadFrames W input)

/-- Exact byte layout after routing the two physical copies. -/
theorem verifierValidityRowRoutedOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowRoutedOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (arithmeticValidityRowFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase) ++
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierValidityRowRoutedOperandPayloadFrames
  rw [← verifierValidityRowDuplicatedRouteFamily_encoding_eq]
  rw [rewriteUnaryFrameDuplicatedRowRoute_family]
  · unfold encodeUnaryFrameDuplicatedRowRouteOutput
      verifierValidityRowDuplicatedRouteFamily
    rw [List.flatMap_map]
  · simp [arithmeticValidityRowFixedOperandForms]

/-- One fixed polynomial-time pipeline computes the routed row packets from
the original verifier word. -/
noncomputable def
    verifierValidityRowRoutedOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowRoutedOperandPayloadFrames W) := by
  let duplicatedSource :=
    verifierValidityRowDuplicatedPlainOperandPayloadFrames_computableInPolyTime W
  let router := unaryFrameDuplicatedRowRoute_computableInPolyTime
    (arithmeticValidityRowFixedOperandForms W.machine.tm).length
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      duplicatedSource router
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameDuplicatedRowRoute
        (arithmeticValidityRowFixedOperandForms W.machine.tm).length
        (verifierValidityRowDuplicatedPlainOperandPayloadFrames W input))
  simpa [Function.comp_def] using Classical.choice composed
end CLRS.Chapter34.Turing.CookLevin


