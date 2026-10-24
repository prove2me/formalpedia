-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part3
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:37:49.483006+00:00
-- url     : https://prove2.me/theorems/4a416aad-9f41-4d58-80d4-287e6ec274a6
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every semantic fixed row has the verifier-fixed delimiter-table length. -/
theorem arithmeticValidityTailFixedOperandValues_length
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    (arithmeticValidityTailFixedOperandValues tm H start rowBase).length =
      (arithmeticValidityTailFixedOperandDelimiters tm).length := by
  rw [← arithmeticValidityTailFixedOperandForms_eq tm H start rowBase]
  simp [affineUnaryTripleMap,
    arithmeticValidityTailFixedOperandDelimiters_length]

/-- Fixed stack and final-prefix delimiters are now materialized in every
row, while the one-hot invocation payload remains byte-for-byte unchanged. -/
noncomputable def verifierValidityRowTailSplicedSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixSplice
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
    (verifierValidityRowTailAffinePayloadFrames W input)

/-- Exact row-major splice semantics at the Cook--Levin specialization. -/
theorem verifierValidityRowTailSplicedSourceFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailSplicedSourceFrames W input =
      encodeUnaryFrameFixedPrefixSpliceOutputFamily
        (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
        (fun seed : ValidityRowSeed =>
          arithmeticValidityTailFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneOutputSourceInvocationFamily
            (validityRowSeedOneHotFrames W.machine.tm seed).reverse)
        (verifierValidityRowSeeds W input) := by
  unfold verifierValidityRowTailSplicedSourceFrames
  rw [verifierValidityRowTailAffinePayloadFrames_eq_spliceInput]
  apply rewriteUnaryFrameFixedPrefixSplice_family
  · intro seed
    exact arithmeticValidityTailFixedOperandValues_length
      W.machine.tm seed.height seed.start seed.rowBase
  · intro seed symbol hsymbol
    exact affineExactlyOneOutputInvocationFamily_no_frameEnd _ symbol hsymbol

/-- End-to-end polynomial-time construction of the delimiter-bearing compact
validity-tail source rows from the raw verifier input. -/
noncomputable def
    verifierValidityRowTailSplicedSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailSplicedSourceFrames W) := by
  let affineSource :=
    verifierValidityRowTailAffinePayloadFrames_computableInPolyTime W
  let spliceSource := unaryFrameFixedPrefixSplice_computableInPolyTime
    (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineSource spliceSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameFixedPrefixSplice
        (arithmeticValidityTailFixedOperandDelimiters W.machine.tm)
        (verifierValidityRowTailAffinePayloadFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Identification with the established compact tail source -/

theorem encodeUnaryFrameWithFixedDelimiters_append
    (left right : List Nat) (leftDelimiters rightDelimiters :
      List UnaryFrameSym)
    (hlength : left.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (left ++ right)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters left leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters right rightDelimiters := by
  induction left generalizing leftDelimiters with
  | nil =>
      cases leftDelimiters with
      | nil => rfl
      | cons delimiter delimiters => simp at hlength
  | cons value values ih =>
      cases leftDelimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          have hlength' : values.length = delimiters.length :=
            Nat.add_right_cancel hlength
          simp [encodeUnaryFrameWithFixedDelimiters,
            ih delimiters hlength', List.append_assoc]

/-- The eight fixed values and delimiters of one arithmetic stack are
byte-for-byte its established standalone compact invocation. -/
theorem arithmeticValidityTailStackFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    let seed := arithmeticRuntimeStackSourceSeed tm H start rowBase k
    encodeUnaryFrameWithFixedDelimiters
        [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
          seed.maskStart, seed.maskBase + seed.count, 0, seed.count]
        arithmeticValidityTailStackOperandDelimiters =
      encodeAffineRuntimeStackStandaloneInvocation seed := by
  simp [arithmeticValidityTailStackOperandDelimiters,
    encodeUnaryFrameWithFixedDelimiters,
    encodeAffineRuntimeStackStandaloneInvocation,
    encodeAffineRuntimeStackSourceInvocation, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

/-- Materializing all fixed stack fields yields exactly the established
canonical stack-family source invocation. -/
theorem arithmeticValidityTailStackFamilyFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    encodeUnaryFrameWithFixedDelimiters
        ((arithmeticRuntimeStackSourceSeeds tm H start rowBase).flatMap
          fun seed =>
            [seed.cellRight, seed.cellLeft, seed.cellBlank, seed.count,
              seed.maskStart, seed.maskBase + seed.count, 0, seed.count])
        ((arithmeticRuntimeStackSourceIndices tm).flatMap fun _ =>
          arithmeticValidityTailStackOperandDelimiters) =
      encodeAffineRuntimeStackStandaloneInvocationFamily
        (arithmeticRuntimeStackSourceSeeds tm H start rowBase) := by
  unfold arithmeticRuntimeStackSourceSeeds
  generalize arithmeticRuntimeStackSourceIndices tm = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.map_cons, List.flatMap_cons,
        encodeAffineRuntimeStackStandaloneInvocationFamily]
      rw [encodeUnaryFrameWithFixedDelimiters_append]
      · rw [arithmeticValidityTailStackFixedEncoding_eq, ih]
      · simp [arithmeticValidityTailStackOperandDelimiters]

/-- The four final fixed values are exactly the fixed prefix of the existing
final-conjunction compact invocation. -/
theorem arithmeticValidityTailFinalPrefixFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (H start : Nat) :
    encodeUnaryFrameWithFixedDelimiters
        [ arithmeticValidityFinalStart tm H start,
          H,
          arithmeticStackValidityStart tm H start,
          arithmeticHaltedMatchStart tm H start + 4 ]
        arithmeticValidityTailFinalPrefixDelimiters =
      encodeUnaryFrameBlock (arithmeticValidityFinalStart tm H start) ++
        encodeAffineStackOutputSourceInvocation
          { height := H
            base := arithmeticStackValidityStart tm H start } ++
        encodeUnaryFrameBlock
          (arithmeticHaltedMatchStart tm H start + 4) := by
  simp [arithmeticValidityTailFinalPrefixDelimiters,
    encodeUnaryFrameWithFixedDelimiters,
    encodeAffineStackOutputSourceInvocation, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.append_assoc]

/-- One fully spliced arithmetic row is exactly the compact invocation
consumed by the already verified continuous validity-tail source. -/
theorem arithmeticValidityTailSplicedRow_eq_sourceInvocation
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    encodeUnaryFrameWithFixedDelimiters
          (arithmeticValidityTailFixedOperandValues tm H start rowBase)
          (arithmeticValidityTailFixedOperandDelimiters tm) ++
        encodeAffineExactlyOneOutputSourceInvocationFamily
            (arithmeticRawOneHotFrames tm H start rowBase).reverse ++
          [.frameEnd] =
      encodeAffineValidityTailSourceInvocation
        (arithmeticValidityTailSourceFrame tm H start rowBase) := by
  unfold arithmeticValidityTailFixedOperandValues
    arithmeticValidityTailFixedOperandDelimiters
  rw [encodeUnaryFrameWithFixedDelimiters_append]
  · rw [arithmeticValidityTailStackFamilyFixedEncoding_eq,
      arithmeticValidityTailFinalPrefixFixedEncoding_eq]
    simp [encodeAffineValidityTailSourceInvocation,
      arithmeticValidityTailSourceFrame,
      arithmeticValidityFinalConjunctionSourceFrame,
      encodeAffineValidityFinalConjunctionSourceInvocation,
      List.append_assoc]
  · unfold arithmeticRuntimeStackSourceSeeds
    generalize arithmeticRuntimeStackSourceIndices tm = indices
    induction indices with
    | nil => rfl
    | cons index rest ih =>
        simp [arithmeticValidityTailStackOperandDelimiters, ih]
end CLRS.Chapter34.Turing.CookLevin


