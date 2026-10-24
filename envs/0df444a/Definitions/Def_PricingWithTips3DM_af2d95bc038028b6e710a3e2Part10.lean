-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part10
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part10
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:38:35.811968+00:00
-- url     : https://prove2.me/theorems/20310ddf-f10f-4528-96e2-c72e1f8f8085
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part10
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part9
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Materialize the fixed halted/tail delimiters behind the one-hot prefix -/

theorem inputCompiler_exactlyOneFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction frames with
  | nil => simp [encodeAffineExactlyOneFamily] at hsymbol
  | cons frame rest ih =>
      simp only [encodeAffineExactlyOneFamily, List.mem_append] at hsymbol
      rcases hsymbol with hframe | hrest
      · exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hframe
      · exact ih hrest

/-! ## Project the retained compact copy to output-source invocations -/

/-- Typed verifier specialization of the row-local compact projection.  The
canonical one-hot prefix and every fixed halted/tail operand are preserved;
only the retained compact one-hot copy is projected. -/
noncomputable def verifierValidityRowCompactProjectionFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AffineExactlyOneLeadingFixedCompactProjectionFamily
      (arithmeticValidityRowFixedOperandForms W.machine.tm).length :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      { leading := .tick :: encodeAffineExactlyOneFamily
          (validityRowSeedOneHotFrames W.machine.tm seed)
        fixed := arithmeticValidityRowFixedOperandValues W.machine.tm
          seed.height seed.start seed.rowBase
        frames := validityRowSeedOneHotFrames W.machine.tm seed }
    fixed_lengths := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      rw [arithmeticValidityRowFixedOperandValues_length,
        arithmeticValidityRowFixedOperandDelimiters_length]
    leading_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      simp only [List.mem_cons] at hsymbol
      rcases hsymbol with rfl | hfamily
      · simp
      · exact inputCompiler_exactlyOneFamily_no_frameEnd _ symbol hfamily }

/-- The typed projection input is byte-for-byte the expanded-prefix stream. -/
theorem verifierValidityRowCompactProjectionFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineExactlyOneLeadingFixedCompactProjectionInput
        (verifierValidityRowCompactProjectionFamily W input) =
      verifierValidityRowExpandedPrefixPayloadFrames W input := by
  rw [verifierValidityRowExpandedPrefixPayloadFrames_eq_rows]
  unfold encodeAffineExactlyOneLeadingFixedCompactProjectionInput
    verifierValidityRowCompactProjectionFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- Concrete row stream after the retained compact copy has become the
runtime invocation family for the exactly-one output source. -/
noncomputable def verifierValidityRowProjectedOperandFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
    (verifierValidityRowCompactProjectionFamily W input)

/-- Exact row-major semantics of the projected verifier stream. -/
theorem verifierValidityRowProjectedOperandFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowProjectedOperandFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        .tick ::
          (encodeAffineExactlyOneFamily
              (validityRowSeedOneHotFrames W.machine.tm seed) ++
            .frameEnd ::
              (encodeUnaryFrame
                  (arithmeticValidityRowFixedOperandValues W.machine.tm
                    seed.height seed.start seed.rowBase) ++
                encodeAffineExactlyOneOutputSourceInvocationFamily
                  (validityRowSeedOneHotFrames W.machine.tm seed).reverse ++
                [.frameEnd])) := by
  unfold verifierValidityRowProjectedOperandFrames
    encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
    verifierValidityRowCompactProjectionFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]

/-- The original verifier word polynomially computes the projected row
stream.  This closes the raw-input-to-runtime-invocation bridge for every
one-hot subfamily in the validity rows. -/
noncomputable def
    verifierValidityRowProjectedOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowProjectedOperandFrames W) := by
  let expandedSource :=
    verifierValidityRowExpandedPrefixPayloadFrames_computableInPolyTime W
  let typedExpandedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineExactlyOneLeadingFixedCompactProjectionInput
        (verifierValidityRowCompactProjectionFamily W) :=
    { tm := expandedSource.tm
      inputAlphabet := expandedSource.inputAlphabet
      outputAlphabet := expandedSource.outputAlphabet
      time := expandedSource.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowCompactProjectionFamily_encoding_eq W input]
          using expandedSource.outputsFun input }
  let projector :=
    affineExactlyOneLeadingFixedCompactProjection_computableInPolyTime
      (arithmeticValidityRowFixedOperandForms W.machine.tm).length
      (by simp [arithmeticValidityRowFixedOperandForms])
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedExpandedSource projector
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
        (verifierValidityRowCompactProjectionFamily W input))
  simpa [Function.comp_def] using Classical.choice composed

theorem
    inputCompiler_outputInvocationFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneOutputSourceInvocationFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeAffineExactlyOneOutputSourceInvocationFamily,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨frame, hframe, hsymbol⟩
  rw [encodeAffineExactlyOneOutputSourceInvocation, encodeUnaryFrame,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with ⟨_, rfl⟩ | rfl <;> simp
end CLRS.Chapter34.Turing.CookLevin


