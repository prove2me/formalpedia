-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part13
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part13
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:51:06.406699+00:00
-- url     : https://prove2.me/theorems/ac4f4042-1760-46c0-b12f-106df93ab84a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part13
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part12
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Expand every compact tail behind its canonical row prefixes -/

/-- Typed view of the compact row stream consumed by the continuous
prefix-preserving validity-tail source. -/
noncomputable def verifierValidityRowPrefixedTailSourceFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AffineValidityTailPrefixedSourceFamily
      (arithmeticRuntimeStackSourceBlankSteps W.machine.tm) :=
  { rows := (verifierValidityRowSeeds W input).map fun seed =>
      { first := .tick :: encodeAffineExactlyOneFamily
          (validityRowSeedOneHotFrames W.machine.tm seed)
        second := encodeUnaryFrame
          [ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
            seed.rowBase,
            arithmeticNoneLabelWire W.machine.tm seed.rowBase ]
        tail := arithmeticValidityTailSourceFrame W.machine.tm
          seed.height seed.start seed.rowBase }
    first_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      simp only [List.mem_cons] at hsymbol
      rcases hsymbol with rfl | hfamily
      · simp
      · exact inputCompiler_exactlyOneFamily_no_frameEnd _ symbol hfamily
    second_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hsymbol
    stack_lengths := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact arithmeticRuntimeStackSourceSeeds_length
        W.machine.tm seed.height seed.start seed.rowBase }

/-- Retyping the compact raw-input result loses no bytes: it is exactly the
generic prefixed-tail family input. -/
theorem verifierValidityRowPrefixedTailSourceFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineValidityTailPrefixedSourceInput
        (verifierValidityRowPrefixedTailSourceFamily W input) =
      verifierValidityRowCompactSourceFrames W input := by
  rw [verifierValidityRowCompactSourceFrames_eq_invocations]
  unfold encodeAffineValidityTailPrefixedSourceInput
    verifierValidityRowPrefixedTailSourceFamily
  rw [List.flatMap_map]
  simp [List.append_assoc]
end CLRS.Chapter34.Turing.CookLevin


