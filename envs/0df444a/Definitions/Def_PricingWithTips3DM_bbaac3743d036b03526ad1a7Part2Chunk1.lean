-- Prove2me | Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk1
-- name    : PricingWithTips3DM_bbaac3743d036b03526ad1a7Part2Chunk1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T22:00:46.695615+00:00
-- url     : https://prove2.me/theorems/cc92dc05-0ed8-42d7-a728-053a36e66ad1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource.Part2.Chunk1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bbaac3743d036b03526ad1a7Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Fixed invocation delimiters -/

/-- Delimiter layout of one standalone runtime-stack invocation.  The
seventh zero field materializes the header boundary; the eighth height field
is the runtime payload terminated by the outer stack boundary. -/
def arithmeticValidityTailStackOperandDelimiters : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator,
    .separator, .separator, .frameEnd, .frameEnd]

/-- The four fixed final-conjunction prefix operands remain ordinary unary
blocks; the variable one-hot family follows them in the next source layer. -/
def arithmeticValidityTailFinalPrefixDelimiters : List UnaryFrameSym :=
  [.separator, .separator, .separator, .separator]

/-- One complete cyclic delimiter table for the fixed part of a validity-tail
row: one eight-field stack invocation per fixed machine stack, then the four
final-conjunction prefix fields. -/
def arithmeticValidityTailFixedOperandDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  ((arithmeticRuntimeStackSourceIndices tm).flatMap fun _ =>
      arithmeticValidityTailStackOperandDelimiters) ++
    arithmeticValidityTailFinalPrefixDelimiters

@[simp] theorem arithmeticValidityTailFixedOperandDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (arithmeticValidityTailFixedOperandDelimiters tm).length := by
  simp [arithmeticValidityTailFixedOperandDelimiters,
    arithmeticValidityTailFinalPrefixDelimiters]

/-- The delimiter table has exactly one entry for every fixed affine form. -/
theorem arithmeticValidityTailFixedOperandDelimiters_length
    (tm : _root_.Turing.FinTM2) :
    (arithmeticValidityTailFixedOperandDelimiters tm).length =
      (arithmeticValidityTailFixedOperandForms tm).length := by
  simp [arithmeticValidityTailFixedOperandDelimiters,
    arithmeticValidityTailStackOperandDelimiters,
    arithmeticValidityTailFinalPrefixDelimiters,
    arithmeticValidityTailFixedOperandForms,
    arithmeticValidityTailStackOperandFormsFamily,
    arithmeticValidityTailStackOperandForms,
    arithmeticValidityTailFinalPrefixForms, affineValidityForm]
end CLRS.Chapter34.Turing.CookLevin


