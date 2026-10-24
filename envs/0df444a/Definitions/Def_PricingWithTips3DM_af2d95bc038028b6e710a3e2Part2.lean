-- Prove2me | Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part2
-- name    : PricingWithTips3DM_af2d95bc038028b6e710a3e2Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:25:26.152991+00:00
-- url     : https://prove2.me/theorems/eca0a33c-04fc-46bd-8f43-320399961ea3
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_af2d95bc038028b6e710a3e2Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Single-source fixed operands with compact one-hot payload -/

/-- Runtime row seed in the generic affine source's field order. -/
def validityRowUnifiedAffineSeed
    (height start rowBase : Nat) : AffineUnaryTripleSeed :=
  { first := height, second := start, third := rowBase }

/-- The halted triple followed by every verifier-fixed tail operand form.
All coefficients depend only on the fixed verifier machine. -/
noncomputable def arithmeticValidityRowFixedOperandForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  [ { constant := arithmeticRawOneHotGateCountConstant tm
      first := arithmeticRawOneHotGateCountHeightCoeff tm
      second := 1
      third := 0 },
    { constant := 0, first := 0, second := 0, third := 1 },
    { constant := labelCount tm + 1
      first := 0
      second := 0
      third := 1 },
    { constant := 0, first := 0, second := 0, third := 0 } ] ++
    arithmeticValidityTailFixedOperandForms tm

/-- The unified affine table is value-exact for the halted fields and the
complete fixed part of the canonical tail invocation. -/
theorem arithmeticValidityRowFixedOperandForms_eq
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityRowFixedOperandForms tm)
        (validityRowUnifiedAffineSeed height start rowBase) =
      [ arithmeticHaltedMatchStart tm height start,
        rowBase,
        arithmeticNoneLabelWire tm rowBase,
        0 ] ++
        arithmeticValidityTailFixedOperandValues
          tm height start rowBase := by
  unfold arithmeticValidityRowFixedOperandForms
  rw [show affineUnaryTripleMap
      ([ { constant := arithmeticRawOneHotGateCountConstant tm
           first := arithmeticRawOneHotGateCountHeightCoeff tm
           second := 1
           third := 0 },
         { constant := 0, first := 0, second := 0, third := 1 },
         { constant := labelCount tm + 1
           first := 0
           second := 0
           third := 1 },
         { constant := 0, first := 0, second := 0, third := 0 } ] ++
        arithmeticValidityTailFixedOperandForms tm)
        (validityRowUnifiedAffineSeed height start rowBase) =
      affineUnaryTripleMap
          [ { constant := arithmeticRawOneHotGateCountConstant tm
              first := arithmeticRawOneHotGateCountHeightCoeff tm
              second := 1
              third := 0 },
            { constant := 0, first := 0, second := 0, third := 1 },
            { constant := labelCount tm + 1
              first := 0
              second := 0
              third := 1 },
            { constant := 0, first := 0, second := 0, third := 0 } ]
          (validityRowUnifiedAffineSeed height start rowBase) ++
        affineUnaryTripleMap (arithmeticValidityTailFixedOperandForms tm)
          (validityRowUnifiedAffineSeed height start rowBase) by
    simp [affineUnaryTripleMap]]
  rw [show affineUnaryTripleMap
        [ { constant := arithmeticRawOneHotGateCountConstant tm
            first := arithmeticRawOneHotGateCountHeightCoeff tm
            second := 1
            third := 0 },
          { constant := 0, first := 0, second := 0, third := 1 },
          { constant := labelCount tm + 1
            first := 0
            second := 0
            third := 1 },
          { constant := 0, first := 0, second := 0, third := 0 } ]
        (validityRowUnifiedAffineSeed height start rowBase) =
      [ arithmeticHaltedMatchStart tm height start,
        rowBase,
        arithmeticNoneLabelWire tm rowBase,
        0 ] by
    simp [affineUnaryTripleMap, affineUnaryTripleFormValue,
      validityRowUnifiedAffineSeed, arithmeticHaltedMatchStart,
      arithmeticNoneLabelWire,
      arithmeticRawOneHotGateCount_eq_affine]
    ring_nf
    simp]
  congr 1
  have h := arithmeticValidityTailFixedOperandForms_eq
    tm height start rowBase
  change affineUnaryTripleMap (arithmeticValidityTailFixedOperandForms tm)
      { first := height, second := start, third := rowBase } =
    arithmeticValidityTailFixedOperandValues tm height start rowBase at h
  simpa [validityRowUnifiedAffineSeed] using h
end CLRS.Chapter34.Turing.CookLevin


