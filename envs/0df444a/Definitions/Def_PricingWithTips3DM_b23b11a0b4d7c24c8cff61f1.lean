-- Prove2me | Definitions.Def_PricingWithTips3DM_b23b11a0b4d7c24c8cff61f1
-- name    : PricingWithTips3DM_b23b11a0b4d7c24c8cff61f1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:51:42.044269+00:00
-- url     : https://prove2.me/theorems/1dba60ea-660d-4940-a85b-d924802555cc
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailQuotedForms
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_f627e6e08a4b59ba4a2206e2
import Definitions.Def_PricingWithTips3DM_16b21fe714c3028ac94dcaf3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Affine form tables for delimiter-safe transition tails

Every selected tail fragment is emitted directly in two-symbol quotation.
The suffix's final field is the only exception: it remains one literal
`frameEnd`, serving as the outer boundary of the complete transition row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Suffix fields before the outer local-row terminator. -/
noncomputable def transitionTailSuffixInnerPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionZeroForm ::
    transitionTailPhaseLiftForms (transitionFinalAndInvocationForms tm)

/-- Suffix delimiters before the outer local-row terminator. -/
def transitionTailSuffixInnerPhaseDelimiters
    (_tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  [.tick] ++ transitionFinalAndInvocationDelimiterTable

/-- Fully quoted narrowing-prefix form table. -/
noncomputable def transitionTailQuotedPrefixPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  quoteAffineUnaryTripleForms (transitionTailPrefixPhaseForms tm)

def transitionTailQuotedPrefixPhaseDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  quoteFixedDelimiterTable (transitionTailPrefixPhaseDelimiters tm)

/-- Quoted equality-to-AND suffix followed by one literal outer boundary
field. -/
noncomputable def transitionTailQuotedSuffixPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  quoteAffineUnaryTripleForms (transitionTailSuffixInnerPhaseForms tm) ++
    [affineUnaryTripleZeroForm]

def transitionTailQuotedSuffixPhaseDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  quoteFixedDelimiterTable
      (transitionTailSuffixInnerPhaseDelimiters tm) ++ [.frameEnd]

/-- Fully quoted ordinary equality-frame form table. -/
noncomputable def transitionTailQuotedEqPhaseForms :
    List AffineUnaryTripleForm :=
  quoteAffineUnaryTripleForms transitionEqInvocationForms

def transitionTailQuotedEqPhaseDelimiters : List UnaryFrameSym :=
  quoteFixedDelimiterTable transitionEqInvocationDelimiterTable

@[simp] theorem transitionTailSuffixInnerPhase_lengths
    (tm : _root_.Turing.FinTM2) :
    (transitionTailSuffixInnerPhaseForms tm).length =
      (transitionTailSuffixInnerPhaseDelimiters tm).length := by
  simp [transitionTailSuffixInnerPhaseForms,
    transitionTailSuffixInnerPhaseDelimiters,
    transitionTailPhaseLiftForms,
    transitionFinalAndInvocationForms,
    transitionFinalAndInvocationDelimiterTable]

@[simp] theorem transitionTailQuotedPrefixPhase_lengths
    (tm : _root_.Turing.FinTM2) :
    (transitionTailQuotedPrefixPhaseForms tm).length =
      (transitionTailQuotedPrefixPhaseDelimiters tm).length := by
  simp [transitionTailQuotedPrefixPhaseForms,
    transitionTailQuotedPrefixPhaseDelimiters]

@[simp] theorem transitionTailQuotedSuffixPhase_lengths
    (tm : _root_.Turing.FinTM2) :
    (transitionTailQuotedSuffixPhaseForms tm).length =
      (transitionTailQuotedSuffixPhaseDelimiters tm).length := by
  simp [transitionTailQuotedSuffixPhaseForms,
    transitionTailQuotedSuffixPhaseDelimiters]

@[simp] theorem transitionTailQuotedEqPhase_lengths :
    transitionTailQuotedEqPhaseForms.length =
      transitionTailQuotedEqPhaseDelimiters.length := by
  simp [transitionTailQuotedEqPhaseForms,
    transitionTailQuotedEqPhaseDelimiters,
    transitionEqInvocationForms, transitionEqInvocationDelimiterTable]

theorem transitionTailQuotedPrefixPhase_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailQuotedPrefixPhaseForms tm)
        coordinate =
      quoteAffineUnaryValues
        (affineUnaryTripleMap (transitionTailPrefixPhaseForms tm)
          coordinate) := by
  exact affineUnaryTripleMap_quoteForms _ _

theorem transitionTailQuotedSuffixPhase_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailQuotedSuffixPhaseForms tm)
        coordinate =
      quoteAffineUnaryValues
          (affineUnaryTripleMap
            (transitionTailSuffixInnerPhaseForms tm) coordinate) ++ [0] := by
  unfold transitionTailQuotedSuffixPhaseForms affineUnaryTripleMap
  rw [List.map_append]
  simp only [List.map_singleton, affineUnaryTripleZeroForm_value]
  rw [show List.map (fun form => affineUnaryTripleFormValue form coordinate)
          (quoteAffineUnaryTripleForms
            (transitionTailSuffixInnerPhaseForms tm)) =
        quoteAffineUnaryValues
          (List.map (fun form => affineUnaryTripleFormValue form coordinate)
            (transitionTailSuffixInnerPhaseForms tm)) by
    simpa only [affineUnaryTripleMap] using
      affineUnaryTripleMap_quoteForms
        (transitionTailSuffixInnerPhaseForms tm) coordinate]

theorem transitionTailQuotedEqPhase_value
    (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap transitionTailQuotedEqPhaseForms coordinate =
      quoteAffineUnaryValues
        (affineUnaryTripleMap transitionEqInvocationForms coordinate) := by
  exact affineUnaryTripleMap_quoteForms _ _

end CLRS.Chapter34.Turing.CookLevin


