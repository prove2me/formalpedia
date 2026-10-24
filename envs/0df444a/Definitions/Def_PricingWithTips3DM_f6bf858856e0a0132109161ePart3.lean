-- Prove2me | Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161ePart3
-- name    : PricingWithTips3DM_f6bf858856e0a0132109161ePart3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:33:56.32538+00:00
-- url     : https://prove2.me/theorems/bb266b07-6dae-433b-a7ac-06fced835f44
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeGuardedKeysTM2.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_f6bf858856e0a0132109161ePart2

noncomputable section

namespace PricingWithTips.FixedShapeGuardedKeysTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open PricingWithTips.FixedShapeOccurrenceKeysTM2
open PricingWithTips.FixedShapeLiteralKeySemantics
open _root_.Turing

def guardedBaseKeyStream (input : List CNFSym) : List CliqueSym :=
  (guardedCanonicalKeys input).flatMap encodeCliqueEdge

theorem gate_flaggedKeyInput (input : List CNFSym) :
    gate (flaggedKeyInput input) = guardedBaseKeyStream input := by
  rw [flaggedKeyInput, canonicalFlagStream, canonicalThreeCNFFlag_eq]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  rw [gate_flag]
  by_cases h : IsThreeCNF (decodeCNF input)
  · have hb : isThreeCNFBool (decodeCNF input) = true :=
      (isThreeCNFBool_eq_true _).2 h
    simp [h, hb, guardedBaseKeyStream, guardedCanonicalKeys,
      canonicalOccurrenceKeyStream]
  · have hb : isThreeCNFBool (decodeCNF input) = false := by
      cases he : isThreeCNFBool (decodeCNF input)
      · rfl
      · exact False.elim (h ((isThreeCNFBool_eq_true _).1 he))
    simp [h, hb, guardedBaseKeyStream, guardedCanonicalKeys,
      canonicalOccurrenceKeyStream]

/-- End-to-end native generation of exactly the guarded base literal keys. -/
noncomputable def guardedBaseKeyStream_computableInPolyTime :
    TM2ComputableInPolyTime id id guardedBaseKeyStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    flaggedKeyInput_computableInPolyTime gate_computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simp only [Function.comp_apply, id_eq] at output
        rw [gate_flaggedKeyInput] at output
        exact output }
end PricingWithTips.FixedShapeGuardedKeysTM2


