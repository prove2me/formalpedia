-- Prove2me | Definitions.Def_PricingWithTips3DM_907e19bdbe7b9bc0babe86ad
-- name    : PricingWithTips3DM_907e19bdbe7b9bc0babe86ad
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T09:01:14.436931+00:00
-- url     : https://prove2.me/theorems/d7a64fa8-d26b-438d-8823-44f347a8f54c
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralKeySemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_847c78c883603fef589ababa
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Semantic bridge from guarded/padded certified literals to the native CLRS
occurrence-key stream used by the batch lookup. -/

namespace PricingWithTips.FixedShapeLiteralKeySemantics

open CLRS.Chapter34
open Hardness Hardness.Cert SatToMatching3DCode
open PricingWithTips.CLRS3CNFBridge
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeOccurrenceKeysTM2

def certifiedLiteralKey (clause : Nat) (literal : Hardness.Literal Nat) :
    Nat × Nat :=
  (clause, 2 * literal.var + bitOf literal.polarity)

def certifiedClauseKeys (clause : Nat) (literals : Hardness.Clause Nat) :
    List (Nat × Nat) :=
  literals.map (certifiedLiteralKey clause)

def certifiedFormulaKeysFrom : Nat → Hardness.CNF Nat → List (Nat × Nat)
  | _, [] => []
  | clause, literals :: formula =>
      certifiedClauseKeys clause literals ++
        certifiedFormulaKeysFrom (clause + 1) formula

def certifiedFormulaKeys (formula : Hardness.CNF Nat) : List (Nat × Nat) :=
  certifiedFormulaKeysFrom 0 formula

def convertLiteral (literal : CLRS.Chapter34.Literal) :
    Hardness.Literal Nat :=
  Hardness.Cert.litOf (certLiteral literal)

def convertFormula (formula : CLRS.Chapter34.CNF) : Hardness.CNF Nat :=
  formula.map (List.map convertLiteral)

@[simp] theorem certifiedLiteralKey_convert (clause : Nat)
    (literal : CLRS.Chapter34.Literal) :
    certifiedLiteralKey clause (convertLiteral literal) =
      literalKey clause literal := by
  cases literal <;> rfl

theorem certifiedFormulaKeysFrom_convert (clause : Nat)
    (formula : CLRS.Chapter34.CNF) :
    certifiedFormulaKeysFrom clause (convertFormula formula) =
      formulaKeysFrom clause formula := by
  induction formula generalizing clause with
  | nil => rfl
  | cons literals formula ih =>
      change certifiedClauseKeys clause (literals.map convertLiteral) ++
          certifiedFormulaKeysFrom (clause + 1) (convertFormula formula) =
        clauseKeys clause literals ++ formulaKeysFrom (clause + 1) formula
      rw [ih]
      congr 1
      simp [certifiedClauseKeys, clauseKeys, List.map_map,
        Function.comp_def, certifiedLiteralKey_convert]

theorem decode_certCNF_eq_convert (formula : CLRS.Chapter34.CNF) :
    Hardness.Cert.decodeCNF (certCNF formula) = convertFormula formula := by
  simp [Hardness.Cert.decodeCNF, certCNF, convertFormula, convertLiteral,
    List.map_map, Function.comp_def]

def guardedCanonicalKeys (input : List CNFSym) : List (Nat × Nat) :=
  if isThreeCNFBool (decodeCNF input) then
    canonicalOccurrenceKeys input
  else []

/-- The certified gadget's guarded base formula has exactly the native
occurrence keys on valid 3-CNF words and no literal keys on invalid words. -/
theorem certifiedFormulaKeys_baseCNF (input : List CNFSym) :
    certifiedFormulaKeys (baseCNF input) = guardedCanonicalKeys input := by
  by_cases h : isThreeCNFBool (decodeCNF input) = true
  · rw [show baseCNF input = convertFormula (decodeCNF input) by
      simp [baseCNF, guardedCertCNF, h, decode_certCNF_eq_convert]]
    simp only [certifiedFormulaKeys, canonicalOccurrenceKeys,
      formulaKeys, guardedCanonicalKeys, h, if_true]
    exact certifiedFormulaKeysFrom_convert 0 (decodeCNF input)
  · have hf : isThreeCNFBool (decodeCNF input) = false := by
      cases he : isThreeCNFBool (decodeCNF input)
      · rfl
      · exact False.elim (h he)
    simp [baseCNF, guardedCertCNF, hf, Hardness.Cert.decodeCNF,
      certifiedFormulaKeys, certifiedFormulaKeysFrom,
      certifiedClauseKeys, guardedCanonicalKeys]

theorem certifiedFormulaKeysFrom_append (start : Nat)
    (left right : Hardness.CNF Nat) :
    certifiedFormulaKeysFrom start (left ++ right) =
      certifiedFormulaKeysFrom start left ++
        certifiedFormulaKeysFrom (start + left.length) right := by
  induction left generalizing start with
  | nil => simp [certifiedFormulaKeysFrom]
  | cons clause left ih =>
      simp only [List.cons_append, certifiedFormulaKeysFrom,
        List.length_cons]
      rw [ih]
      simp [List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

def paddingKeysFrom : Nat → Nat → List (Nat × Nat)
  | _, 0 => []
  | start, count + 1 =>
      [(start, 1), (start, 0)] ++ paddingKeysFrom (start + 1) count

theorem certifiedFormulaKeysFrom_replicate_taut (start count : Nat) :
    certifiedFormulaKeysFrom start (List.replicate count tautClause) =
      paddingKeysFrom start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, certifiedFormulaKeysFrom]
      rw [ih]
      simp [tautClause, certifiedClauseKeys, certifiedLiteralKey, bitOf,
        paddingKeysFrom]

/-- Exact key decomposition of the padded gadget formula. -/
theorem certifiedFormulaKeys_paddedCNF (input : List CNFSym) :
    certifiedFormulaKeys (paddedCNF input) =
      guardedCanonicalKeys input ++
        paddingKeysFrom (baseCNF input).length
          (input.length - (baseCNF input).length) := by
  unfold certifiedFormulaKeys paddedCNF
  rw [certifiedFormulaKeysFrom_append]
  rw [show 0 + (baseCNF input).length = (baseCNF input).length by omega]
  rw [certifiedFormulaKeysFrom_replicate_taut]
  change certifiedFormulaKeys (baseCNF input) ++ _ = _
  rw [certifiedFormulaKeys_baseCNF]

end PricingWithTips.FixedShapeLiteralKeySemantics


