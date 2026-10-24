-- Prove2me | Definitions.Def_PricingWithTips3DM_0113804d1513567e5f178f47
-- name    : PricingWithTips3DM_0113804d1513567e5f178f47
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:42:59.011297+00:00
-- url     : https://prove2.me/theorems/76929aac-302a-4a62-a732-d33512da2f66
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeBaselineTM2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_0dd2a1f65dab48349fe246d7
import Definitions.Def_PricingWithTips3DM_6610522946c1bb61b9f5e9c8
import Definitions.Def_PricingWithTips3DM_8169be64da1591889851249c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Native TM2 construction for the exact fixed-shape framing and cubic clock. -/

noncomputable section

namespace PricingWithTips.FixedShapeBaselineTM2

open CLRS.Chapter34.Turing.PolyBuilder
open PricingWithTips.FixedShape3DM

def dimensionPolynomial : Polynomial ℕ :=
  2 * Polynomial.X * (Polynomial.X + 1)

@[simp] theorem dimensionPolynomial_eval (n : ℕ) :
    dimensionPolynomial.eval n = (n + 1) * (n * 2) := by
  simp [dimensionPolynomial]
  ring

def tablePolynomial : Polynomial ℕ := dimensionPolynomial ^ 3

@[simp] theorem tablePolynomial_eval (n : ℕ) :
    tablePolynomial.eval n = ((n + 1) * (n * 2)) ^ 3 := by
  simp [tablePolynomial]

def prefixBitBody : LoopBody UnaryFrameSym Bool where
  emit
    | .tick => [true]
    | .separator => [false]
    | .frameEnd => [false]
  cost := fun _ => 1
  emit_length_le_cost := by intro s; cases s <;> simp

@[simp] theorem prefixBitBody_tick :
    prefixBitBody.emit .tick = [true] := rfl

@[simp] theorem prefixBitBody_separator :
    prefixBitBody.emit .separator = [false] := rfl

def prefixBits (input : List CLRS.Chapter34.CNFSym) : List Bool :=
  (exactPolynomialUnaryFrame dimensionPolynomial input).flatMap
    prefixBitBody.emit

theorem flatMap_prefix_ticks (n : ℕ) :
    (List.replicate n UnaryFrameSym.tick).flatMap prefixBitBody.emit =
      List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem prefixBits_eq (input : List CLRS.Chapter34.CNFSym) :
    prefixBits input = List.replicate (dimension input) true ++ [false] := by
  rw [prefixBits]
  change (encodeUnaryFrameBlock
      (dimensionPolynomial.eval input.length)).flatMap prefixBitBody.emit = _
  rw [dimensionPolynomial_eval]
  change (List.replicate ((input.length + 1) * (input.length * 2))
      UnaryFrameSym.tick ++ [UnaryFrameSym.separator]).flatMap prefixBitBody.emit = _
  rw [List.flatMap_append, flatMap_prefix_ticks]
  rfl

def falseBitBody : LoopBody Unit Bool where
  emit _ := [false]
  cost _ := 1
  emit_length_le_cost _ := by simp

def tableBits (input : List CLRS.Chapter34.CNFSym) : List Bool :=
  (exactPolynomialClock tablePolynomial input).flatMap falseBitBody.emit

theorem flatMap_false_bits {α : Type} (l : List α) :
    l.flatMap (fun _ => [false]) = List.replicate l.length false := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.replicate_succ, ih]

theorem tableBits_eq (input : List CLRS.Chapter34.CNFSym) :
    tableBits input = List.replicate (dimension input ^ 3) false := by
  rw [tableBits]
  change (exactPolynomialClock tablePolynomial input).flatMap
      (fun _ => [false]) = _
  rw [flatMap_false_bits, exactPolynomialClock_length, tablePolynomial_eval]
  rfl

def baseline (input : List CLRS.Chapter34.CNFSym) : List Bool :=
  prefixBits input ++ tableBits input

theorem baseline_eq (input : List CLRS.Chapter34.CNFSym) :
    baseline input = List.replicate (dimension input) true ++ [false] ++
      List.replicate (dimension input ^ 3) false := by
  rw [baseline, prefixBits_eq, tableBits_eq, List.append_assoc]

def boolPairEncode : Bool → UnaryFrameSym × UnaryFrameSym
  | false => (.tick, .tick)
  | true => (.tick, .separator)

def boolPairDecode : UnaryFrameSym → UnaryFrameSym → Bool
  | .tick, .separator => true
  | _, _ => false

theorem boolPair_leftInverse (b : Bool) :
    boolPairDecode (boolPairEncode b).1 (boolPairEncode b).2 = b := by
  cases b <;> rfl

noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime
      (id : List CLRS.Chapter34.CNFSym → List CLRS.Chapter34.CNFSym)
      id baseline := by
  let prefixFrames :=
    exactPolynomialUnaryFrame_computableInPolyTime
      (Γ := CLRS.Chapter34.CNFSym) dimensionPolynomial
  let prefixMappedExists :=
    Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch prefixFrames
      (boundedLoop_computableInPolyTime prefixBitBody)
  let prefixMapped := Classical.choice prefixMappedExists
  let tableClock := exactPolynomialClock_computableInPolyTime
    (Γ := CLRS.Chapter34.CNFSym) tablePolynomial
  let tableMappedExists :=
    Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch tableClock
      (boundedLoop_computableInPolyTime falseBitBody)
  let tableMapped := Classical.choice tableMappedExists
  exact fixedPairSameInputConcat_computableInPolyTime
    boolPairEncode boolPairDecode boolPair_leftInverse
    prefixMapped tableMapped

end PricingWithTips.FixedShapeBaselineTM2


