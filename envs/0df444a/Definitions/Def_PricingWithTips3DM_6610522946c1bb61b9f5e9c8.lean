-- Prove2me | Definitions.Def_PricingWithTips3DM_6610522946c1bb61b9f5e9c8
-- name    : PricingWithTips3DM_6610522946c1bb61b9f5e9c8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:24:23.6718+00:00
-- url     : https://prove2.me/theorems/dfbd0bdb-2e9a-4f69-a1fb-07c296a201d8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0b2f8d1d07e5b5a6b6ac84b8
import Definitions.Def_PricingWithTips3DM_b4f76447a6d2b46e80bcfdbb
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact polynomial unary frames

The exact polynomial clock produces a token list whose length is a fixed
polynomial in the raw input length.  This module compiles those tokens into
the delimiter-bearing unary representation consumed by the Cook--Levin
runtime controllers.  Every stage is a concrete compiled TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Relabel a clock token as a unary tick and its unique sentinel as the
terminating separator. -/
def unaryFrameSymbolBody : LoopBody (Option Unit) UnaryFrameSym where
  emit
    | some _ => [.tick]
    | none => [.separator]
  cost := fun _ => 1
  emit_length_le_cost := by
    intro symbol
    cases symbol <;> simp

/-- Symbol-local conversion of a sentinel-terminated unit clock into unary
frame symbols. -/
def unaryFrameSymbols (input : List (Option Unit)) : List UnaryFrameSym :=
  input.flatMap unaryFrameSymbolBody.emit

/-- A sentinel-terminated unit clock becomes exactly one self-delimiting
unary block. -/
@[simp] theorem unaryFrameSymbols_sentinelInput (tokens : List Unit) :
    unaryFrameSymbols (sentinelInput tokens) =
      encodeUnaryFrameBlock tokens.length := by
  induction tokens with
  | nil => rfl
  | cons _ tokens ih =>
      change .tick :: unaryFrameSymbols (sentinelInput tokens) =
        List.replicate (tokens.length + 1) .tick ++ [.separator]
      rw [ih]
      simp [encodeUnaryFrameBlock, List.replicate_succ]

/-- The sentinel-to-frame relabeler is one concrete verified bounded-loop
machine. -/
noncomputable def unaryFrameSymbols_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id unaryFrameSymbols := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List (Option Unit) =>
      input.flatMap unaryFrameSymbolBody.emit)
  exact boundedLoop_computableInPolyTime unaryFrameSymbolBody

/-- Unary operand block whose value is a fixed polynomial evaluated at the
raw input length. -/
def exactPolynomialUnaryFrame {Γ : Type} (p : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameBlock (p.eval input.length)

/-- The concrete clock/sentinel/relabel pipeline has exactly the public unary
frame semantics. -/
theorem exactPolynomialUnaryFrame_eq {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) :
    unaryFrameSymbols (sentinelInput (exactPolynomialClock p input)) =
      exactPolynomialUnaryFrame p input := by
  simp [exactPolynomialUnaryFrame]

/-- A fixed compiled TM2 maps the raw source word to the exact unary encoding
of any fixed polynomial in its length. -/
noncomputable def exactPolynomialUnaryFrame_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryFrame Γ p) := by
  let clockThenSentinel :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (exactPolynomialClock_computableInPolyTime (Γ := Γ) p)
      (sentinelInput_computableInPolyTime Unit)
  let full :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice clockThenSentinel)
      unaryFrameSymbols_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ => encodeUnaryFrameBlock (p.eval input.length))
  simpa [Function.comp_def] using Classical.choice full

end CLRS.Chapter34.Turing.PolyBuilder


