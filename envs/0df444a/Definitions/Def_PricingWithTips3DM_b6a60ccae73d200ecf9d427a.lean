-- Prove2me | Definitions.Def_PricingWithTips3DM_b6a60ccae73d200ecf9d427a
-- name    : PricingWithTips3DM_b6a60ccae73d200ecf9d427a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:28:17.235068+00:00
-- url     : https://prove2.me/theorems/66d5de69-16fd-4b77-be62-58d60583bd0b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FiniteSymbolUnaryFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_3799fd79c9b0b4d68c438353
import Definitions.Def_PricingWithTips3DM_b4f76447a6d2b46e80bcfdbb
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Unary frames for finite-symbol codes

A fixed finite alphabet permits each symbol to carry a fixed natural-number
code in finite control.  The verified bounded-loop macro expands a raw input
word into one self-delimiting unary block per symbol.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Symbol-local expansion into one unary block. -/
def finiteSymbolUnaryFrameBody {Γ : Type} (code : Γ → Nat) :
    LoopBody Γ UnaryFrameSym where
  emit symbol := encodeUnaryFrameBlock (code symbol)
  cost symbol := code symbol + 1
  emit_length_le_cost symbol := by
    simp [encodeUnaryFrameBlock]

/-- Concatenated unary code blocks for a raw finite-alphabet word. -/
def finiteSymbolUnaryFrames {Γ : Type} (code : Γ → Nat)
    (input : List Γ) : List UnaryFrameSym :=
  input.flatMap (finiteSymbolUnaryFrameBody code).emit

/-- The bounded-loop target is precisely the ordinary unary encoding of the
pointwise code list. -/
theorem finiteSymbolUnaryFrames_eq_encodeUnaryFrame {Γ : Type}
    (code : Γ → Nat) (input : List Γ) :
    finiteSymbolUnaryFrames code input =
      encodeUnaryFrame (input.map code) := by
  unfold finiteSymbolUnaryFrames finiteSymbolUnaryFrameBody encodeUnaryFrame
  rw [List.flatMap_map]

/-- A fixed polynomial-time TM2 computes all symbol-code frames directly from
the raw word.  The finite code table contributes only a constant factor. -/
noncomputable def finiteSymbolUnaryFrames_computableInPolyTime
    {Γ : Type} [Fintype Γ] (code : Γ → Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (finiteSymbolUnaryFrames code) := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      input.flatMap (finiteSymbolUnaryFrameBody code).emit)
  exact boundedLoop_computableInPolyTime
    (finiteSymbolUnaryFrameBody code)

end CLRS.Chapter34.Turing.PolyBuilder


