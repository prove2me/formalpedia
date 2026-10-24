-- Prove2me | Definitions.Def_PricingWithTips3DM_fc044af4e5ea7dd381bd01dc
-- name    : PricingWithTips3DM_fc044af4e5ea7dd381bd01dc
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:24:34.941698+00:00
-- url     : https://prove2.me/theorems/89f5c5a8-7e34-4bc7-bac6-db2a99a1d0ed
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteCore
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_23b4e8fdb6bc1ff87a8f0413
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Decoding one quoted unary-frame row

The decoder is total.  A malformed codeword stops semantic decoding and the
physical controller drains the remaining input before its clean halt.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Total prefix decoder for the two-symbol quotation code. -/
def unquoteUnaryFrameStream : List UnaryFrameSym → List UnaryFrameSym
  | [] => []
  | .frameEnd :: _ => []
  | [.tick] => []
  | .tick :: .tick :: rest => .tick :: unquoteUnaryFrameStream rest
  | .tick :: .separator :: rest =>
      .separator :: unquoteUnaryFrameStream rest
  | .tick :: .frameEnd :: _ => []
  | [.separator] => []
  | .separator :: .tick :: rest =>
      .frameEnd :: unquoteUnaryFrameStream rest
  | .separator :: .separator :: _ => []
  | .separator :: .frameEnd :: _ => []

/-- Quoting followed by a single outer boundary decodes exactly. -/
@[simp] theorem unquoteUnaryFrameStream_quote_boundary
    (input : List UnaryFrameSym) :
    unquoteUnaryFrameStream
      (quoteUnaryFrameStream input ++ [.frameEnd]) = input := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp [quoteUnaryFrameStream_cons, quoteUnaryFrameSym, ih,
          unquoteUnaryFrameStream]

/-- Quotation respects append, used after same-input row concatenation. -/
@[simp] theorem quoteUnaryFrameStream_append
    (left right : List UnaryFrameSym) :
    quoteUnaryFrameStream (left ++ right) =
      quoteUnaryFrameStream left ++ quoteUnaryFrameStream right := by
  simp [quoteUnaryFrameStream, List.flatMap_append]

/-- The concatenation of two quoted payloads and one outer boundary decodes
to the literal source concatenation. -/
theorem unquoteUnaryFrameStream_quote_append_boundary
    (left right : List UnaryFrameSym) :
    unquoteUnaryFrameStream
        (quoteUnaryFrameStream left ++ quoteUnaryFrameStream right ++
          [.frameEnd]) =
      left ++ right := by
  rw [← quoteUnaryFrameStream_append]
  exact unquoteUnaryFrameStream_quote_boundary (left ++ right)

/-- Finite phases of the total quoted-row decoder. -/
inductive UnaryFrameUnquoteLabel
  | scan
  | afterTick
  | afterSeparator
  | emit (symbol : UnaryFrameSym)
  | drain
  | finish
deriving DecidableEq, Fintype

/-- Reverse-output decoder.  `frameEnd` at a codeword boundary is the outer
terminator; malformed inputs are drained without further output. -/
def unaryFrameUnquoteRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameUnquoteLabel
  main := .scan
  op
    | .scan => .popInput .finish fun
        | .tick => .afterTick
        | .separator => .afterSeparator
        | .frameEnd => .drain
    | .afterTick => .popInput .finish fun
        | .tick => .emit .tick
        | .separator => .emit .separator
        | .frameEnd => .drain
    | .afterSeparator => .popInput .finish fun
        | .tick => .emit .frameEnd
        | .separator => .drain
        | .frameEnd => .drain
    | .emit symbol => .pushOutput symbol .scan
    | .drain => .popInput .finish fun _ => .drain
    | .finish => .halt

/-- Uniform configuration surface for decoder simulations. -/
def unaryFrameUnquoteCfg (label : UnaryFrameUnquoteLabel)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameUnquoteRevProgram :=
  { label := some label
    buffer₁ := buffer
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := []
    work₂ := []
    counter₁ := []
    counter₂ := []
    counter₃ := [] }

end CLRS.Chapter34.Turing.PolyBuilder


