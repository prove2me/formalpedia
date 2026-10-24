-- Prove2me | Definitions.Def_PricingWithTips3DM_f5a947acd4786694aefa1167
-- name    : PricingWithTips3DM_f5a947acd4786694aefa1167
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:26:39.616881+00:00
-- url     : https://prove2.me/theorems/763dd9b4-68d8-4c2a-874d-2e526582a87a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowQuotedDelimiterMapCore
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a109ba81e03654d2e3b00464
import Definitions.Def_PricingWithTips3DM_23b4e8fdb6bc1ff87a8f0413
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quoted delimiter materialization over marked unary rows

Numeric descriptor rows use `frameEnd` only as their outer row boundary.
This transducer performs the fixed cyclic delimiter substitution and quotes
every materialized payload symbol at the same time.  The original row marker
is retained unquoted, so the result is again a delimiter-safe marked family.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Combined delimiter replacement and payload quotation.  Input
`frameEnd`s are reserved row boundaries and therefore remain literal. -/
def rewriteUnaryFrameQuotedDelimitersFrom
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Fin delimiters.length → List UnaryFrameSym → List UnaryFrameSym
  | _, [] => []
  | index, .tick :: rest =>
      quoteUnaryFrameSym .tick ++
        rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty index rest
  | index, .separator :: rest =>
      quoteUnaryFrameSym (delimiters.get index) ++
        rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty
          (unaryFrameDelimiterNext delimiters hnonempty index) rest
  | index, .frameEnd :: rest =>
      .frameEnd ::
        rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty index rest

/-- Start the combined pass at the first delimiter-table entry. -/
def rewriteUnaryFrameQuotedDelimiters
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty
    ⟨0, hnonempty⟩ input

/-- Finite control remembers the cyclic delimiter position and the
materialized symbol whose two-symbol quotation is being emitted. -/
inductive UnaryFrameQuotedDelimiterMapLabel
    (delimiters : List UnaryFrameSym)
  | scan (index : Fin delimiters.length)
  | emitFirst (nextIndex : Fin delimiters.length) (symbol : UnaryFrameSym)
  | emitSecond (nextIndex : Fin delimiters.length) (symbol : UnaryFrameSym)
  | emitBoundary (index : Fin delimiters.length)
  | finish
deriving DecidableEq, Fintype

/-- Prepend-output implementation of the combined pass. -/
def unaryFrameQuotedDelimiterMapRevProgram
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameQuotedDelimiterMapLabel delimiters
  main := .scan ⟨0, hnonempty⟩
  op
    | .scan index => .popInput .finish fun symbol =>
        match symbol with
        | .frameEnd => .emitBoundary index
        | .tick => .emitFirst index .tick
        | .separator =>
            .emitFirst
              (unaryFrameDelimiterNext delimiters hnonempty index)
              (delimiters.get index)
    | .emitFirst nextIndex symbol =>
        .pushOutput (quoteUnaryFrameFirst symbol)
          (.emitSecond nextIndex symbol)
    | .emitSecond nextIndex symbol =>
        .pushOutput (quoteUnaryFrameSecond symbol) (.scan nextIndex)
    | .emitBoundary index => .pushOutput .frameEnd (.scan index)
    | .finish => .halt

/-- Uniform configuration surface used by the exact simulation. -/
def unaryFrameQuotedDelimiterMapCfg
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (label : UnaryFrameQuotedDelimiterMapLabel delimiters)
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty) :=
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


