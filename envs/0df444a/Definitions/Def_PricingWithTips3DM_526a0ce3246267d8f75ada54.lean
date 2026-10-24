-- Prove2me | Definitions.Def_PricingWithTips3DM_526a0ce3246267d8f75ada54
-- name    : PricingWithTips3DM_526a0ce3246267d8f75ada54
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:46:28.75957+00:00
-- url     : https://prove2.me/theorems/54efad84-b98f-48ab-b78f-2ca6374f6a0f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedOrPairFormatCore
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a46ec1070e8b9fcb3ebc4d0c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Formatting marked operand pairs as finite-OR frames: core

The source-side representation stores one row as the ordinary unary encoding
of `[left, right]`, followed by `frameEnd`.  The finite OR controller expects
the canonical frame

`frameEnd / left / 0 / (right + 1) / frameEnd`.

This file defines the pure encodings and the fixed finite controller.  Exact
simulation and polynomial runtime packaging live in separate modules.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Marked two-field source encoding consumed by the formatter. -/
def encodeAffineOrFinMarkedPairFrame (frame : AffineOrFinPairFrame) :
    List UnaryFrameSym :=
  encodeUnaryFrame [frame.left, frame.right] ++ [.frameEnd]

def encodeAffineOrFinMarkedPairFrames
    (frames : List AffineOrFinPairFrame) : List UnaryFrameSym :=
  frames.flatMap encodeAffineOrFinMarkedPairFrame

/-- Finite phases of the direct two-field to OR-frame formatter. -/
inductive UnaryFrameMarkedOrPairFormatLabel
  | beginRow
  | emitOpen (symbol : UnaryFrameSym)
  | left (symbol : UnaryFrameSym)
  | scanLeft
  | emitZero
  | scanRight
  | right (symbol : UnaryFrameSym)
  | emitRightSeparator
  | expectEnd
  | endRow
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- Prepend-output controller emitting the reverse canonical OR-frame
serialization. -/
def unaryFrameMarkedOrPairFormatRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedOrPairFormatLabel
  main := .beginRow
  op
    | .beginRow => .popInput .finish .emitOpen
    | .emitOpen symbol => .pushOutput .frameEnd (.left symbol)
    | .left .tick => .pushOutput .tick .scanLeft
    | .left .separator => .pushOutput .separator .emitZero
    | .left .frameEnd => .jump .invalid
    | .scanLeft => .popInput .invalid .left
    | .emitZero => .pushOutput .separator .scanRight
    | .scanRight => .popInput .invalid .right
    | .right .tick => .pushOutput .tick .scanRight
    | .right .separator => .pushOutput .tick .emitRightSeparator
    | .right .frameEnd => .jump .invalid
    | .emitRightSeparator => .pushOutput .separator .expectEnd
    | .expectEnd => .popInput .invalid fun
        | .frameEnd => .endRow
        | _ => .invalid
    | .endRow => .pushOutput .frameEnd .beginRow
    | .finish => .halt
    | .invalid => .halt

def unaryFrameMarkedOrPairFormatCfg
    (label : UnaryFrameMarkedOrPairFormatLabel)
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedOrPairFormatRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

def unaryFrameMarkedOrPairFormatLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedOrPairFormatRevProgram :=
  unaryFrameMarkedOrPairFormatCfg .beginRow none input output

end CLRS.Chapter34.Turing.PolyBuilder


