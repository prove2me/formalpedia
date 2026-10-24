-- Prove2me | Definitions.Def_PricingWithTips3DM_1c2352411c43f97f713e7d28
-- name    : PricingWithTips3DM_1c2352411c43f97f713e7d28
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:28:14.457648+00:00
-- url     : https://prove2.me/theorems/939379f9-befb-4cd9-b131-e2816a046f51
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowPresentCore
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_645fa74d60687a6229a5303d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Marking every delimited row as present: core definitions

The optional-conjunction controller expects `tick` before every present row
and one additional `frameEnd` after the complete family.  This fixed
transducer supplies exactly that framing for an arbitrary marked-row family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Encoding obtained by selecting the present branch for every marked row. -/
def encodeUnaryFramePresentMarkedRowFamily
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  family.rows.flatMap (fun row => .tick :: row ++ [.frameEnd]) ++
    [.frameEnd]

inductive UnaryFrameMarkedRowPresentLabel
  | beginRow
  | emitPresent (symbol : UnaryFrameSym)
  | emitSymbol (symbol : UnaryFrameSym)
  | scan
  | emitFinal
  | finish
deriving DecidableEq, Fintype

/-- Prepend-output implementation of the all-present row framing pass. -/
def unaryFrameMarkedRowPresentRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedRowPresentLabel
  main := .beginRow
  op
    | .beginRow => .popInput .emitFinal .emitPresent
    | .emitPresent symbol => .pushOutput .tick (.emitSymbol symbol)
    | .emitSymbol .frameEnd => .pushOutput .frameEnd .beginRow
    | .emitSymbol .tick => .pushOutput .tick .scan
    | .emitSymbol .separator => .pushOutput .separator .scan
    | .scan => .popInput .emitFinal .emitSymbol
    | .emitFinal => .pushOutput .frameEnd .finish
    | .finish => .halt

def unaryFrameMarkedRowPresentCfg
    (label : UnaryFrameMarkedRowPresentLabel)
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowPresentRevProgram where
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

def unaryFrameMarkedRowPresentLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowPresentRevProgram :=
  unaryFrameMarkedRowPresentCfg .beginRow none input output

end CLRS.Chapter34.Turing.PolyBuilder


