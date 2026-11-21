-- Prove2me | Definitions.Def_Eidos_Ergo_Expr
-- name    : Eidos_Ergo_Expr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:36:21.355179+00:00
-- url     : https://prove2.me/theorems/ea9332bb-f9bd-43ca-bcc8-7ffbc0e2c58b
-- title:
--   Expr
-- statement:
--   Definitions and structural lemmas for Expr, from Lithos Protocol contributors's pinned Reserve accounting for an ErgoScript fragment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Expr.lean

import Definitions.Def_Eidos_Ergo_Context
set_option autoImplicit false
namespace Eidos.Ergo
inductive LongExpr where
  | const (value : Long)
  | selfValue
  | outputValue (index : Nat)
  | sub (left right : LongExpr)
  deriving Repr
inductive BoolExpr where
  | const (value : Bool)
  | le (left right : LongExpr)
  | and (left right : BoolExpr)
  deriving Repr
def LongExpr.eval (ctx : Context) : LongExpr → Except EvalError Long
  | .const value => .ok value
  | .selfValue => .ok ctx.self.value
  | .outputValue index => ctx.outputValue index
  | .sub left right => do
      let x ← left.eval ctx
      let y ← right.eval ctx
      Long.sub x y
def BoolExpr.eval (ctx : Context) : BoolExpr → Except EvalError Bool
  | .const value => .ok value
  | .le left right => do
      let x ← left.eval ctx
      let y ← right.eval ctx
      pure (decide (x.val ≤ y.val))
  | .and left right => do
      let b ← left.eval ctx
      if b then right.eval ctx else pure false
def Accepts (script : BoolExpr) (ctx : Context) : Prop :=
  script.eval ctx = .ok true
instance (script : BoolExpr) (ctx : Context) : Decidable (Accepts script ctx) :=
  inferInstanceAs (Decidable (script.eval ctx = .ok true))
end Eidos.Ergo


