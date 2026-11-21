-- Prove2me | Definitions.Def_Eidos_Ergo_Context
-- name    : Eidos_Ergo_Context
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:36:07.658201+00:00
-- url     : https://prove2.me/theorems/7350eb33-abdb-4f63-baee-744cf3cbed7e
-- title:
--   Context
-- statement:
--   Definitions and structural lemmas for Context, from Lithos Protocol contributors's pinned Reserve accounting for an ErgoScript fragment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Context.lean

import Definitions.Def_Eidos_Ergo_Long
set_option autoImplicit false
namespace Eidos.Ergo
structure Box where
  value : Long
  deriving Repr, DecidableEq
structure Context where
  self : Box
  outputs : List Box
  deriving Repr, DecidableEq
def Context.outputValue (ctx : Context) (index : Nat) : Except EvalError Long :=
  match ctx.outputs[index]? with
  | some box => .ok box.value
  | none => .error (.outputOutOfBounds index)
end Eidos.Ergo


