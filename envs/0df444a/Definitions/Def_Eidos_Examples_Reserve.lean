-- Prove2me | Definitions.Def_Eidos_Examples_Reserve
-- name    : Eidos_Examples_Reserve
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:36:33.789208+00:00
-- url     : https://prove2.me/theorems/fb5c9377-83ae-4a39-9174-44ba4e9dd056
-- title:
--   Reserve
-- statement:
--   Definitions and structural lemmas for Reserve, from Lithos Protocol contributors's pinned Reserve accounting for an ErgoScript fragment development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Examples/Reserve.lean

import Definitions.Def_Eidos_Ergo_Expr
set_option autoImplicit false
namespace Eidos.Examples.Reserve
open Ergo
def script (reserve : Long) : BoolExpr :=
  .and (.le (.outputValue 0) .selfValue)
       (.le (.const reserve) (.outputValue 0))
def vulnerableScript : BoolExpr := .le (.outputValue 0) .selfValue
def WithdrawalBounded (reserve : Long) (ctx : Context) : Prop :=
  ∃ out, ctx.outputs[0]? = some out ∧
    0 ≤ ctx.self.value.val - out.value.val ∧
    ctx.self.value.val - out.value.val ≤ ctx.self.value.val - reserve.val
def attackContext : Context :=
  { self := ⟨⟨100000000000, by decide⟩⟩
    outputs := [⟨⟨20000000000, by decide⟩⟩] }
def exampleReserve : Long := ⟨30000000000, by decide⟩
end Eidos.Examples.Reserve


