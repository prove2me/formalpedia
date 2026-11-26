-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_Division
-- name    : KrohnRhodes_Foundations_Division
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:54:47.977949+00:00
-- url     : https://prove2.me/theorems/0ac8a67b-be9e-4d76-9669-a5cff726eee8
-- title:
--   Division
-- statement:
--   Definitions and structural lemmas for Division, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Division.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
namespace KrohnRhodes
universe u
variable {M : Type u} [Monoid M] [Finite M] [DecidableEq M]
end KrohnRhodes
namespace KrohnRhodes
universe u
instance instMulActionPUnit : MulAction PUnit.{u+1} PUnit.{u+1} :=
  Monoid.toMulAction (M := PUnit.{u+1})
end KrohnRhodes


