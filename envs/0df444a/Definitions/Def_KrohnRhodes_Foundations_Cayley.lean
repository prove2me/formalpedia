-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_Cayley
-- name    : KrohnRhodes_Foundations_Cayley
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:55:48.895077+00:00
-- url     : https://prove2.me/theorems/74610074-c83b-5b79-b4c9-46af370e9059
-- title:
--   Cayley
-- statement:
--   Definitions and structural lemmas for Cayley, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/Cayley.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.style.show false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
namespace KrohnRhodes
universe u
variable {M : Type u} [Monoid M] [Finite M]
end KrohnRhodes


