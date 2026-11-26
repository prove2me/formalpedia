-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
-- name    : KrohnRhodes_Foundations_ConstantMaps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:55:18.649514+00:00
-- url     : https://prove2.me/theorems/f651dd3e-45a6-5a09-8687-651766bc32a1
-- title:
--   Constant Maps
-- statement:
--   Definitions and structural lemmas for Constant Maps, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/ConstantMaps.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
namespace KrohnRhodes
universe u
variable {Q : Type u}
def constEnd (q : Q) : Function.End Q := fun _ => q
def IsConstEnd (t : Function.End Q) : Prop := ∃ q : Q, t = constEnd q
end KrohnRhodes


