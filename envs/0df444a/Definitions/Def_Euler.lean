-- Prove2me | Definitions.Def_Euler
-- name    : Euler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:42:41.272822+00:00
-- url     : https://prove2.me/theorems/6bf326af-8d16-541a-9f73-5b1cae7ceb63
-- title:
--   Euler
-- statement:
--   Definitions and structural lemmas for Euler, from Juan Pablo Traverso Gianini (jtraverso/euler-petersen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Euler's theorem on Eulerian circuits and trails, and Petersen's 2-factor theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler.lean

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Konigsberg
public import Definitions.Def_Euler_Orientation
public import Definitions.Def_Euler_Petersen
set_option autoImplicit true
@[expose] public section


