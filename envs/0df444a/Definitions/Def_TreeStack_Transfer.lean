-- Prove2me | Definitions.Def_TreeStack_Transfer
-- name    : TreeStack_Transfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:07:49.254883+00:00
-- url     : https://prove2.me/theorems/de505cea-74b1-5177-9b61-5923f3ef47cf
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Transfer.lean

import Mathlib
import Definitions.Def_TreeStack_Basic
set_option autoImplicit false
namespace TreeStack
def F (x : ℤ) : ℤ :=
  if x ≤ 1 then
    2 * x - 3
  else if x = 2 then
    1
  else if x = 3 then
    0
  else if x % 2 = 0 then
    x / 2
  else
    (x - 3) / 2
abbrev Message := Option ℤ
def EMPTY : Message := none
end TreeStack


