-- Prove2me | Definitions.Def_Apportionmentlib_Utils
-- name    : Apportionmentlib_Utils
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T06:39:18.462838+00:00
-- url     : https://prove2.me/theorems/0d2cdd5a-8dc8-4b7d-a8e8-52b9c84fb107
-- title:
--   Utils
-- statement:
--   Definitions and structural lemmas for Utils, from mdbrnowski/apportionmentlib contributors (see pinned LICENSE and source headers)'s pinned Balinski–Young apportionment impossibility development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Utils.lean

module
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
public section
@[expose] section
def padLeft (s : String) (n : Nat) (c : Char) : String :=
  let padLen := n - s.length
  if padLen > 0 then ("".pushn c padLen) ++ s else s
def formatRat4 (r : Rat) : String :=
  let scaled := (r * 10000).floor
  let sign := if scaled < 0 then "-" else ""
  let absVal := scaled.natAbs
  let intPart := absVal / 10000
  let fracPart := absVal % 10000
  let fracStr := padLeft (toString fracPart) 4 '0'
  sign ++ toString intPart ++ "." ++ fracStr


