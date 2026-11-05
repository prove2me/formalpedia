-- Prove2me | Definitions.Def_PaddedDescent_Params
-- name    : PaddedDescent_Params
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:16.700351+00:00
-- url     : https://prove2.me/theorems/0019b4aa-9aaa-4175-a281-a85656b98c49
-- title:
--   Params
-- statement:
--   Definitions and structural lemmas for Params, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Params.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Ring.Nat
set_option autoImplicit false
section
section
namespace PaddedDescent
def Dcol : ℕ := 2 ^ 18
def kseq : ℕ → ℕ
  | 0 => 8
  | j + 1 => 2 * (kseq j + 47 + j)
attribute [irreducible] kseq
def Kseq (j : ℕ) : ℕ := 2 ^ kseq j
def Lseq (j : ℕ) : ℕ := 2 ^ (47 + j)
def gseq (j : ℕ) : ℕ := Kseq j * Lseq j
def sOf (n : ℕ) : ℕ := 3 * (Nat.log2 (Nat.log2 n) - 911) / 19
def tauOf (s : ℕ) : ℕ := 2 ^ (4 * s + 17)
def betaOf (s : ℕ) : ℕ := (s + 7) ^ 2
def layersOf (s : ℕ) : ℕ := 2 * betaOf s + 4
def capOf (n : ℕ) : ℕ := n + 2
def depthOf (s : ℕ) : ℕ := 19 * s / 3 + 700
def s0K (k : ℕ) : ℕ := 2 ^ (k + 4)
def C0K (k : ℕ) : ℕ := 8 * 2 ^ s0K k
def Ktop (s : ℕ) : ℕ := Kseq (depthOf s)
def gtop (s : ℕ) : ℕ := 3 * Ktop s ^ 8
def Ytop (s : ℕ) : ℕ := gtop s ^ 2
end PaddedDescent


