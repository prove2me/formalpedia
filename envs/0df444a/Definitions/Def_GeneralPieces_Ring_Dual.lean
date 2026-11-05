-- Prove2me | Definitions.Def_GeneralPieces_Ring_Dual
-- name    : GeneralPieces_Ring_Dual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:21:48.603421+00:00
-- url     : https://prove2.me/theorems/ac884ba0-5a5a-4165-86a4-f87a985ff279
-- title:
--   Dual
-- statement:
--   Definitions and structural lemmas for Dual, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
namespace GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces
def theta (n : ℕ+) (k : ℤ) : ℤ := ∑ j ∈ Icc 1 (n : ℕ), binom n ((n : ℤ) - j) * binom (-k - 1) ((j : ℤ) - 1)
def tuples {α : Type} [DecidableEq α] : List (Finset α) → Finset (List α)
  | [] => {[]}
  | s :: r => (s ×ˢ tuples r).image fun p => p.1 :: p.2
noncomputable def nablas (ks : List ℤ) (f : V) : V := ks.foldr nabla f
noncomputable def posTuples (r h : ℕ) : Finset (List ℤ) := (tuples (List.replicate r (Icc (1 : ℤ) h))).filter fun ks => ks.sum = h
def sgn (μ : List ℕ+) : ℤ := (μ.map fun n : ℕ+ => (-1 : ℤ) ^ ((n : ℕ) - 1)).prod
end GeneralPieces.Dual


