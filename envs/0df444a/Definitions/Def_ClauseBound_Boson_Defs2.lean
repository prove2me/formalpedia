-- Prove2me | Definitions.Def_ClauseBound_Boson_Defs2
-- name    : ClauseBound_Boson_Defs2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:16:45.306293+00:00
-- url     : https://prove2.me/theorems/c2ddc348-1d3a-46b1-86cc-66536db9bd6f
-- title:
--   Defs2
-- statement:
--   Definitions and structural lemmas for Defs2, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Defs2.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_PiecesStatement
set_option autoImplicit false
section
section
namespace ClauseBound.Boson
open Finset
abbrev FA : Type := List (ℤ × List ℕ)
def yl (n : ℕ) : List (ℤ × ℕ) := (List.range n).map fun i => ((-1) ^ (n - 1) * (n.choose (i + 1) : ℤ), i + 1)
def aFam : List ℕ → FA
  | [] => [(1, [])]
  | n :: μ => (yl n).flatMap fun cj => (aFam μ).map fun cL => (cj.1 * cL.1, cj.2 :: cL.2)
def zz (ν : Multiset ℕ) : ℕ := ∏ k ∈ ν.toFinset, k ^ ν.count k * (ν.count k).factorial
def Qk (A : FA) (b : List ℕ) (s : ℤ) : Ker := fun π σ =>
  ∑ i ∈ range (2 * b.sum + 1), (-1) ^ i *
    (A.map fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ) * mul2 c.2 (s - b.sum + i) b (b.sum - s - i) π σ).sum
def Qk' (A : FA) (b : List ℕ) (s : ℤ) : Ker := fun π σ =>
  ∑ i ∈ range (2 * b.sum + 1), (-1) ^ i *
    (A.map fun c => c.1 * ((c.2.sum + b.sum).choose i : ℤ) * mul2 b (b.sum - s - i) c.2 (s - b.sum + i) π σ).sum
def FA.Ok (A : FA) (h : ℕ) : Prop := ∀ c ∈ A, Pos c.2 ∧ c.2.sum ≤ h
noncomputable def lst {h : ℕ} (q : Nat.Partition h) : List ℕ := q.parts.toList
end ClauseBound.Boson


