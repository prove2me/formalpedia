-- Prove2me | Definitions.Def_Coding_GridDefs
-- name    : Coding_GridDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:59:18.0959+00:00
-- url     : https://prove2.me/theorems/b1717f46-12f0-45a2-8d60-dffb2ff5dc5a
-- title:
--   Grid Defs
-- statement:
--   Definitions and structural lemmas for Grid Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/GridDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Theorems.Thm_Groundwork_PolyT_flatMap
attribute [local fun_prop] Groundwork.PolyT.flatMap


set_option autoImplicit false
section
section
namespace Coding
open Finset Groundwork Groundwork.Prog ClauseBound.Alg Eight.SecNetworks Eight.ViaGrouping
def readThrough {g : ℕ} (N : Net g) (len₀ : Fin g → ℕ) (pad : Fin g → List Bool → List Bool) : Net g where
  len := len₀
  S a := words (len₀ a)
  W a z := N.W a (pad a z)
  Ψ a b z z' := N.Ψ a b (pad a z) (pad b z')
  c := N.c
  f a b z θ := N.f a b (pad a z) θ
def padRow (g : ℕ) (tr : Bool) (lam a : ℕ) (z : List Bool) : List Bool :=
  (List.range g).flatMap fun x => (List.range (g * g)).flatMap fun u =>
    if u = nodeG g tr a x then List.replicate lam false else block lam (if u < nodeG g tr a x then u else u - 1) (block ((g * g - 1) * lam) x z)
def StGridPadding : Prop := ∀ (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)),
  PaddingOf (readThrough (levelNetP g tr lam y Rm) (fun _ => g * (g ^ 2 - 1) * lam) fun a => padRow g tr lam a.val) (levelNetP g tr lam y Rm) fun a => padRow g tr lam a.val
def StGridLength : Prop := ∀ g lam : ℕ, g * (g ^ 2 - 1) * lam ≤ g ^ 3 * lam
end Coding


