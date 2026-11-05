-- Prove2me | Definitions.Def_SparsifyWidthK_Poly_Sparsify
-- name    : SparsifyWidthK_Poly_Sparsify
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:33:42.17941+00:00
-- url     : https://prove2.me/theorems/a741a358-3b1e-462e-a460-6c72b590caa9
-- title:
--   Sparsify
-- statement:
--   Definitions and structural lemmas for Sparsify, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Poly/Sparsify.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace WidthK.Prog
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]
def tryT (k : ℕ) (s : PFml) (c : (ℕ × ℕ) × ℕ) : Option (PCl × PFml) :=
  ((heartsP k s c.1.1 c.1.2).find? fun H => decide (c.2 ≤ (overP s c.1.1 H).length)).map fun H =>
    (H, (overP s c.1.1 H).map (minusP H))
end WidthK.Prog


