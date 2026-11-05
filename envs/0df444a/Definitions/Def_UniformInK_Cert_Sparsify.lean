-- Prove2me | Definitions.Def_UniformInK_Cert_Sparsify
-- name    : UniformInK_Cert_Sparsify
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:36:26.640773+00:00
-- url     : https://prove2.me/theorems/8a8d6326-9340-43e9-a1d1-094ec9791f66
-- title:
--   Sparsify
-- statement:
--   Definitions and structural lemmas for Sparsify, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace UniformInK.CertSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog
variable {α : Type} [Enc α]
def heartsL (M : List (List Bool)) (s : PFml) (j h : ℕ) : PFml :=
  (s.filter fun C => decide (C.length = j)).flatMap fun C => (M.map fun m => maskP m C).filter fun H => decide (H.length = h)
def tryL (M : List (List Bool)) (s : PFml) (c : (ℕ × ℕ) × ℕ) : Option (PCl × PFml) :=
  ((heartsL M s c.1.1 c.1.2).find? fun H => decide (c.2 ≤ (overP s c.1.1 H).length)).map fun H => (H, (overP s c.1.1 H).map (minusP H))
def pickL (M : List (List Bool)) (L : List ((ℕ × ℕ) × ℕ)) (s : PFml) : Option (PCl × PFml) := (L.filterMap (tryL M s)).head?
end UniformInK.CertSparsify


