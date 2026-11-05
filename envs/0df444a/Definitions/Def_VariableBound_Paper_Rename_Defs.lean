-- Prove2me | Definitions.Def_VariableBound_Paper_Rename_Defs
-- name    : VariableBound_Paper_Rename_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:31:38.262371+00:00
-- url     : https://prove2.me/theorems/51e3bb6f-aaf8-4b27-ba28-d7d25db80b5b
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
namespace VariableBound.Rename
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
def occL (ψ : Fml) : List ℕ := (ψ.flatMap fun C => C.map fun l => l.1).dedup
def renL (L : List ℕ) (ψ : Fml) : Fml := ψ.map fun C => C.map fun l => (L.idxOf l.1, l.2)
def renF (ψ : Fml) : U × Fml := ((occL ψ).map fun _ => (), renL (occL ψ) ψ)
def slotN (o : Option (ℕ × Bool)) : ℕ := o.elim 0 fun l => 2 * l.1 + 1 + l.2.toNat
def encN (ku : U) (d : U × Fml) : List Bool :=
  ku.map (fun _ => true) ++ false :: (d.1.map (fun _ => true) ++ false :: d.2.flatMap fun C => (List.range ku.length).flatMap fun j =>
    (List.range (Nat.log2 (2 * d.1.length) + 1)).map (slotN C[j]?).testBit)
def renc (x : List Bool) : List Bool := encN (kOf x) (renF (fmlOf x).2)
end VariableBound.Rename


