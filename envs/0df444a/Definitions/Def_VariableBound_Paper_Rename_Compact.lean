-- Prove2me | Definitions.Def_VariableBound_Paper_Rename_Compact
-- name    : VariableBound_Paper_Rename_Compact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:38:22.240176+00:00
-- url     : https://prove2.me/theorems/742c5f4f-4ffa-44aa-95ad-57b0570eed42
-- title:
--   Compact
-- statement:
--   Definitions and structural lemmas for Compact, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_dropWhile
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)
@[expose] def clausesOf (k w : ℕ) (b : List Bool) : Fml :=
  ((List.range b.length).take (b.length / (k * w))).map fun c => clauseDec k w (block (k * w) c b)
@[expose] def decC (x : List Bool) : Fml :=
  clausesOf (kOf x).length ((restOf x).takeWhile id).length ((restOf x).dropWhile id).tail
@[expose] def rencC (x : List Bool) : List Bool := encN (kOf x) (renF (decC x))
def bodyOf (k : ℕ) {N : ℕ} (φ : CNF N) : List Bool :=
  φ.flatMap fun C => (List.range k).flatMap fun j => (List.range (Nat.log2 (2 * N) + 1)).map (Sat3.slot C[j]?).testBit
end VariableBound.Rename


