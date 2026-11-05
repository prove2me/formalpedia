-- Prove2me | Definitions.Def_ThmCount_FrontEnd
-- name    : ThmCount_FrontEnd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:56:03.5402+00:00
-- url     : https://prove2.me/theorems/1ccef7d4-d0c5-4eb0-b450-31fd39ced112
-- title:
--   Front End
-- statement:
--   Definitions and structural lemmas for Front End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
namespace ThmCount
open Groundwork Groundwork.Decode
def encPlain (u w : List Unit) (F : NCNF) : List Bool :=
  List.replicate 3 true ++ false :: (u.map (fun _ => true) ++ false :: F.flatMap fun C => (List.range 3).flatMap fun j =>
    (List.range w.length).map (Wrap.slotNat C[j]?).testBit)
def frontEnd (x : List Bool) : List Bool :=
  encPlain (List.replicate ((x.takeWhile id).length + 4) ()) (List.replicate (Wrap.slotBits x) ()) (Wrap.addFour (dec x))
end ThmCount
section
@[expose] section
namespace ThmCount
open Groundwork Groundwork.Decode
end ThmCount


