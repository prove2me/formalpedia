-- Prove2me | Definitions.Def_CountedToPadded_Pick
-- name    : CountedToPadded_Pick
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:45:56.631371+00:00
-- url     : https://prove2.me/theorems/1056a1f0-f05d-47a1-8a12-a080e3986715
-- title:
--   Pick
-- statement:
--   Definitions and structural lemmas for Pick, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Pick.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels
@[expose] def cand (kf : U × U → Option U) (b : U) (l : ℕ) : Option (U × (U × U)) := (kf (b.take l, b)).map fun k => (b.take l, (b.take l, k))
end QueryMachines.Bridge.Proof
namespace QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels Proof
end QueryMachines.Bridge


