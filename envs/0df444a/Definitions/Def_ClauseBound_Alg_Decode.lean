-- Prove2me | Definitions.Def_ClauseBound_Alg_Decode
-- name    : ClauseBound_Alg_Decode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:13:30.807576+00:00
-- url     : https://prove2.me/theorems/1d2fa93e-826f-4c9b-bd8a-073fbb0f84c3
-- title:
--   Decode
-- statement:
--   Definitions and structural lemmas for Decode, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Decode.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Theorems.Thm_Groundwork_Decode_width_polyT
attribute [local fun_prop] Groundwork.Decode.width_polyT


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.Decode
open Groundwork CountKSat
open Groundwork.Decode (slotDec width width_polyT)
open Groundwork.DecodeK (clauseDec decK)
variable {α : Type} [Enc α]
end ClauseBound.Alg.Decode


