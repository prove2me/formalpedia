-- Prove2me | Definitions.Def_MinOfBounds_Rename
-- name    : MinOfBounds_Rename
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:41:20.118598+00:00
-- url     : https://prove2.me/theorems/8ec95719-756f-4c35-81b4-7932e49e438c
-- title:
--   Rename
-- statement:
--   Definitions and structural lemmas for Rename, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Rename.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_WidthK_Decode
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup
set_option autoImplicit false
section
section
@[expose] section
namespace MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
end MinOfBounds


