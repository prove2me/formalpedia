-- Prove2me | Definitions.Def_VariableBound_Paper_MainTheorem
-- name    : VariableBound_Paper_MainTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:36:40.009205+00:00
-- url     : https://prove2.me/theorems/ef4a8876-85d2-427d-bb32-e6adce008de0
-- title:
--   Main Theorem
-- statement:
--   Definitions and structural lemmas for Main Theorem, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/MainTheorem.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_CountKSatRate_Pad
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Paper
open Groundwork Turing CountKSatRate VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
end VariableBound.Paper


