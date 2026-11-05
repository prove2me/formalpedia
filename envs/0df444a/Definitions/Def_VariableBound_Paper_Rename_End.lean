-- Prove2me | Definitions.Def_VariableBound_Paper_Rename_End
-- name    : VariableBound_Paper_Rename_End
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:23:09.329751+00:00
-- url     : https://prove2.me/theorems/48259a53-978e-4ecb-ac7c-ed0c1ca6224c
-- title:
--   End
-- statement:
--   Definitions and structural lemmas for End, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/End.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_UniformInK_Top_End
import Theorems.Thm_Groundwork_PolyT_any
attribute [local fun_prop] Groundwork.PolyT.any


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Rename
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
@[expose] def anyBit (w : List Bool) : List Bool := [w.any id]
end VariableBound.Rename


