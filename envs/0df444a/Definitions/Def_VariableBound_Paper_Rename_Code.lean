-- Prove2me | Definitions.Def_VariableBound_Paper_Rename_Code
-- name    : VariableBound_Paper_Rename_Code
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:36:48.799286+00:00
-- url     : https://prove2.me/theorems/9a522e69-8bad-44c2-828b-50fa962df306
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_Decode
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
end VariableBound.Rename


