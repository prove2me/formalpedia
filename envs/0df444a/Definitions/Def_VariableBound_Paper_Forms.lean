-- Prove2me | Definitions.Def_VariableBound_Paper_Forms
-- name    : VariableBound_Paper_Forms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:19:15.785864+00:00
-- url     : https://prove2.me/theorems/13b324aa-3358-4361-8180-4b8c95e84420
-- title:
--   Forms
-- statement:
--   Definitions and structural lemmas for Forms, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)
end VariableBound.Paper


