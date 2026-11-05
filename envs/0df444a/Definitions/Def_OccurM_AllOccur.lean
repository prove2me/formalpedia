-- Prove2me | Definitions.Def_OccurM_AllOccur
-- name    : OccurM_AllOccur
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T02:42:44.96007+00:00
-- url     : https://prove2.me/theorems/5ad2ad13-78c5-42a9-8067-b447aa5b8f83
-- title:
--   All Occur
-- statement:
--   Definitions and structural lemmas for All Occur, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/AllOccur.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_OccurM_ArithBack
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_End
set_option autoImplicit false
section
section
@[expose] section
namespace ClausesOccur
open Turing MainTheoremForms
open Sat3 (CNF)
end ClausesOccur


