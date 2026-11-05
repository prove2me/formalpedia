-- Prove2me | Definitions.Def_UniformInK_Top_ArithMaster
-- name    : UniformInK_Top_ArithMaster
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:23:41.041218+00:00
-- url     : https://prove2.me/theorems/ea0ab4a4-b91c-4192-9a9f-668800a8e377
-- title:
--   Arith Master
-- statement:
--   Definitions and structural lemmas for Arith Master, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithMaster.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_ParityChecks_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK
open ClauseBound.Alg.TopArith
end UniformInK


