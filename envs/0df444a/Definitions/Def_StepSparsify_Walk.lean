-- Prove2me | Definitions.Def_StepSparsify_Walk
-- name    : StepSparsify_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:27.428412+00:00
-- url     : https://prove2.me/theorems/263214f8-7848-4cd2-9413-32868ac4afa8
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/Walk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace StepSparsify
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate UniformInK
end StepSparsify


