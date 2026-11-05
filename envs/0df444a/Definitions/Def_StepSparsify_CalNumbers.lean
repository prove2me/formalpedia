-- Prove2me | Definitions.Def_StepSparsify_CalNumbers
-- name    : StepSparsify_CalNumbers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:23:54.155423+00:00
-- url     : https://prove2.me/theorems/a54cba48-19a5-4eca-8f35-be0e4f54663c
-- title:
--   Cal Numbers
-- statement:
--   Definitions and structural lemmas for Cal Numbers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_UniformInK_Top_Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
section
section
@[expose] section
namespace StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma
end StepSparsify


