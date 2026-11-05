-- Prove2me | Definitions.Def_ThmCount_MEps
-- name    : ThmCount_MEps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:35:59.787593+00:00
-- url     : https://prove2.me/theorems/6fc1d9d8-d2af-4fd9-aded-7003101a601c
-- title:
--   MEps
-- statement:
--   Definitions and structural lemmas for MEps, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/MEps.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_Rates
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Sketch
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ThmCount
open PaperSentences
end ThmCount


