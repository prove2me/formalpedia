-- Prove2me | Definitions.Def_SparsificationLemma_Mach_LemSparsification
-- name    : SparsificationLemma_Mach_LemSparsification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:33:52.357742+00:00
-- url     : https://prove2.me/theorems/5e739447-068e-4f5f-9f15-dd60d0548e09
-- title:
--   Lem Sparsification
-- statement:
--   Definitions and structural lemmas for Lem Sparsification, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/LemSparsification.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
end SparsificationLemma.Mach


