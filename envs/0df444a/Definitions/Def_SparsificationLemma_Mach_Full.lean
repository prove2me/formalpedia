-- Prove2me | Definitions.Def_SparsificationLemma_Mach_Full
-- name    : SparsificationLemma_Mach_Full
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:31:09.701122+00:00
-- url     : https://prove2.me/theorems/ba8c9ffd-2449-4ea1-8910-1b80f946d7d6
-- title:
--   Full
-- statement:
--   Definitions and structural lemmas for Full, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Full.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Geo_S
import Definitions.Def_SparsificationLemma_Mach_Len
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


