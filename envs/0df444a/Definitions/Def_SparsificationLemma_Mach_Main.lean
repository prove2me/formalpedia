-- Prove2me | Definitions.Def_SparsificationLemma_Mach_Main
-- name    : SparsificationLemma_Mach_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:30:25.620194+00:00
-- url     : https://prove2.me/theorems/851f1fd3-04fa-40ad-b2a4-51a02a881c4c
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Cert
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
set_option autoImplicit false
section
section
@[expose] section
namespace SparsificationLemma.Mach
open Groundwork CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
end SparsificationLemma.Mach


