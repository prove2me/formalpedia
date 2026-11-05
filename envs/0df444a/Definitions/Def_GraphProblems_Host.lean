-- Prove2me | Definitions.Def_GraphProblems_Host
-- name    : GraphProblems_Host
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:47:44.817641+00:00
-- url     : https://prove2.me/theorems/3c3c0b9a-740a-474e-a783-c5bc1e9ff34b
-- title:
--   Host
-- statement:
--   Definitions and structural lemmas for Host, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Host.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_CountKSat_Host
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
section
namespace GraphProblems
open Groundwork CountKSat Turing
end GraphProblems


