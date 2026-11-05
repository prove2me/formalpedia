-- Prove2me | Definitions.Def_PaddedDescent_Host
-- name    : PaddedDescent_Host
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:46:56.817356+00:00
-- url     : https://prove2.me/theorems/89e06489-7ac9-49a8-8609-dacfbf30091d
-- title:
--   Host
-- statement:
--   Definitions and structural lemmas for Host, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Host.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_Machine_Host
set_option autoImplicit false
section
namespace PaddedDescent
open Groundwork Groundwork.TM Groundwork.Host Turing
end PaddedDescent


