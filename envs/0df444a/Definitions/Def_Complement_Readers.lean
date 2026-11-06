-- Prove2me | Definitions.Def_Complement_Readers
-- name    : Complement_Readers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:49:21.164365+00:00
-- url     : https://prove2.me/theorems/2edb51d9-9c4b-467d-8264-23ffbc331fdc
-- title:
--   Readers
-- statement:
--   Definitions and structural lemmas for Readers, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Sets
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems
end Complement


