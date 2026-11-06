-- Prove2me | Definitions.Def_Complement_Main
-- name    : Complement_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:55:45.240701+00:00
-- url     : https://prove2.me/theorems/2be2d51f-c5b3-4f37-8b47-136c6427ef82
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Host
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems Turing
end Complement


