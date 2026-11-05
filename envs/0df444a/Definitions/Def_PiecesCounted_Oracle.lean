-- Prove2me | Definitions.Def_PiecesCounted_Oracle
-- name    : PiecesCounted_Oracle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:03:17.596674+00:00
-- url     : https://prove2.me/theorems/b70ad660-c74b-45ce-a169-a74c768e0a1e
-- title:
--   Oracle
-- statement:
--   Definitions and structural lemmas for Oracle, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Oracle.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Groundwork QueryMachines
end PiecesCounted


