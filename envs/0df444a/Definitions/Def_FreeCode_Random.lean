-- Prove2me | Definitions.Def_FreeCode_Random
-- name    : FreeCode_Random
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:44.463923+00:00
-- url     : https://prove2.me/theorems/e059ed02-8d61-46dd-9a47-5219da546c98
-- title:
--   Random
-- statement:
--   Definitions and structural lemmas for Random, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal
end SatFree


