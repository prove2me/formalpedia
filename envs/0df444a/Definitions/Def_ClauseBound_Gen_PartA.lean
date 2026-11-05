-- Prove2me | Definitions.Def_ClauseBound_Gen_PartA
-- name    : ClauseBound_Gen_PartA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:30.038442+00:00
-- url     : https://prove2.me/theorems/847c634d-8739-49cf-856c-4d25a2a503f7
-- title:
--   Part A
-- statement:
--   Definitions and structural lemmas for Part A, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/PartA.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Gen
open Levels.Gen
@[expose] def x (x₀ : ℕ) : ℕ → ℕ
  | 0 => x₀
  | l + 1 => 2 * (3 * l + x₀ + x x₀ l)
end ClauseBound.Gen


