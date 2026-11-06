-- Prove2me | Definitions.Def_SplitSat_Sizes
-- name    : SplitSat_Sizes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:35:18.23408+00:00
-- url     : https://prove2.me/theorems/8d437a06-0722-43aa-81ab-dc4e1749760d
-- title:
--   Sizes
-- statement:
--   Definitions and structural lemmas for Sizes, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify
@[expose] def cOf (P₂ P₀ R c e : ℕ) : ℕ := P₂ + P₀ + c * R ^ c + c + e + 20
end SplitSat


