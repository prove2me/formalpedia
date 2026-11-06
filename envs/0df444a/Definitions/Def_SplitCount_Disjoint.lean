-- Prove2me | Definitions.Def_SplitCount_Disjoint
-- name    : SplitCount_Disjoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:30:11.628042+00:00
-- url     : https://prove2.me/theorems/5ba65158-06c9-4ab0-912d-70e87ba78570
-- title:
--   Disjoint
-- statement:
--   Definitions and structural lemmas for Disjoint, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width
end SplitCount


