-- Prove2me | Definitions.Def_VariableBound_Net_Basic
-- name    : VariableBound_Net_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:02:37.925352+00:00
-- url     : https://prove2.me/theorems/2347d7b7-4903-44cf-b87c-ec602eb5958c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}
end VariableBound.Net.Basic


