-- Prove2me | Definitions.Def_VariableBound_Net_Total
-- name    : VariableBound_Net_Total
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:07:24.050178+00:00
-- url     : https://prove2.me/theorems/221e0e38-d520-46d5-8839-c2e0df42271a
-- title:
--   Total
-- statement:
--   Definitions and structural lemmas for Total, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Total.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
section
namespace VariableBound.Net.Total
open Groundwork Groundwork.Prog Finset PaddedDescent.F
end VariableBound.Net.Total


