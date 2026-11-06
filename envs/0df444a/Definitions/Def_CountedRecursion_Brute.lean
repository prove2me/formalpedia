-- Prove2me | Definitions.Def_CountedRecursion_Brute
-- name    : CountedRecursion_Brute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:42:09.08321+00:00
-- url     : https://prove2.me/theorems/206957dd-3344-418a-a01a-3a829f5ce64c
-- title:
--   Brute
-- statement:
--   Definitions and structural lemmas for Brute, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Brute.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Within
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
end ExplicitCost


