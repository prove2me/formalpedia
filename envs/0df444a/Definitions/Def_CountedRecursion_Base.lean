-- Prove2me | Definitions.Def_CountedRecursion_Base
-- name    : CountedRecursion_Base
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:48:48.28185+00:00
-- url     : https://prove2.me/theorems/736d97c4-20dc-4ad3-b856-7507bbb876af
-- title:
--   Base
-- statement:
--   Definitions and structural lemmas for Base, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
end ExplicitCost


