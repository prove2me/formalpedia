-- Prove2me | Definitions.Def_FreeCode_Brute
-- name    : FreeCode_Brute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:52:26.794373+00:00
-- url     : https://prove2.me/theorems/ed8dece1-8240-4d5b-abd6-856a45e70d27
-- title:
--   Brute
-- statement:
--   Definitions and structural lemmas for Brute, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Basic
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
end FreeCode


