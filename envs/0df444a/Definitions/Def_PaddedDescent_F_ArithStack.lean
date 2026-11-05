-- Prove2me | Definitions.Def_PaddedDescent_F_ArithStack
-- name    : PaddedDescent_F_ArithStack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:41:33.032517+00:00
-- url     : https://prove2.me/theorems/b181ac7f-e818-45cd-8c1f-9d89c53e7062
-- title:
--   Arith Stack
-- statement:
--   Definitions and structural lemmas for Arith Stack, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
set_option autoImplicit false
section
section
@[expose] section
set_option exponentiation.threshold 1024
namespace PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)
end PaddedDescent.F.Arith


