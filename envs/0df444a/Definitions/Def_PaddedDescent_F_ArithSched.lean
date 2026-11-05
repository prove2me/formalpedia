-- Prove2me | Definitions.Def_PaddedDescent_F_ArithSched
-- name    : PaddedDescent_F_ArithSched
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:47:50.368363+00:00
-- url     : https://prove2.me/theorems/1c354c4c-55e2-42b3-87af-771da6c84ec5
-- title:
--   Arith Sched
-- statement:
--   Definitions and structural lemmas for Arith Sched, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
set_option autoImplicit false
section
section
@[expose] section
namespace PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
namespace Arith
def schedState (j : ℕ) : List Lvl × U × U := (schedL j, List.replicate (Kseq j) (), List.replicate (Lseq j) ())
end Arith
open Arith
namespace Arith
end Arith
end PaddedDescent.F


