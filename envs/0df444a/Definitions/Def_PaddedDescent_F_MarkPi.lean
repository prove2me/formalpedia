-- Prove2me | Definitions.Def_PaddedDescent_F_MarkPi
-- name    : PaddedDescent_F_MarkPi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:38:17.281173+00:00
-- url     : https://prove2.me/theorems/87e31b1d-2841-4d85-80e7-0264cbcf097a
-- title:
--   Mark Pi
-- statement:
--   Definitions and structural lemmas for Mark Pi, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false
section
namespace PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]
end PaddedDescent.F.Mark.Pi


