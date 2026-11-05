-- Prove2me | Definitions.Def_SparsifyWidthK_Thresholds
-- name    : SparsifyWidthK_Thresholds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:33:34.96792+00:00
-- url     : https://prove2.me/theorems/dcca563e-35b5-4fb3-934f-25d6e4065186
-- title:
--   Thresholds
-- statement:
--   Definitions and structural lemmas for Thresholds, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Thresholds.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_StepMachines_Math_SparsifyCount
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace WidthK.Thresholds
open Finset
end WidthK.Thresholds
namespace WidthK
open Finset Thresholds
end WidthK


