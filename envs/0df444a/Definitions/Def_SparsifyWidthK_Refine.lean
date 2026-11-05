-- Prove2me | Definitions.Def_SparsifyWidthK_Refine
-- name    : SparsifyWidthK_Refine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:33:28.161931+00:00
-- url     : https://prove2.me/theorems/9b3e3d32-4a41-479f-91d7-84e293c61d02
-- title:
--   Refine
-- statement:
--   Definitions and structural lemmas for Refine, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
def Before (x y : ℕ × ℕ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ y.2 < x.2)
end WidthK.Refine


