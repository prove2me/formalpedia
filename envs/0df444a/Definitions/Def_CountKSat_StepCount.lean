-- Prove2me | Definitions.Def_CountKSat_StepCount
-- name    : CountKSat_StepCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:44:58.386574+00:00
-- url     : https://prove2.me/theorems/873d9a46-0d83-470d-a6f0-00b719b96cfb
-- title:
--   Step Count
-- statement:
--   Definitions and structural lemmas for Step Count, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Tauto
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
namespace StepCount
def Holds (v : PLit → Prop) (x : PFml) : Prop := ∀ C ∈ x, ∃ l ∈ C, v l
end StepCount
open StepCount
end CountKSat


