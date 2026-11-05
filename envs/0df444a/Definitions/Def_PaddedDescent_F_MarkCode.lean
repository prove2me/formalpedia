-- Prove2me | Definitions.Def_PaddedDescent_F_MarkCode
-- name    : PaddedDescent_F_MarkCode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:30:52.262456+00:00
-- url     : https://prove2.me/theorems/76fb65cf-4048-4500-8834-77e2fb881870
-- title:
--   Mark Code
-- statement:
--   Definitions and structural lemmas for Mark Code, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
namespace PaddedDescent.F.Mark.Code
open Groundwork
def ones (b : ℕ) (x : List Bool) (o : ℕ) : List ℕ := (List.range b).filter fun p => x.getD (o * b + p) false
def blkc (β b : ℕ) (x : List Bool) (o : ℕ) : List Bool :=
  (ones b x o).map (fun _ => true) ++ false :: (ones b x o).flatMap (toWord β)
end PaddedDescent.F.Mark.Code
namespace PaddedDescent.F
end PaddedDescent.F


