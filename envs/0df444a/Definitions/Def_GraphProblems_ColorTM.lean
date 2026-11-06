-- Prove2me | Definitions.Def_GraphProblems_ColorTM
-- name    : GraphProblems_ColorTM
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:06:02.869561+00:00
-- url     : https://prove2.me/theorems/69d4fde2-a27b-4fe1-a40a-b8e8a3de88d8
-- title:
--   Color TM
-- statement:
--   Definitions and structural lemmas for Color TM, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/ColorTM.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_GraphProblems_Sized
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
namespace GraphProblems
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing
@[expose] public def readC (k : ℕ) (x : List Bool) : List Unit × Fml :=
  (List.replicate ((read1 x).1.length * k) (), (colorF k (read1 x).1.length (read1 x).2).dedup)
end GraphProblems


