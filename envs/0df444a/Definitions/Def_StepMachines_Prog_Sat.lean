-- Prove2me | Definitions.Def_StepMachines_Prog_Sat
-- name    : StepMachines_Prog_Sat
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:34:06.68348+00:00
-- url     : https://prove2.me/theorems/bd5931e4-dcdc-4041-955d-f71ad8ca7ecd
-- title:
--   Sat
-- statement:
--   Definitions and structural lemmas for Sat, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Sat.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Math_SparsifyCount
set_option autoImplicit false
section
namespace Groundwork.Prog
open Groundwork.Sparsify (leaves rootP stepP)
@[expose] public def decF (x : List Bool) : Fml := (Decode.dec x).2
@[expose] public def hasNil (ψ : Fml) : Bool := ψ.any List.isEmpty
@[expose] public def posZ (v : ℤ) : Bool := decide (0 < v)
@[expose] public def satM (τ : ℕ) (M : Stepped Fml ℤ) : Stepped (List Bool) Bool :=
  Stepped.mapIn decF (Stepped.ite hasNil (Stepped.const false)
    (Stepped.walk (stepP τ) rootP (Stepped.mapOut M posZ)))
end Groundwork.Prog


