-- Prove2me | Definitions.Def_Paper_SecNetworks_Model
-- name    : Paper_SecNetworks_Model
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:48:01.737808+00:00
-- url     : https://prove2.me/theorems/dba93729-87e0-4e12-9946-b1183559aac7
-- title:
--   Sec Networks Model
-- statement:
--   Definitions and structural lemmas for Sec Networks Model, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Model.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_StepMachineStatements
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
set_option autoImplicit false
section
section
namespace Paper
open Groundwork
abbrev StepMachine (α β : Type) : Type 1 := Stepped α β
def PolyTimeSteps {α β : Type} [Enc α] [Enc β] (M : StepMachine α β) : Prop := Nonempty (IsPolyT M)
abbrev DecidesInSteps (M : StepMachine (List Bool) Bool) (δ : ℝ) : Prop := Groundwork.DecidesInSteps M δ
end Paper


