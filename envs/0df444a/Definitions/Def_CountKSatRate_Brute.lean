-- Prove2me | Definitions.Def_CountKSatRate_Brute
-- name    : CountKSatRate_Brute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:11:09.192734+00:00
-- url     : https://prove2.me/theorems/7ec0dba5-213c-4ef5-bf58-caaac42741a9
-- title:
--   Brute
-- statement:
--   Definitions and structural lemmas for Brute, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Batteries.Data.Nat.Lemmas
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
namespace CountKSatRate.Brute
open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)
end CountKSatRate.Brute
namespace CountKSatRate
open CountKSatRate.Brute
end CountKSatRate


