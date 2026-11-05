-- Prove2me | Definitions.Def_Paper_SecCrossing_Crossing
-- name    : Paper_SecCrossing_Crossing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:38:06.691827+00:00
-- url     : https://prove2.me/theorems/486fd8c4-99e0-4b0a-8c9f-c1139440a265
-- title:
--   Sec Crossing Crossing
-- statement:
--   Definitions and structural lemmas for Sec Crossing Crossing, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecCrossing_Crossing.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_DefFactor
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Cuts
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_CutProg
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Coeff
set_option autoImplicit false
section
section
namespace Paper
open Finset
open Groundwork (Bits)
local notation "T" => (Polynomial.X : Polynomial ℤ)
local notation "C" => (Polynomial.C : ℤ →+* Polynomial ℤ)
variable {lam : ℕ}
variable {Z Z' : Type*}
open Groundwork.Grid (sideCut)
end Paper


