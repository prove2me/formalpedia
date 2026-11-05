-- Prove2me | Definitions.Def_CountedToPadded_SolverPoly
-- name    : CountedToPadded_SolverPoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:08:08.905355+00:00
-- url     : https://prove2.me/theorems/98482492-bfac-452e-86e6-de6c648cccaf
-- title:
--   Solver Poly
-- statement:
--   Definitions and structural lemmas for Solver Poly, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/SolverPoly.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
@[expose, instance_reducible] def onTablesIsPoly (M : QueryMachine TableQuery ℤ (U × U × U) ℤ) [QueryMachine.IsPolyQ M] : IsPolyT (onTables M) :=
  letI := lookupIsPoly
  QueryMachine.plug_isPolyT M lookup
end QueryMachines.Bridge.Proof
namespace QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed Proof
end QueryMachines.Bridge


