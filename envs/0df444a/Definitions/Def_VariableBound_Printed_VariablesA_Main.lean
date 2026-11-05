-- Prove2me | Definitions.Def_VariableBound_Printed_VariablesA_Main
-- name    : VariableBound_Printed_VariablesA_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:21.496392+00:00
-- url     : https://prove2.me/theorems/676c5ec9-bcf6-4ab2-8d87-613101445f39
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_UniformInK_Top_Time
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.VariablesA
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK MainTheoremForms
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
end VariableBound.VariablesA


