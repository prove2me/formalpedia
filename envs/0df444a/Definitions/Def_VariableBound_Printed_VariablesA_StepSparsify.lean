-- Prove2me | Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
-- name    : VariableBound_Printed_VariablesA_StepSparsify
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:04:22.655612+00:00
-- url     : https://prove2.me/theorems/793fbce0-4a48-41aa-ac4b-6f7ecd09d858
-- title:
--   Step Sparsify
-- statement:
--   Definitions and structural lemmas for Step Sparsify, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/StepSparsify.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.VariablesA
open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)
end VariableBound.VariablesA


