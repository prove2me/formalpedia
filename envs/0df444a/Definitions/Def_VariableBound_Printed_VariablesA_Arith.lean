-- Prove2me | Definitions.Def_VariableBound_Printed_VariablesA_Arith
-- name    : VariableBound_Printed_VariablesA_Arith
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:01:13.175302+00:00
-- url     : https://prove2.me/theorems/130b64eb-aec5-43dc-afd6-725ba69e0fe1
-- title:
--   Arith
-- statement:
--   Definitions and structural lemmas for Arith, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Arith.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)
end VariableBound.VariablesA


