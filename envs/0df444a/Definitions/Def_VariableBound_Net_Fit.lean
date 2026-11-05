-- Prove2me | Definitions.Def_VariableBound_Net_Fit
-- name    : VariableBound_Net_Fit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:03:36.995677+00:00
-- url     : https://prove2.me/theorems/16444663-817f-4e0c-8c7b-e228bdee8432
-- title:
--   Fit
-- statement:
--   Definitions and structural lemmas for Fit, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Fit.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
end VariableBound.Net.FitL


