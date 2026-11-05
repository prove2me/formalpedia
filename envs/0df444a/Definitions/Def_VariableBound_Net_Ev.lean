-- Prove2me | Definitions.Def_VariableBound_Net_Ev
-- name    : VariableBound_Net_Ev
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:05:02.276394+00:00
-- url     : https://prove2.me/theorems/c58ae288-7939-416a-a36e-41e89dbd1bc0
-- title:
--   Ev
-- statement:
--   Definitions and structural lemmas for Ev, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Ev.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Tactic.Positivity
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net.Ev
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
open ClauseBound.ParityChecks (Vof)
end VariableBound.Net.Ev


