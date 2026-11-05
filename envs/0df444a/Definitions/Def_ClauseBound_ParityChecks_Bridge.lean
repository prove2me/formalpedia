-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Bridge
-- name    : ClauseBound_ParityChecks_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:06:18.479122+00:00
-- url     : https://prove2.me/theorems/4932a071-960a-4482-b32e-b3d8d59ce1e3
-- title:
--   Bridge
-- statement:
--   Definitions and structural lemmas for Bridge, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
set_option autoImplicit false
section
section
@[expose] section
open Finset ParityChecks
namespace ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
end ClauseBound.ParityChecks.Bridge


