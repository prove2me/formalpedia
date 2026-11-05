-- Prove2me | Definitions.Def_VariableBound_Params_Cert
-- name    : VariableBound_Params_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:48:00.056599+00:00
-- url     : https://prove2.me/theorems/81529006-e282-4f3a-8e77-d8a3d778c854
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
namespace Cert
variable {α : Type} [Enc α]
end Cert
end VariableBound


