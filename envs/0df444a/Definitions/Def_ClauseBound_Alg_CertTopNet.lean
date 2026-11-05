-- Prove2me | Definitions.Def_ClauseBound_Alg_CertTopNet
-- name    : ClauseBound_Alg_CertTopNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:33:28.982349+00:00
-- url     : https://prove2.me/theorems/250aae1b-2301-417a-8ce7-c6797d469ea0
-- title:
--   Cert Top Net
-- statement:
--   Definitions and structural lemmas for Cert Top Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTopNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.CertTopNet
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F
variable {α : Type} [Enc α]
end ClauseBound.Alg.CertTopNet


