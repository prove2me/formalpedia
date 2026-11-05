-- Prove2me | Definitions.Def_ClauseBound_Inst_CertHalfTab
-- name    : ClauseBound_Inst_CertHalfTab
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:33:47.42702+00:00
-- url     : https://prove2.me/theorems/5d6eafe9-0d7a-42c0-b1e3-316e9e79407f
-- title:
--   Cert Half Tab
-- statement:
--   Definitions and structural lemmas for Cert Half Tab, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
end ClauseBound.Inst.Half


