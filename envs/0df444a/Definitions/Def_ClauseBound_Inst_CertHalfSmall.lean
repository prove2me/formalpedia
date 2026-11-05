-- Prove2me | Definitions.Def_ClauseBound_Inst_CertHalfSmall
-- name    : ClauseBound_Inst_CertHalfSmall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:44:26.072922+00:00
-- url     : https://prove2.me/theorems/9bfefa48-7475-4406-878b-cc5f399baee5
-- title:
--   Cert Half Small
-- statement:
--   Definitions and structural lemmas for Cert Half Small, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]
end ClauseBound.Inst.Half.CertSmall


