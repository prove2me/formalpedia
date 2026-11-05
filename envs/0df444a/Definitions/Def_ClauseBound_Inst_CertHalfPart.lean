-- Prove2me | Definitions.Def_ClauseBound_Inst_CertHalfPart
-- name    : ClauseBound_Inst_CertHalfPart
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:09:42.672221+00:00
-- url     : https://prove2.me/theorems/99ebb41b-9720-4761-ab96-fb390c8f6035
-- title:
--   Cert Half Part
-- statement:
--   Definitions and structural lemmas for Cert Half Part, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]
end ClauseBound.Inst.Half


