-- Prove2me | Definitions.Def_VariableBound_Search_Cert
-- name    : VariableBound_Search_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:10:42.807175+00:00
-- url     : https://prove2.me/theorems/2268848a-6c40-455d-8aff-eaee6dbf385a
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
end VariableBound.Search
namespace VariableBound
open Groundwork PaddedDescent.F
end VariableBound


