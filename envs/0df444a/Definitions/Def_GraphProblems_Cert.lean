-- Prove2me | Definitions.Def_GraphProblems_Cert
-- name    : GraphProblems_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:53:55.672943+00:00
-- url     : https://prove2.me/theorems/bf076325-fed9-4987-9cd2-c9f56b9bb183
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_CountKSat_Poly
set_option autoImplicit false
section
section
namespace GraphProblems
open Groundwork Groundwork.Prog CountKSat
variable {α : Type} [Enc α]
end GraphProblems


