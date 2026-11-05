-- Prove2me | Definitions.Def_UniformInK_Cert_Walk
-- name    : UniformInK_Cert_Walk
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:54:15.774183+00:00
-- url     : https://prove2.me/theorems/369f365f-f726-42e8-983d-710237fe3c69
-- title:
--   Walk
-- statement:
--   Definitions and structural lemmas for Walk, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Walk.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSatRate_Cert
set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert
namespace CertWalk
variable {α : Type} [Enc α]
end CertWalk
end UniformInK


