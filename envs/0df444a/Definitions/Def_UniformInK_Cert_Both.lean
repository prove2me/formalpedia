-- Prove2me | Definitions.Def_UniformInK_Cert_Both
-- name    : UniformInK_Cert_Both
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:41:11.014978+00:00
-- url     : https://prove2.me/theorems/7a4b576e-6648-45d4-8508-3e20650f0725
-- title:
--   Both
-- statement:
--   Definitions and structural lemmas for Both, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Both.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_PaddedDescent_Col_CertG
set_option autoImplicit false
section
section
@[expose] section
namespace UniformInK.CertBoth
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
end UniformInK.CertBoth
namespace UniformInK
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK.CertBoth
end UniformInK


