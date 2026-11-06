-- Prove2me | Definitions.Def_SparsifyThenCount_CertTop
-- name    : SparsifyThenCount_CertTop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:06:38.628297+00:00
-- url     : https://prove2.me/theorems/ed34c7db-a2a0-46b0-b1a5-3ff73317c40b
-- title:
--   Cert Top
-- statement:
--   Definitions and structural lemmas for Cert Top, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
set_option autoImplicit false
section
section
@[expose] section
namespace SparsifyThenCount
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.CertTop SparsificationLemma
end SparsifyThenCount


