-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_CertTopOL
-- name    : ClauseBound_ParityChecks_CertTopOL
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:04:31.758751+00:00
-- url     : https://prove2.me/theorems/9a0391ff-4b05-46ec-b7f1-f1ae6db54e78
-- title:
--   Cert Top OL
-- statement:
--   Definitions and structural lemmas for Cert Top OL, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
section par
variable {K n s D : α → ℕ}
end par
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
end ClauseBound.ParityChecks.CertTopOL


