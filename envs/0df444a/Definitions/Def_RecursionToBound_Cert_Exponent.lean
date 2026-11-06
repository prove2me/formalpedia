-- Prove2me | Definitions.Def_RecursionToBound_Cert_Exponent
-- name    : RecursionToBound_Cert_Exponent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:06:58.421191+00:00
-- url     : https://prove2.me/theorems/e46fd515-668a-48f0-8980-3ab41fee3ca8
-- title:
--   Exponent
-- statement:
--   Definitions and structural lemmas for Exponent, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ToTuring_Poly_NetFun
set_option autoImplicit false
section
section
@[expose] section
namespace RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
end RecursionToBound


