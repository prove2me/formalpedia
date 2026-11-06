-- Prove2me | Definitions.Def_RecursionToBound_Cert_Top
-- name    : RecursionToBound_Cert_Top
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:14:57.757272+00:00
-- url     : https://prove2.me/theorems/70c2cdda-66cd-4802-b85f-8d8360b96de8
-- title:
--   Top
-- statement:
--   Definitions and structural lemmas for Top, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Exponent
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_NetFun
set_option autoImplicit false
section
section
@[expose] section
namespace RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
end RecursionToBound


