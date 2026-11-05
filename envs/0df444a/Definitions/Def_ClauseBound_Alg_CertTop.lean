-- Prove2me | Definitions.Def_ClauseBound_Alg_CertTop
-- name    : ClauseBound_Alg_CertTop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:19:58.695464+00:00
-- url     : https://prove2.me/theorems/178396aa-9a7b-4bd8-bb44-913dc6378409
-- title:
--   Cert Top
-- statement:
--   Definitions and structural lemmas for Cert Top, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_CertCount
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg.CertCount CountKSat CountKSat.Poly
variable {α : Type} [Enc α]
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
end ClauseBound.Alg.CertTop


