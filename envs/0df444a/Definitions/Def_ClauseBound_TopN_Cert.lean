-- Prove2me | Definitions.Def_ClauseBound_TopN_Cert
-- name    : ClauseBound_TopN_Cert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:53:31.921033+00:00
-- url     : https://prove2.me/theorems/eb82521c-20bc-43ec-af10-3bfe414d4253
-- title:
--   Cert
-- statement:
--   Definitions and structural lemmas for Cert, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Cert.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_PaddedDescent_F_CertEval
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.TopN.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open PaddedDescent.F.Mark (MCtx Cl cls nProf adm markF placeE)
variable {α : Type} [Enc α]
section count
variable {pad gu : α → U} {val : α → MCtx → ℤ} {p : α → U × U × U × U} {R : α → ℕ} {ψ : α → Fml}
end count
section par
variable {K n s : α → ℕ}
end par
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
end ClauseBound.TopN.Cert


