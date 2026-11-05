-- Prove2me | Definitions.Def_PaddedDescent_F_CertEval
-- name    : PaddedDescent_F_CertEval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:40:08.802903+00:00
-- url     : https://prove2.me/theorems/16bee81d-1586-450e-bfaa-492096ec5641
-- title:
--   Cert Eval
-- statement:
--   Definitions and structural lemmas for Cert Eval, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertTop
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
namespace PaddedDescent.F.CertEval
open Groundwork Groundwork.Prog
open PaddedDescent.F.Mark (Cl cls nProf adm markF dropE placeAt placeE)
variable {α : Type} [Enc α]
section choice
variable {ev : α → List Fml → ℤ} {w : α → ℕ} {Ls : α → List Fml} {C : α → Cl}
end choice
section count
variable {pad : α → U} {S : α → List Lvl × U} {p : α → U × U × U × U} {R : α → ℕ} {ψ : α → Fml}
end count
end PaddedDescent.F.CertEval


