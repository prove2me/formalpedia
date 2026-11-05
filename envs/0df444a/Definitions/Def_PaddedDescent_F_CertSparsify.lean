-- Prove2me | Definitions.Def_PaddedDescent_F_CertSparsify
-- name    : PaddedDescent_F_CertSparsify
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:35:48.783821+00:00
-- url     : https://prove2.me/theorems/97921527-02bf-4566-8114-2e39a44b607d
-- title:
--   Cert Sparsify
-- statement:
--   Definitions and structural lemmas for Cert Sparsify, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Theorems.Thm_WidthK_Prog_pickK_eq

set_option autoImplicit false
section
section
@[expose] section
namespace PaddedDescent.F.CertTop
open Groundwork Groundwork.Sparsify
open WidthK (thrPair theta)
open WidthK.Prog (pairsK pickK pickK_eq stepK)
variable {α σ : Type} [Enc α] [Enc σ]
end PaddedDescent.F.CertTop


