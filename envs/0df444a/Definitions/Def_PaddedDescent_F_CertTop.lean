-- Prove2me | Definitions.Def_PaddedDescent_F_CertTop
-- name    : PaddedDescent_F_CertTop
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:37:47.314691+00:00
-- url     : https://prove2.me/theorems/14633ddf-2710-452e-b4f5-4eecad1e30a2
-- title:
--   Cert Top
-- statement:
--   Definitions and structural lemmas for Cert Top, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
set_option autoImplicit false
section
section
namespace PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]
end PaddedDescent.F.CertTop


