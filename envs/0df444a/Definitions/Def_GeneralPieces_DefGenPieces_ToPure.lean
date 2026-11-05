-- Prove2me | Definitions.Def_GeneralPieces_DefGenPieces_ToPure
-- name    : GeneralPieces_DefGenPieces_ToPure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:28:03.900281+00:00
-- url     : https://prove2.me/theorems/f1d345da-00d0-4be2-8476-641f90e5ce26
-- title:
--   To Pure
-- statement:
--   Definitions and structural lemmas for To Pure, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/ToPure.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
set_option autoImplicit false
section
section
namespace GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
namespace DefGenPieces
open Trim
end DefGenPieces
open DefGenPieces
end GeneralPieces


