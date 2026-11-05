-- Prove2me | Definitions.Def_GeneralPieces_GenF_Commute
-- name    : GeneralPieces_GenF_Commute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:27:54.868497+00:00
-- url     : https://prove2.me/theorems/5f311440-473a-4b68-80b9-87c7764a07ed
-- title:
--   Commute
-- statement:
--   Definitions and structural lemmas for Commute, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Commute.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
open MvPowerSeries hiding C X
@[expose] noncomputable def kq (rd : Bool) (i i' : X) : S := sel rd (fun p => sel rd 0 (fun q => kapS p q) i') 0 i
end GeneralPieces.GenF


