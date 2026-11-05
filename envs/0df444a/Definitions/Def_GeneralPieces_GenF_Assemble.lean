-- Prove2me | Definitions.Def_GeneralPieces_GenF_Assemble
-- name    : GeneralPieces_GenF_Assemble
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:27:57.790197+00:00
-- url     : https://prove2.me/theorems/a3aaae76-8d9b-40a9-a10d-166976af9ab3
-- title:
--   Assemble
-- statement:
--   Definitions and structural lemmas for Assemble, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
@[expose] noncomputable def ex (a b : List ℕ) : X →₀ ℕ := aL Sum.inl a + aL Sum.inr b
end GeneralPieces.GenF
namespace GeneralPieces
open GeneralPieces.Series GeneralPieces.GenF ClauseBound.Boson MvPowerSeries Finset
end GeneralPieces


