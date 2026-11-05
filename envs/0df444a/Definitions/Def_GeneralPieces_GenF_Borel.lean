-- Prove2me | Definitions.Def_GeneralPieces_GenF_Borel
-- name    : GeneralPieces_GenF_Borel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:26:43.462362+00:00
-- url     : https://prove2.me/theorems/dc2fef7b-2fbc-4eed-b9d8-a3777f5eb91a
-- title:
--   Borel
-- statement:
--   Definitions and structural lemmas for Borel, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]
noncomputable def expo (L : List Y) : Y →₀ ℕ := (L.map fun i => Finsupp.single i 1).sum
noncomputable def pdL : List Y → MvPowerSeries Y R → MvPowerSeries Y R
  | [], F => F
  | i :: L, F => pdL L (pderiv R i F)
variable [Algebra ℚ R]
end GeneralPieces.GenF


