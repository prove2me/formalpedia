-- Prove2me | Definitions.Def_GeneralPieces_GenF_PDeriv
-- name    : GeneralPieces_GenF_PDeriv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:25:35.879889+00:00
-- url     : https://prove2.me/theorems/adf9dcbd-1860-4f07-a923-8587e5ea269d
-- title:
--   PDeriv
-- statement:
--   Definitions and structural lemmas for PDeriv, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/PDeriv.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Taylor
import Mathlib.RingTheory.MvPowerSeries.Derivative
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
end GeneralPieces.GenF


