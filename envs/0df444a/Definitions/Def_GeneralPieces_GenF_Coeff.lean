-- Prove2me | Definitions.Def_GeneralPieces_GenF_Coeff
-- name    : GeneralPieces_GenF_Coeff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:26:00.187275+00:00
-- url     : https://prove2.me/theorems/512307b5-e02e-48c5-a911-baa2f0a6efe2
-- title:
--   Coeff
-- statement:
--   Definitions and structural lemmas for Coeff, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Coeff.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_PDeriv
import Mathlib.Data.Finsupp.Multiset
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open Finset MvPowerSeries
variable {X A : Type} [CommRing A] [Algebra ℚ A]
noncomputable def fac (α : X →₀ ℕ) : ℚ := α.prod fun _ m => (m.factorial : ℚ)
end GeneralPieces.GenF


