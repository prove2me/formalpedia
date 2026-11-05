-- Prove2me | Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
-- name    : GeneralPieces_DefGenPieces_MayAssume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:27:01.712937+00:00
-- url     : https://prove2.me/theorems/34aa363f-ebc8-4def-8105-cbb0236dd007
-- title:
--   May Assume
-- statement:
--   Definitions and structural lemmas for May Assume, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/DefGenPieces/MayAssume.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
namespace GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime
namespace DefGenPieces
open Trim
end DefGenPieces
open DefGenPieces Trim
section
variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}
end
end GeneralPieces


