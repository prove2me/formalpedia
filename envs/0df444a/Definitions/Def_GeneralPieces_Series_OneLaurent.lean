-- Prove2me | Definitions.Def_GeneralPieces_Series_OneLaurent
-- name    : GeneralPieces_Series_OneLaurent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:31.165577+00:00
-- url     : https://prove2.me/theorems/1df0b452-8ad1-4abd-a5bf-a2f4a4902a12
-- title:
--   One Laurent
-- statement:
--   Definitions and structural lemmas for One Laurent, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
set_option autoImplicit false
section
section
namespace GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}
noncomputable def Expansion.F (X : Expansion a b G π σ) : L := (X.terms.map fun c => c.1 • (dW ^ (a.sum + b.sum - c.2.1) * c.2.2)).sum
noncomputable def ev : L →ₐ[ℚ] ℚ := AddMonoidAlgebra.lift ℚ ℚ (ℤ × ℤ) 1
end GeneralPieces.Series


