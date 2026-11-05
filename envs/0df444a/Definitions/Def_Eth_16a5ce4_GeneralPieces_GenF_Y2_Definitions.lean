-- Prove2me | Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
-- name    : Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:28:40.48254+00:00
-- url     : https://prove2.me/theorems/f98f071f-7eaf-49d0-ac8d-630cc7cfd162
-- title:
--   Y2
-- statement:
--   Definitions and structural lemmas for Y2, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset
@[expose] noncomputable def y0 : List ℕ → Multiset ℕ → (Vu →ₗ[Lu] Lu)
  | [], σ => MvPolynomial.lcoeff Lu (Multiset.toFinsupp σ)
  | n :: a, σ => ∑ l ∈ σ.toFinset, (C (bet n l : ℚ) * T ((l : ℤ) - n)) • y0 a (σ.erase l) + (y0 a σ).comp (JmU n).toLinearMap
@[expose] noncomputable def GG (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (w : W) : PS := braW σ (expW (Ap rd E) * Phi rd w)
end GeneralPieces.GenF


