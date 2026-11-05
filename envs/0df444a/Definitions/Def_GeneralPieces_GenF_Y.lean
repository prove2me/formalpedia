-- Prove2me | Definitions.Def_GeneralPieces_GenF_Y
-- name    : GeneralPieces_GenF_Y
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:28:42.79619+00:00
-- url     : https://prove2.me/theorems/6d11436b-896b-43a6-98c2-6c8ce95e25a3
-- title:
--   Y
-- statement:
--   Definitions and structural lemmas for Y, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
section Yent
variable {R : Type} [CommRing R] [Algebra ℚ R]
noncomputable def Yent (e : ℤ → R) (b : List ℕ) (τ σ : Multiset ℕ) : R := ((op b ((τ.sum : ℤ) - σ.sum) τ σ : ℤ) : ℚ) • e ((τ.sum : ℤ) - σ.sum - b.sum)
end Yent
namespace Y
variable {Z R : Type} [CommRing R] [Algebra ℚ R]
end Y
open Y
noncomputable def outer (rd : Bool) (σ' : Multiset ℕ) : W := expW (Bp rd) * ket rd σ'
namespace Y
noncomputable def cB (rd : Bool) (k : ℕ) : X → S := sel rd 0 fun n => (bet n (-(k : ℤ)) : ℚ) • mo 0 (-(k : ℤ) - n)
end Y
end GeneralPieces.GenF


