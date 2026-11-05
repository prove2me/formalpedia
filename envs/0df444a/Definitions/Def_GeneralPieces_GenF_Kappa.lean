-- Prove2me | Definitions.Def_GeneralPieces_GenF_Kappa
-- name    : GeneralPieces_GenF_Kappa
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:26:30.439555+00:00
-- url     : https://prove2.me/theorems/a5ec90ce-d899-48d3-86c6-a065c9fa8fbd
-- title:
--   Kappa
-- statement:
--   Definitions and structural lemmas for Kappa, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Kappa.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Exp
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset
@[expose] noncomputable def wtX : (X →₀ ℕ) →+ ℕ := Finsupp.weight (Sum.elim id id : X → ℕ)
@[expose] def GamX (i i' : X) : ℚ := sel false (fun p => sel false 0 (fun q => (Gam p q : ℚ)) i') 0 i
@[expose] noncomputable def kapQ : MvPowerSeries X ℚ := bil GamX
@[expose] noncomputable def gam (α : X →₀ ℕ) : ℚ := coeff α (expW kapQ)
end GeneralPieces.GenF


