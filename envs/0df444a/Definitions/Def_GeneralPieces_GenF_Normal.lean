-- Prove2me | Definitions.Def_GeneralPieces_GenF_Normal
-- name    : GeneralPieces_GenF_Normal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:28:44.510599+00:00
-- url     : https://prove2.me/theorems/ecdc8987-2492-4cd8-981e-121bb73ede37
-- title:
--   Normal
-- statement:
--   Definitions and structural lemmas for Normal, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
section Generic
variable {Y A : Type} [CommRing A] [Algebra ℚ A]
end Generic
end GeneralPieces.GenF


