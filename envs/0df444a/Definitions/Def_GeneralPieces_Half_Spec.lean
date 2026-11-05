-- Prove2me | Definitions.Def_GeneralPieces_Half_Spec
-- name    : GeneralPieces_Half_Spec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:47:27.057491+00:00
-- url     : https://prove2.me/theorems/fc5bebc5-5bf8-4c77-819e-5974cb5d4f46
-- title:
--   Spec
-- statement:
--   Definitions and structural lemmas for Spec, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Spec.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Consts
import Definitions.Def_GeneralPieces_Half_Size
import Definitions.Def_GeneralPieces_Trim_Prog
import Definitions.Def_ClauseBound_Inst_HalfAll
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half Finset
@[expose] noncomputable def halfA (lam i : ℕ) : Pieces.Four lam :=
  ClauseBound.Boson.ApcL (ell (ClauseBound.Part.hOf lam)) (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)
end GeneralPieces


