-- Prove2me | Definitions.Def_ClauseBound_Alg_GridPresents
-- name    : ClauseBound_Alg_GridPresents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:42:04.569301+00:00
-- url     : https://prove2.me/theorems/a9ebda5f-a86f-4d78-a46a-0ca6f63dfe4f
-- title:
--   Grid Presents
-- statement:
--   Definitions and structural lemmas for Grid Presents, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
def item (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : ℤ :=
  (if a < b then P.top else P.bot) ((pad, tr), (h, digG P d tr h ℓ y (tri (min a b) (max a b)) (tri i i')),
    (heG p d ℓ z i (nodeG d tr b i'), heG p d ℓ z i' (nodeG d tr b i),
      chunkAt (lenG P d tr h ℓ y (tri (min a b) (max a b))) (tri i i') (θ.drop (nMemb p d tr * ℓ))))
section Net
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
variable (P pad p d tr h ℓ y)
end Net
end ClauseBound.Alg.GridPresents


