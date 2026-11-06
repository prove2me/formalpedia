-- Prove2me | Definitions.Def_SplitCount_Tree
-- name    : SplitCount_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:29:23.460194+00:00
-- url     : https://prove2.me/theorems/1351de09-e933-4b2b-a2d6-9fc2c7647c08
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
set_option autoImplicit false
section
section
@[expose] section
namespace SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width
section maps
variable {σ ρ : Type} {s₁ : σ → Option (σ × σ)} {s₂ : ρ → Option (ρ × ρ)} {f : σ → ρ}
end maps
def withSide (t : PFml) (x : CNode) : CNode := (x.1, x.2 ++ t)
end SplitCount


