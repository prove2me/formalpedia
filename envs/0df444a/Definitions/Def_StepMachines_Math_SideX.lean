-- Prove2me | Definitions.Def_StepMachines_Math_SideX
-- name    : StepMachines_Math_SideX
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:07:04.747823+00:00
-- url     : https://prove2.me/theorems/c569a5a8-2168-4a48-9c2d-8ed095508efd
-- title:
--   Side X
-- statement:
--   Definitions and structural lemmas for Side X, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideX.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SideNet
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
def sideChunk (g : ℕ) (tr : Bool) (n y a b : ℕ) (θ : List Bool) (κ : ℕ) : List Bool :=
  chunkAt (rectLen g tr n y (tri (min a b) (max a b))) κ (θ.drop (g * n))
def sideItem (g : ℕ) (tr : Bool) (n y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : ℤ :=
  cutW tr (decide (a < b)) (rectDig g tr n y (tri (min a b) (max a b)) (tri i i'))
    (he g n z i (node g tr b i')) (he g n z i' (node g tr b i)) (sideChunk g tr n y a b θ (tri i i'))
section core
variable {g n : ℕ}
end core
end Groundwork.Grid


