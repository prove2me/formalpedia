-- Prove2me | Definitions.Def_Eight_Level_Presents
-- name    : Eight_Level_Presents
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:51:53.641897+00:00
-- url     : https://prove2.me/theorems/b1a6aa12-30bf-4844-ae9e-4512894e30c8
-- title:
--   Presents
-- statement:
--   Definitions and structural lemmas for Presents, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Presents.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Presents
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped SingleBitPieces.Level.Presents
namespace Presents
def netP8 (P : PiecesF) (g : ℕ) (tr : Bool) : NetFormer := fun lam R =>
  { n := fun c _ => nMemb g g tr * (g * g) * lam c.1
    cap := fun c a b => capG P g g tr 0 (lam c.1) c.2 a b
    W := sideWP g tr lam R
    f := ofFun fun x => gridFf P [] g g tr 0 (lam x.1.1) x.1.2 x.2 }
end Presents
open Presents
end Eight.Level


