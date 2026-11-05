-- Prove2me | Definitions.Def_Eight_SecLevel_GridDefs
-- name    : Eight_SecLevel_GridDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:46:26.702843+00:00
-- url     : https://prove2.me/theorems/eba6aca1-3bdf-4f91-99d2-05be1253af0d
-- title:
--   Sec Level Grid Defs
-- statement:
--   Definitions and structural lemmas for Sec Level Grid Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Paper_SecLevel_Grid
import Definitions.Def_ClauseBound_Alg_GridNet
import Mathlib.Data.Sym.Sym2
set_option autoImplicit false
section
section
namespace Eight
open Finset Groundwork
open Paper (Rectangle rectangles Settings RowSetting)
variable {g lam : ℕ}
def patterns (g lam : ℕ) : Finset (Rectangle g → ℕ) := Grid.Pat (Fin g) (Fin g) (tOf lam)
noncomputable def Zι (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) : ℤ :=
  Grid.ZG W fun q => A lam (ι q)
def rowCut (lam i : ℕ) : Grid.Cut (Bits lam) (List Bool) where
  lab := words (crow lam i)
  top x y θ := fTop (false, i, List.ofFn x, List.ofFn y, θ)
  bot u v θ := fBot (false, i, List.ofFn u, List.ofFn v, θ)
  cap := crow lam i
def colCut (lam i : ℕ) : Grid.Cut (Bits lam) (List Bool) where
  lab := words (ccol lam i)
  top x u θ := fTop (true, i, List.ofFn x, List.ofFn u, θ)
  bot y v θ := fBot (true, i, List.ofFn y, List.ofFn v, θ)
  cap := ccol lam i
abbrev RowIndex (g lam : ℕ) : Type := Grid.RowLab (Fin g) (Bits lam) (List Bool)
noncomputable def rowNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    Network (Fin g) (RowSetting g lam) (RowIndex g lam) :=
  Grid.rowNet W (fun q => rowCut lam (ι q)) [] lam
noncomputable def colNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    Network (Fin g) (RowSetting g lam) (RowIndex g lam) :=
  Grid.rowNet (Grid.trInst W) (fun q => colCut lam (ι (q.2, q.1))) [] lam
end Eight
namespace Eight.Level
open Groundwork Groundwork.Prog ClauseBound.Alg.GridNet
open Paper (Rectangle)
def digOf (g lam y : ℕ) : Rectangle g → ℕ := fun q => digit (tOf lam) y (ixG g g q)
def patOf (g lam y : ℕ) : Rectangle g → ℕ := patG g g (tOf lam) y
end Eight.Level


