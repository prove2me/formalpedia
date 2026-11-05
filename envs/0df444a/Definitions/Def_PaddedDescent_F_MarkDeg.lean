-- Prove2me | Definitions.Def_PaddedDescent_F_MarkDeg
-- name    : PaddedDescent_F_MarkDeg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:08:19.507583+00:00
-- url     : https://prove2.me/theorems/70506d89-ba20-461f-b6f8-9a916daef01e
-- title:
--   Mark Deg
-- statement:
--   Definitions and structural lemmas for Mark Deg, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
set_option autoImplicit false
section
namespace PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
section fin
variable {α : Type*} [DecidableEq α] {θ : ℕ → ℕ} {k : ℕ} {F : Finset (Finset α)}
end fin
end PaddedDescent.F.Mark.Deg
namespace PaddedDescent.F
end PaddedDescent.F


