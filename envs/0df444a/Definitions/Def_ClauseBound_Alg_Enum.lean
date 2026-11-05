-- Prove2me | Definitions.Def_ClauseBound_Alg_Enum
-- name    : ClauseBound_Alg_Enum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:35:47.415863+00:00
-- url     : https://prove2.me/theorems/b444a97d-883a-46e9-a129-b74fb6fbd4b8
-- title:
--   Enum
-- statement:
--   Definitions and structural lemmas for Enum, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
section identity
variable {J σ τ : Type} [Fintype J] [LinearOrder J]
end identity
section place
variable {g : ℕ}
def pos (p : Fin g × Fin g) : ℕ := p.1.val * g + p.2.val
end place
section prog
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}
def term (F : FNet C) (c : C) (t : Fin g × Fin g → List Bool) : ℤ :=
  ∏ a : Fin g, ∑ z ∈ words (F.n c a), F.W (c, (a.val, z)) * ∏ b ∈ univ.erase a, F.f (c, ((a.val, b.val), (z, t (pr a b))))
end prog
end ClauseBound.Alg.Enum


