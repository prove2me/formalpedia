-- Prove2me | Definitions.Def_GeneralPieces_Group_CaseII
-- name    : GeneralPieces_Group_CaseII
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:36:17.351871+00:00
-- url     : https://prove2.me/theorems/448433aa-729f-45c4-8398-c95b42dd0337
-- title:
--   Case II
-- statement:
--   Definitions and structural lemmas for Case II, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Group/CaseII.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Group_Grouping
set_option autoImplicit false
section
section
namespace GeneralPieces.Group
open Finset ClauseBound.Group ClauseBound.Group.Grouping
variable {K n : ℕ}
noncomputable def cz {g : ℕ} (c : Fin g → Fin g → ℕ) (a b : Fin g) : ℝ := if a = b then 0 else (c a b : ℝ)
noncomputable def cs {g : ℕ} (c : Fin g → Fin g → ℕ) (a : Fin g) : ℝ := ∑ b, cz c a b
noncomputable def tot {g : ℕ} (c : Fin g → Fin g → ℕ) : ℝ := ∑ a, cs c a
noncomputable def Yg (c : Fin (K * n) → Fin (K * n) → ℕ) (e : Equiv.Perm (Fin (K * n))) (γ γ' : Fin K) : ℝ := ∑ a ∈ cls e γ, ∑ b ∈ cls e γ', (c a b : ℝ)
end GeneralPieces.Group
namespace GeneralPieces
open Finset ClauseBound.Group.Grouping GeneralPieces.Group
end GeneralPieces


