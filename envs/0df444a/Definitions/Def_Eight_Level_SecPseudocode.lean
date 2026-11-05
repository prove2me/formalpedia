-- Prove2me | Definitions.Def_Eight_Level_SecPseudocode
-- name    : Eight_Level_SecPseudocode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T04:51:30.064569+00:00
-- url     : https://prove2.me/theorems/d678de6c-116a-43ed-a5f6-ee3b2b7833d4
-- title:
--   Sec Pseudocode
-- statement:
--   Definitions and structural lemmas for Sec Pseudocode, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/SecPseudocode.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Eight_Level_exists_level
import Theorems.Thm_Groundwork_TM_Run_trans

set_option autoImplicit false
section
section
namespace Eight.Level
open Groundwork Groundwork.Prog Paper
theorem exists_first {δ' : ℝ} (hδ' : 0 < δ') : ∃ ℓ, 72 / δ' ≤ levelK ℓ ∧ Eight.Level.levelE ℓ ≤ δ' / 12 := by
  obtain ⟨ℓ, h1, h2⟩ := Eight.Level.exists_level (η := δ' / 12) (by positivity) ⌈72 / δ'⌉₊
  exact ⟨ℓ, (Nat.le_ceil _).trans (by exact_mod_cast h1), h2⟩
open Classical in
/-- Header of Algorithm 1: «ℓ is the first level with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12». Same as in the
paper. -/
noncomputable def firstLevel {δ' : ℝ} (hδ' : 0 < δ') : ℕ := Nat.find (exists_first hδ')
section
variable (hL : StLevel) (hLK : StLevelKeeps)
end
end Eight.Level


