-- Prove2me | Definitions.Def_ToTuring_TM_Rename
-- name    : ToTuring_TM_Rename
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:28.972462+00:00
-- url     : https://prove2.me/theorems/0313890b-7b9a-4dd1-ad6a-a426a1628d44
-- title:
--   Rename
-- statement:
--   Definitions and structural lemmas for Rename, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
def renK : TM2.Stmt (fun _ : K₁ => A) Λ σ → TM2.Stmt (fun _ : K₂ => A) Λ σ
  | .push k f q => .push (φ k) f (renK q)
  | .peek k f q => .peek (φ k) f (renK q)
  | .pop k f q => .pop (φ k) f (renK q)
  | .load f q => .load f (renK q)
  | .branch p q₁ q₂ => .branch p (renK q₁) (renK q₂)
  | .goto l => .goto l
  | .halt => .halt
def Frag.ren (P : Frag (fun _ : K₁ => A) σ) : Frag (fun _ : K₂ => A) σ where
  Λ := P.Λ
  entry := P.entry
  m l := renK φ (P.m l)
end Groundwork.TM


