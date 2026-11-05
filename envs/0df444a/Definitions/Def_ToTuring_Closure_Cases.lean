-- Prove2me | Definitions.Def_ToTuring_Closure_Cases
-- name    : ToTuring_Closure_Cases
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:46:55.234906+00:00
-- url     : https://prove2.me/theorems/1415a88b-9d2c-4aa4-bf2b-1d24aaef69eb
-- title:
--   Cases
-- statement:
--   Definitions and structural lemmas for Cases, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_Groundwork_TM_Frag_Within_seq

set_option autoImplicit false
section
section
namespace Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
def tagHead : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym) :=
  .pop .main (fun _ o => o) <|
    .branch (fun s => s == some (.bit true)) (.load (fun _ => none) <| .goto fun _ => true)
      (.load (fun _ => none) <| .goto fun _ => false)
def nilHead : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym) :=
  .pop .main (fun _ _ => none) <| .peek .main (fun _ o => o) <| .push .main (fun _ => .L) <|
    .branch (fun s => s == some .R) (.load (fun _ => none) <| .goto fun _ => false)
      (.load (fun _ => none) <| .goto fun _ => true)
def tagF (b : Bool) : Fr := (pushW [.bit b]).seq consF
def listSplit : List β → Unit ⊕ β × List β
  | [] => .inl ()
  | e :: r => .inr (e, r)
end Groundwork.PolyT


