-- Prove2me | Definitions.Def_PiecesCounted_Padded
-- name    : PiecesCounted_Padded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:07:50.653845+00:00
-- url     : https://prove2.me/theorems/efa53283-84a2-4492-95c3-5407e7c5570f
-- title:
--   Padded
-- statement:
--   Definitions and structural lemmas for Padded, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
@[expose] def answerOf (P : PiecesF) (val : AppRunningTime.ValQ → ℤ) (shift : ℕ → ℤ) (x : (List Unit × Question) × List Unit) : Answer :=
  x.1.2.elim (fun _ => .inl (P.d 0 x.1.1.length : ℤ)) fun q =>
    q.elim (fun _ => .inr ((List.range (P.cnt 0 x.1.1.length)).map fun i : ℕ => (i : ℤ) + shift x.1.1.length)) fun q =>
      q.elim (fun q => .inl (P.cap q.1 0 x.1.1.length (q.2 - shift x.1.1.length).toNat : ℤ)) fun q =>
        q.elim (fun q => .inl (val (x.2, (x.1.1, (q.1 - shift x.1.1.length).toNat), q.2))) fun q =>
          .inl (bif q.1.2 then P.bot ((x.2, q.1.1), (0, (q.2.1 - shift x.1.1.length).toNat), q.2.2) else P.top ((x.2, q.1.1), (0, (q.2.1 - shift x.1.1.length).toNat), q.2.2))
@[expose] def algOf (P : PiecesF) (val : AppRunningTime.ValQ → ℤ) (k : ℕ) (shift : ℕ → ℤ) : Stepped (List Unit × Question) Answer :=
  padThen (fun g => 2 ^ (k * g.1.length)) (answerOf P val shift)
end PiecesCounted


