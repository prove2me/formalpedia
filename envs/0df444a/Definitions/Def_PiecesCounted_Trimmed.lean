-- Prove2me | Definitions.Def_PiecesCounted_Trimmed
-- name    : PiecesCounted_Trimmed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:05:59.786209+00:00
-- url     : https://prove2.me/theorems/f353a8e5-67f6-4d87-8559-2a6b0e83cfa1
-- title:
--   Trimmed
-- statement:
--   Definitions and structural lemmas for Trimmed, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
@[expose] def trimmed (D : Data) : Data where
  fam lam :=
    { d := (D.fam lam).d
      I := (D.fam lam).I
      A := (D.fam lam).A
      crow := fun i => min ((D.fam lam).crow i) (2 * lam)
      ccol := fun i => min ((D.fam lam).ccol i) (2 * lam) }
  fn lam tr side i z θ :=
    if D.cap lam tr i ≤ 2 * lam then D.fn lam tr side i z θ
    else if side then
      (if tr then (D.fam lam).A i (toBits lam (θ.take lam)) z.1 (toBits lam (θ.drop lam)) z.2
      else (D.fam lam).A i (toBits lam (θ.take lam)) (toBits lam (θ.drop lam)) z.1 z.2)
    else if bitsOf z.1 ++ bitsOf z.2 = θ then 1 else 0
@[expose] def firstQ (g : List Unit × Question) : List Unit × Question :=
  (g.1, g.2.elim (fun _ => g.2) fun q => q.elim (fun _ => g.2) fun q => q.elim (fun _ => g.2) fun q => q.elim (fun _ => g.2) fun q => .inr (.inr (.inl (q.1.1, q.2.1))))
@[expose] def afterFirst (p : (List Unit × Question) × Answer) : Answer ⊕ (List Unit × Question) :=
  p.1.2.elim (fun _ => .inl p.2) fun q => q.elim (fun _ => .inl p.2) fun q =>
    q.elim (fun _ => .inl (p.2.elim (fun z => .inl (if z ≤ ((2 * p.1.1.length : ℕ) : ℤ) then z else ((2 * p.1.1.length : ℕ) : ℤ))) fun l => .inr l)) fun q =>
      q.elim (fun _ => .inl p.2) fun q =>
        if p.2.elim (fun z => z) (fun _ => 0) ≤ ((2 * p.1.1.length : ℕ) : ℤ) then .inr p.1
        else bif q.1.2 then
          .inr (p.1.1, .inr (.inr (.inr (.inl (q.2.1, bif q.1.1 then (q.2.2.2.2.take p.1.1.length, q.2.2.1, q.2.2.2.2.drop p.1.1.length, q.2.2.2.1)
            else (q.2.2.2.2.take p.1.1.length, q.2.2.2.2.drop p.1.1.length, q.2.2.1, q.2.2.2.1))))))
        else .inl (.inl (if q.2.2.1 ++ q.2.2.2.1 = q.2.2.2.2 then 1 else 0))
@[expose] def assumeAlg (Alg : Stepped (List Unit × Question) Answer) : Stepped (List Unit × Question) Answer :=
  Stepped.bind (Stepped.mapIn firstQ Alg) (Stepped.branch afterFirst (Stepped.ofFun fun a : Answer => a) Alg)
end PiecesCounted


