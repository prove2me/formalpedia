-- Prove2me | Definitions.Def_CountedRecursion_RowPairRun
-- name    : CountedRecursion_RowPairRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:57:53.783046+00:00
-- url     : https://prove2.me/theorems/3037ec5d-34e2-4347-9d94-8569843c7887
-- title:
--   Row Pair Run
-- statement:
--   Definitions and structural lemmas for Row Pair Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
def pairLoop : QueryMachine UpQuery Ans (Parent × PsiQ) ℤ :=
  QueryMachine.ite (fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2)
    (QueryMachine.prodRange (fun x : Parent × PsiQ => pG x.1 * pG x.1)
      (QueryMachine.ite (fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × PsiQ) × ℕ => Sum.inr (rectQuestion v)) (QueryMachine.const 1)))
    (QueryMachine.const 0)
def pairItem (D : PiecesCounted.Data) (c g : ℕ) (tr : Bool) (lam y : ℕ) (q : PsiQ) (j : ℕ) : ℤ :=
  if j / g < j % g then pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri q.1.1 q.1.2) (tri (j / g) (j % g)))) (rectStrings g tr lam q (j / g) (j % g)) else 1
end ExplicitCost


