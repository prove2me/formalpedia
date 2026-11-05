-- Prove2me | Definitions.Def_Eight_ViaGrouping_GridPsiDefs
-- name    : Eight_ViaGrouping_GridPsiDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:50:34.594094+00:00
-- url     : https://prove2.me/theorems/ac8d0c4d-a61a-453f-8524-2c0fb718116b
-- title:
--   Grid Psi Defs
-- statement:
--   Definitions and structural lemmas for Grid Psi Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsiDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecLevel_GridDefs
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Eight.SecNetworks Eight.Level
def rectPsi (g : ℕ) (tr : Bool) (lam y a b : ℕ) (z z' : List Bool) (i i' : ℕ) : ℤ :=
  aMul (digit (tOf lam) y (rectIxG g tr (tri a b) (tri i i')),
    bif tr then (heG g g lam z i (nodeG g tr b i'), heG g g lam z' i (nodeG g tr a i'), heG g g lam z i' (nodeG g tr b i), heG g g lam z' i' (nodeG g tr a i))
    else (heG g g lam z i (nodeG g tr b i'), heG g g lam z i' (nodeG g tr b i), heG g g lam z' i (nodeG g tr a i'), heG g g lam z' i' (nodeG g tr a i)))
def psiLt (g : ℕ) (tr : Bool) (lam y a b : ℕ) (z z' : List Bool) : ℤ :=
  bif (List.range g).all fun i => heG g g lam z i (nodeG g tr b i) == heG g g lam z' i (nodeG g tr a i) then
    prodL (g * g) fun j => if j / g < j % g then rectPsi g tr lam y a b z z' (j / g) (j % g) else 1
  else 0
def gridPsi (g : ℕ) (tr : Bool) (lam y : ℕ) (q : PsiQ) : ℤ :=
  if q.1.1 < q.1.2 then psiLt g tr lam y q.1.1 q.1.2 q.2.1 q.2.2 else psiLt g tr lam y q.1.2 q.1.1 q.2.2 q.2.1
def StGridPsi : Prop := ∀ (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)), 1 ≤ lam → ∀ a b : Fin (nParts g g tr), a ≠ b →
  ∀ z ∈ (netOfι g tr lam y Rm).S a, ∀ z' ∈ (netOfι g tr lam y Rm).S b, gridPsi g tr lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z'
def StGridPsiPoly : Prop := ∀ (g : ℕ) (tr : Bool) (C : Type) [Enc C] (lam : C → ℕ), Unary lam → PolyT fun x : (C × ℕ) × PsiQ => gridPsi g tr (lam x.1.1) x.1.2 x.2
end Eight.ViaGrouping


