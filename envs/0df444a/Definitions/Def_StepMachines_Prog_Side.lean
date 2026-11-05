-- Prove2me | Definitions.Def_StepMachines_Prog_Side
-- name    : StepMachines_Prog_Side
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:08:31.674209+00:00
-- url     : https://prove2.me/theorems/69255f20-5c95-45d7-af76-2096b1b55d40
-- title:
--   Side
-- statement:
--   Definitions and structural lemmas for Side, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Side.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_CutProg
import Definitions.Def_StepMachines_Math_SideX
set_option autoImplicit false
section
section
namespace Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 rectDig sideChunk sideItem sideCap)
section W
variable {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ)
def sideChk (x : (C × ℕ) × WQ) : Bool :=
  ((List.range g).all fun i => (he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i)).all (!·)) &&
    (List.range g).all fun i => (List.range g).all fun i' =>
      decide (i' ≤ i) ||
        (he g (lam x.1.1) x.2.2 i (node g tr x.2.1 i') == he g (lam x.1.1) x.2.2 i' (node g tr x.2.1 i))
def sideLabels (ℓ a : ℕ) (z : List Bool) (i u : ℕ) : List Bool :=
  if u = node g tr a i then [] else he g ℓ z i u
def sideQuery (p : ((C × ℕ) × WQ) × ℕ) : C × IQ :=
  (p.1.1.1, (node g tr p.1.2.1 p.2, (List.range (g * g)).map (sideLabels g tr (lam p.1.1.1) p.1.2.1 p.1.2.2 p.2)))
def sideG (_ : (C × ℕ) × WQ) : ℕ := g
def sideWP [HasSize C] (R : Stepped (C × IQ) ℤ) : Stepped ((C × ℕ) × WQ) ℤ :=
  ite (sideChk g tr lam) (prodRange (sideG g) (mapIn (sideQuery g tr lam) R)) (const 0)
def sideWv (ℓ : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (chk : Bool) (a : ℕ) (z : List Bool) : ℤ :=
  if chk then
    ∏ i ∈ range g, (if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr ℓ a z i u) else 1)
  else 0
variable {g tr lam}
end W
def viewAt (g : ℕ) (tr : Bool) (n y a b : ℕ) (z θ : List Bool) (i i' : ℕ) : CutQ :=
  ((decide (a < b), rectDig g tr n y (tri (min a b) (max a b)) (tri i i')),
    (he g n z i (node g tr b i'), he g n z i' (node g tr b i), sideChunk g tr n y a b θ (tri i i')))
section F
variable {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ)
def sideEdges (x : (C × ℕ) × FQ) : Bool :=
  (List.range g).all fun i => he g (lam x.1.1) x.2.2.1 i (node g tr x.2.1.2 i) == block (lam x.1.1) i x.2.2.2
def sideIsRect (p : ((C × ℕ) × FQ) × ℕ) : Bool := decide (p.2 / g < p.2 % g)
def sideView (p : ((C × ℕ) × FQ) × ℕ) : CutQ :=
  viewAt g tr (lam p.1.1.1) p.1.1.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 (p.2 / g % g) (p.2 % g)
def sideNN (_ : (C × ℕ) × FQ) : ℕ := g * g
def sideFP [HasSize C] : Stepped ((C × ℕ) × FQ) ℤ :=
  ite (sideEdges g tr lam)
    (prodRange (sideNN g) (ite (sideIsRect g) (mapIn (sideView g tr lam) (cutP tr)) (const 1)))
    (const 0)
def sideFv (n y : ℕ) (edges : Bool) (a b : ℕ) (z θ : List Bool) : ℤ :=
  if edges then ∏ j ∈ range (g * g), (if j / g < j % g then sideItem g tr n y a b z θ (j / g) (j % g) else 1) else 0
variable {g tr lam}
end F
end Groundwork.Prog


