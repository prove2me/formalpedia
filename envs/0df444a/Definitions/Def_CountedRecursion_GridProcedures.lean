-- Prove2me | Definitions.Def_CountedRecursion_GridProcedures
-- name    : CountedRecursion_GridProcedures
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:42:45.318756+00:00
-- url     : https://prove2.me/theorems/fbc1dc35-4cf6-438f-8335-0cb80bf94055
-- title:
--   Grid Procedures
-- statement:
--   Definitions and structural lemmas for Grid Procedures, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridProcedures.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ExplicitCost_EntryDefs
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
abbrev Lists : Type := List ℤ × List ℕ × List ℕ
abbrev Parent : Type := (List Unit × List Unit) × (List Unit × List Unit) × Lists × (Bool × ℕ × ℕ)
abbrev Head : Type := List Unit × List Unit × List Unit
abbrev Ctx : Type := Head × Option Parent
def pK (p : Parent) : ℕ := p.1.1.length
def pG (p : Parent) : ℕ := p.1.2.length
def pLam (p : Parent) : ℕ := p.2.1.1.length
def pB (p : Parent) : ℕ := p.2.1.2.length
def pLists (p : Parent) : Lists := p.2.2.1
def pTr (p : Parent) : Bool := p.2.2.2.1
def pY (p : Parent) : ℕ := p.2.2.2.2.1
def pX (p : Parent) : ℕ := p.2.2.2.2.2
def hLev (h : Head) : ℕ := h.1.length
def hLam (h : Head) : ℕ := h.2.1.length
def hB (h : Head) : ℕ := h.2.2.length
def cLev (c : Ctx) : ℕ := hLev c.1
def cLam (c : Ctx) : ℕ := hLam c.1
def cB (c : Ctx) : ℕ := hB c.1
def parentOf (c : Ctx) : Parent := c.2.getD (([], []), ([], []), ([], [], []), (false, 0, 0))
def top (l lam B : ℕ) : Ctx := ((unary l, unary lam, unary B), none)
def listsAsPieces (l : Lists) : PiecesF where
  cnt _ _ := l.1.length
  d _ _ := 0
  cap tr _ lam i := min ((if tr = true then l.2.2 else l.2.1).getD i 0) (2 * lam)
  top _ := 0
  bot _ := 0
  need _ _ := 0
  bits _ _ := 0
  m := 1
def bitsOne (c g lam B : ℕ) : ℕ := g * B + g ^ 2 * (2 * lam) ^ c
def netP (p : Parent) : ℕ := pG p ^ 3 * pLam p
def netB (c : ℕ) (p : Parent) : ℕ := bitsOne c (pG p) (pLam p) (pB p)
def netLen (p : Parent) (_ : ℕ) : ℕ := nMemb (pG p) (pG p) (pTr p) * (pG p * pG p) * pLam p
def netCap (p : Parent) (a b : ℕ) : ℕ := capG (listsAsPieces (pLists p)) (pG p) (pG p) (pTr p) 0 (pLam p) (pY p) a b
def netData (c : ℕ) (p : Parent) : DataInput := (p.1, inputOf (pG p) (netP p) (netB c p) (netLen p) (netCap p))
abbrev UpQuery : Type := TableQuery ⊕ PieceQuery
def pointQuery (g : ℕ) (tr : Bool) (lam : ℕ) (q : WQ) (i : ℕ) : IQ :=
  (nodeG g tr q.1 i, (List.range (g * g)).map fun u => if u = nodeG g tr q.1 i then [] else heG g g lam q.2 i u)
def ordered (q : PsiQ) : PsiQ := if q.1.1 < q.1.2 then q else ((q.1.2, q.1.1), (q.2.2, q.2.1))
def straightOK (g : ℕ) (tr : Bool) (lam : ℕ) (q : PsiQ) : Bool :=
  (List.range g).all fun i => heG g g lam q.2.1 i (nodeG g tr q.1.2 i) == heG g g lam q.2.2 i (nodeG g tr q.1.1 i)
def rectStrings (g : ℕ) (tr : Bool) (lam : ℕ) (q : PsiQ) (i i' : ℕ) : List Bool × List Bool × List Bool × List Bool :=
  bif tr then (heG g g lam q.2.1 i (nodeG g tr q.1.2 i'), heG g g lam q.2.2 i (nodeG g tr q.1.1 i'), heG g g lam q.2.1 i' (nodeG g tr q.1.2 i), heG g g lam q.2.2 i' (nodeG g tr q.1.1 i))
  else (heG g g lam q.2.1 i (nodeG g tr q.1.2 i'), heG g g lam q.2.1 i' (nodeG g tr q.1.2 i), heG g g lam q.2.2 i (nodeG g tr q.1.1 i'), heG g g lam q.2.2 i' (nodeG g tr q.1.1 i))
def pieceAt (p : Parent) (r κ : ℕ) : ℤ := (pLists p).1.getD (digG (listsAsPieces (pLists p)) (pG p) (pTr p) 0 (pLam p) (pY p) r κ) 0
def rectQuestion (x : (Parent × PsiQ) × ℕ) : PieceQuery :=
  (x.1.1.2.1.1, .inr (.inr (.inr (.inl (pieceAt x.1.1 (tri x.1.2.1.1 x.1.2.1.2) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)),
    rectStrings (pG x.1.1) (pTr x.1.1) (pLam x.1.1) x.1.2 (x.2 / pG x.1.1) (x.2 % pG x.1.1))))))
def labelOK (g : ℕ) (tr : Bool) (lam : ℕ) (q : FQ) : Bool :=
  (List.range (nMemb g g tr)).all fun i => heG g g lam q.2.1 i (nodeG g tr q.1.2 i) == block lam i q.2.2
def factorQuestion (x : (Parent × FQ) × ℕ) : PieceQuery :=
  (x.1.1.2.1.1, .inr (.inr (.inr (.inr ((pTr x.1.1, !decide (x.1.2.1.1 < x.1.2.1.2)),
    pieceAt x.1.1 (tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2)) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1)),
    (heG (pG x.1.1) (pG x.1.1) (pLam x.1.1) x.1.2.2.1 (x.2 / pG x.1.1) (nodeG (pG x.1.1) (pTr x.1.1) x.1.2.1.2 (x.2 % pG x.1.1)),
     heG (pG x.1.1) (pG x.1.1) (pLam x.1.1) x.1.2.2.1 (x.2 % pG x.1.1) (nodeG (pG x.1.1) (pTr x.1.1) x.1.2.1.2 (x.2 / pG x.1.1)),
     chunkAt (lenG (listsAsPieces (pLists x.1.1)) (pG x.1.1) (pTr x.1.1) 0 (pLam x.1.1) (pY x.1.1) (tri (min x.1.2.1.1 x.1.2.1.2) (max x.1.2.1.1 x.1.2.1.2))) (tri (x.2 / pG x.1.1) (x.2 % pG x.1.1))
       (x.1.2.2.2.drop (pG x.1.1 * pLam x.1.1))))))))
def rowWeight : QueryMachine UpQuery Ans (Parent × WQ) ℤ :=
  QueryMachine.ite (fun x : Parent × WQ => chkG (pG x.1) (pG x.1) (pTr x.1) (pLam x.1) x.2)
    (QueryMachine.prodRange (fun x : Parent × WQ => pG x.1) (askInt fun v : (Parent × WQ) × ℕ => Sum.inl (toTable (pointQuery (pG v.1.1) (pTr v.1.1) (pLam v.1.1) v.1.2 v.2))))
    (QueryMachine.const 0)
def rowPair : QueryMachine UpQuery Ans (Parent × PsiQ) ℤ :=
  QueryMachine.mapIn (fun x : Parent × PsiQ => (x.1, ordered x.2))
    (QueryMachine.ite (fun x : Parent × PsiQ => straightOK (pG x.1) (pTr x.1) (pLam x.1) x.2)
      (QueryMachine.prodRange (fun x : Parent × PsiQ => pG x.1 * pG x.1)
        (QueryMachine.ite (fun v : (Parent × PsiQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × PsiQ) × ℕ => Sum.inr (rectQuestion v)) (QueryMachine.const 1)))
      (QueryMachine.const 0))
def rowFactor : QueryMachine UpQuery Ans (Parent × FQ) ℤ :=
  QueryMachine.ite (fun x : Parent × FQ => labelOK (pG x.1) (pTr x.1) (pLam x.1) x.2)
    (QueryMachine.prodRange (fun x : Parent × FQ => pG x.1 * pG x.1)
      (QueryMachine.ite (fun v : (Parent × FQ) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1)) (askInt fun v : (Parent × FQ) × ℕ => Sum.inr (factorQuestion v)) (QueryMachine.const 1)))
    (QueryMachine.const 0)
def gridProcsData (c : ℕ) : ProcsQ UpQuery Ans Parent where
  P := netP
  B := netB c
  len := netLen
  cap := netCap
  mem := QueryMachine.lift (Stepped.mapIn (fun _ => ()) (Stepped.const true))
  W := rowWeight
  Ψ := rowPair
  f := rowFactor
def calleeInput (c : ℕ) (y : Ctx × TableQuery) : Parent × X0 DataInput :=
  (parentOf y.1, ((netData c (parentOf y.1), pX (parentOf y.1)), toLists (pK (parentOf y.1)) (cLam y.1) y.2))
def procedure (c : ℕ) : QueryMachine UpQuery Ans (Ctx × TableQuery) Ans :=
  QueryMachine.mapOut (QueryMachine.mapIn (calleeInput c) (entryData.subst (gridProcsData c).answer)) Sum.inl
end ExplicitCost


