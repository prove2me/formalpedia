-- Prove2me | Definitions.Def_ULHC_AFlip
-- name    : ULHC_AFlip
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:43:00.800314+00:00
-- url     : https://prove2.me/theorems/1313e85b-fc8f-42ce-a487-de5857f0bd54
-- title:
--   AFlip
-- statement:
--   Definitions and structural lemmas for AFlip, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/AFlip.lean

import Definitions.Def_ULHC_Flip
set_option autoImplicit true
namespace ULHC
open Finset Classical
def Ends (e : Edge) (u v : Pt) : Prop := (e.p = u ∧ e.q = v) ∨ (e.p = v ∧ e.q = u)
section ends
variable {e : Edge} {u v : Pt}
end ends
structure ACell where
  a : Pt
  b : Pt
  d : Pt
  k : Pt
  e1 : Edge
  e2 : Edge
  l1 : Edge
  l2 : Edge
  h1 : Ends e1 a b
  h2 : Ends e2 d k
  h3 : Ends l1 a d
  h4 : Ends l2 b k
  ad : a ≠ d
  ak : a ≠ k
  bd : b ≠ d
  bk : b ≠ k
def ACell.res (C : ACell) (F : Finset Edge) : Finset Edge :=
  insert C.l2 (insert C.l1 ((F.erase C.e1).erase C.e2))
namespace ACell
variable (C : ACell)
end ACell
section abstract
variable {V : Finset Pt} {F : Finset Edge} (C : ACell)
  (hV : Inside V F) (hVa : C.a ∈ V) (hVb : C.b ∈ V) (hVd : C.d ∈ V) (hVk : C.k ∈ V)
  (he1 : C.e1 ∈ F) (he2 : C.e2 ∈ F) (hl1 : C.l1 ∉ F) (hl2 : C.l2 ∉ F)
  (hdeg2 : ∀ z, (Conn F C.a z ∨ Conn F C.d z) → deg F z = 2)
include hV hVa hVb hVd hVk he1 he2 hl1 hl2 hdeg2
end abstract
structure APair where
  a : Pt
  b : Pt
  m1 : Pt
  m2 : Pt
  t1 : Pt
  t2 : Pt
  eab : Edge
  eam : Edge
  ebm : Edge
  em : Edge
  et : Edge
  emt1 : Edge
  emt2 : Edge
  hab : Ends eab a b
  ham : Ends eam a m1
  hbm : Ends ebm b m2
  hm : Ends em m1 m2
  ht : Ends et t1 t2
  hmt1 : Ends emt1 m1 t1
  hmt2 : Ends emt2 m2 t2
  -- `m1`, `m2` differ from the other four corners.
  m1a : m1 ≠ a
  m1b : m1 ≠ b
  m1t1 : m1 ≠ t1
  m1t2 : m1 ≠ t2
  m2a : m2 ≠ a
  m2b : m2 ≠ b
  m2t1 : m2 ≠ t1
  m2t2 : m2 ≠ t2
def APair.res (P : APair) (F : Finset Edge) : Finset Edge :=
  (insert P.emt2 (insert P.emt1
    (((insert P.eab F).erase P.eam).erase P.ebm))).erase P.et
section pair
variable {V : Finset Pt} {F : Finset Edge} (P : APair)
  (hV : Inside V F) (hVa : P.a ∈ V) (hVb : P.b ∈ V) (hVm1 : P.m1 ∈ V) (hVm2 : P.m2 ∈ V)
  (hVt1 : P.t1 ∈ V) (hVt2 : P.t2 ∈ V)
  (heam : P.eam ∈ F) (hebm : P.ebm ∈ F) (hem : P.em ∈ F) (het : P.et ∈ F)
  (hd1 : deg F P.m1 = 2) (hd2 : deg F P.m2 = 2)
include hV hVa hVb hVm1 hVm2 hVt1 hVt2 heam hebm hem het hd1 hd2
end pair
end ULHC


