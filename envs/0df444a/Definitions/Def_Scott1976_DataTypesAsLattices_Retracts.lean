-- Prove2me | Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
-- name    : Scott1976_DataTypesAsLattices_Retracts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:54:27.134313+00:00
-- url     : https://prove2.me/theorems/c1c336b4-6d78-5ee6-a553-a6ebc5ed7dff
-- title:
--   Retracts
-- statement:
--   Definitions and structural lemmas for Retracts, from Lars Warren Ericson (catskillsresearch/scott1976; original Lean code Apache-2.0; non-Lean reference PDF excluded per NOTICE)'s pinned Dana Scott's Data Types as Lattices (1976): Pomega, continuous functions, fixed points, and lambda models development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
namespace Scott1976.DataTypesAsLattices
def comp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))
def IsRetract (a : Pomega) : Prop :=
  a = comp a a
def Fixpoints (f : Pomega → Pomega) : Set Pomega :=
  {x | f x = x}
def typed (u a : Pomega) : Prop :=
  u = funOf a u
def funRetract : Pomega :=
  graph (fun u => graph (fun x => funOf u x))
def arrowR (a b : Pomega) : Pomega :=
  graph (fun u => comp b (comp u a))
def fstC : Pomega := graph (fun u => funOf u (ofNat 0))
def sndC : Pomega := graph (fun u => funOf u (ofNat 1))
def pairSeq (x y : Pomega) : Pomega := seq2 x y
def tensorR (a b : Pomega) : Pomega :=
  graph (fun u =>
    pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))
def plusR (a b : Pomega) : Pomega :=
  graph (fun u =>
    condSet (funOf u (ofNat 0))
      (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
      (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))
def retractLe (a b : Pomega) : Prop :=
  a = comp a b ∧ a = comp b a
def gfpBelow (f : Pomega → Pomega) (b : Pomega) : Pomega :=
  fix (fun z => f z ∩ b)
def Icomb : Pomega := graph (fun x => x)
def diagC : Pomega := graph (fun u => pairSeq u u)
def evalC : Pomega :=
  graph (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)))
def curryC : Pomega :=
  graph (fun u => graph (fun x => graph (fun y => funOf u (pairSeq x y))))
def intR : Pomega :=
  graph fun u =>
    condSet u (ofNat 0) (condSet (predSet u) u topElem)
def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)
def boolR : Pomega :=
  graph (fun u => condSet u (ofNat 0) (ofNat 1))
def openR : Pomega :=
  graph (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u})
end Scott1976.DataTypesAsLattices


