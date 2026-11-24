-- Prove2me | Definitions.Def_ULHC_Chain
-- name    : ULHC_Chain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:24:43.259922+00:00
-- url     : https://prove2.me/theorems/dae4b3e8-5305-426a-9589-65f9e79f95f9
-- title:
--   Chain
-- statement:
--   Definitions and structural lemmas for Chain, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean

import Definitions.Def_ULHC_V2
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_ACell_dk

set_option autoImplicit true
namespace ULHC
open Finset Classical
def Inter (V : Finset Pt) (F : Finset Edge) (e : Edge) : Prop :=
  IsEdge V e ∧ e ∉ F ∧ ¬ Conn F e.p e.q
def triOK (ab ad ak bd bk dk : Bool) : Bool :=
  -- every triangle of corners is transitive
  ((ab && bd) <= ad) && ((ad && bd) <= ab) && ((ab && ad) <= bd) &&
  ((ab && bk) <= ak) && ((ak && bk) <= ab) && ((ab && ak) <= bk) &&
  ((ad && dk) <= ak) && ((ak && dk) <= ad) && ((ad && ak) <= dk) &&
  ((bd && dk) <= bk) && ((bk && dk) <= bd) && ((bd && bk) <= dk)
def bI (b : Bool) : ℕ := if b then 1 else 0
noncomputable def interCount (V : Finset Pt) (F : Finset Edge) (w : Pt) : ℕ :=
  (if Inter V F (bot w) then 1 else 0) + (if Inter V F (top w) then 1 else 0) +
    (if Inter V F (lft w) then 1 else 0) + (if Inter V F (rgt w) then 1 else 0)
section count
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F) (hT : NoTypeIII V F)
include hF hT
end count
section countLocal
variable {V : Finset Pt} {F : Finset Edge} (hF : Deg2 V F)
include hF
end countLocal
section potzero
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE
end potzero
def sidesIn (B : Finset Edge) (c : Pt) : ℕ := ind B (bot c) + ind B (top c) + ind B (lft c) + ind B (rgt c)
noncomputable def crossL (B : Finset Edge) : Pt → List Pt → ℕ
  | _, [] => 0
  | u, v :: l => (if ∃ e ∈ B, Ends e u v then 1 else 0) + crossL B v l
section chains
variable {G : Finset Edge}
end chains
noncomputable def GE (V : Finset Pt) : Finset Edge :=
  (V.biUnion (fun v => ({eR v, eU v} : Finset Edge))).filter (IsEdge V)
section sep
variable {V : Finset Pt} (B : Finset Edge)
def PStep (V : Finset Pt) (B : Finset Edge) (x y : Pt × Bool) : Prop :=
  Adj (GE V) x.1 y.1 ∧ y.2 = (x.2 ^^ decide (∃ e ∈ B, Ends e x.1 y.1))
variable (hs : Solid V) (heven : ∀ c, IsCell V c → sidesIn B c % 2 = 0)
include hs heven
end sep
noncomputable def nOn (c : Pt) (s : Side) (n : ℕ) (e : Edge) : ℕ :=
  ((Finset.range n).filter (fun j => e ∈ cellE (cellJ c s j))).card
section flipfacts
variable (c : Pt) (s : Side)
end flipfacts
def CAdj (V : Finset Pt) (F : Finset Edge) (c c' : Pt) : Prop :=
  IsCell V c ∧ IsCell V c' ∧ ∃ e, Inter V F e ∧ e ∈ cellE c ∧ e ∈ cellE c'
noncomputable def chainCells (V : Finset Pt) (F : Finset Edge) (c0 : Pt) : Finset Pt :=
  (cells V).filter (fun c => Relation.ReflTransGen (CAdj V F) c0 c)
noncomputable def EB (V : Finset Pt) (F : Finset Edge) (c0 : Pt) : Finset Edge :=
  (GE V).filter (fun e => Inter V F e ∧ ∃ c ∈ chainCells V F c0, e ∈ cellE c)
section chainsep
variable {V : Finset Pt} {F : Finset Edge}
end chainsep
end ULHC


