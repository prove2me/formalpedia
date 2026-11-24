-- Prove2me | Definitions.Def_ULHC_PathComplete
-- name    : ULHC_PathComplete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:59.338679+00:00
-- url     : https://prove2.me/theorems/23d9d81f-c39e-4750-b71d-e785b397da72
-- title:
--   Path Complete
-- statement:
--   Definitions and structural lemmas for Path Complete, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
set_option autoImplicit true
namespace ULHC
open Finset
section via
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
include hs x0 hconn hG hT ha hae ha2 hT'
end via
section source
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0)
  (ha2 : 2 ≤ a.n) (hT' : NoTypeIII V (applyS G a))
  {W : ℕ} (hmin : ∀ σ L', CRPathCA V G σ L' → W ≤ wt σ L')
include hs x0 hconn hG hT ha hae ha2 hT' hmin
end source
section gside
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d))
include hG hT hk hcell hpat hsep
end gside
section comp
variable {V : Finset Pt} {G : Finset Edge} {c : Pt} {d : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hG : Deg2 V G) (hT : NoTypeIII V G) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c d j)) (hpat : StripPat G c d (k + 2))
  (hsep : ¬ Conn G (back1 c d) (front1 c d)) (hT' : NoTypeIII V (flipCol G c d (k + 2)))
include hs x0 hconn hG hT hk hcell hpat hsep hT'
end comp
end ULHC


