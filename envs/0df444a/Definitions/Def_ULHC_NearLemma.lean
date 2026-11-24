-- Prove2me | Definitions.Def_ULHC_NearLemma
-- name    : ULHC_NearLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:00:19.970793+00:00
-- url     : https://prove2.me/theorems/df6b1cec-62db-414f-9d8e-0a60dea2d192
-- title:
--   Near Lemma
-- statement:
--   Definitions and structural lemmas for Near Lemma, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearLemma.lean

import Definitions.Def_ULHC_NearChain
set_option autoImplicit true
namespace ULHC
open Finset
def NoChain (b c : StripSpec) : Prop :=
  ∀ j < c.n, ∀ x ∈ cellE (cellJ c.c c.s j), x ∉ cellE (endCell b)
section linka
variable {V : Finset Pt} {G : Finset Edge} {a : StripSpec}
  (hG : Deg2 V G) (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
include hG ha hae ha2
end linka
section classifyW
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m i0 : ℕ} (hzw : SigFrom F z tf m i0)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hzw
end classifyW
section classify
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hs : Solid V) (x0 : Pt) (hconn : ∀ z ∈ V, Conn (GE V) x0 z)
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s)) (hT' : NoTypeIII V (flipCol F c s (k + 2)))
  {z : Pt} {tf : Side} {m : ℕ} (hz : StripPat F z tf m)
include hs x0 hconn hF hT hk hcell hpat hsep hT' hz
end classify
end ULHC


