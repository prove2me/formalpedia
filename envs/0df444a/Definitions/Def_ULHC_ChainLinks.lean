-- Prove2me | Definitions.Def_ULHC_ChainLinks
-- name    : ULHC_ChainLinks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:01:19.000448+00:00
-- url     : https://prove2.me/theorems/9912bad8-3e45-49f3-a181-1d418ecb12b6
-- title:
--   Chain Links
-- statement:
--   Definitions and structural lemmas for Chain Links, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean

import Definitions.Def_ULHC_NearLemma
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Ends_conn

set_option autoImplicit true
namespace ULHC
open Finset
def ChainOK (b c : StripSpec) : Prop :=
  ∀ j < c.n, ∀ x ∈ cellE (cellJ c.c c.s j), x ∈ cellE (endCell b) →
    j = 0 ∧ (x = lat1 (endCell b) b.s ∨ x = lat2 (endCell b) b.s)
def CATail : List StripSpec → Prop
  | [] => True
  | [_] => True
  | b :: c :: L => ChainOK b c ∧ CATail (c :: L)
def CRPathCA (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) (L : List StripSpec) : Prop :=
  CRPath V G σ L ∧ CATail (σ :: L)
section chain
variable {V : Finset Pt} {G : Finset Edge}
end chain
section conn
variable {V : Finset Pt} {S : Finset Edge}
end conn
def FarLinkCA (G : Finset Edge) (a σ τ : StripSpec) : Prop :=
  (∀ j < a.n, ∀ e ∈ cellE (endCell σ), e ∉ cellE (cellJ a.c a.s j)) ∧
    ¬ IsMid a.c a.s (a.n - 2) (back1 (endCell σ) σ.s) ∧
    ¬ IsMid a.c a.s (a.n - 2) (back2 (endCell σ) σ.s) ∧
    (∀ i < τ.n, ∀ j < a.n, ∀ e ∈ cellE (cellJ τ.c τ.s i), e ∉ cellE (cellJ a.c a.s j)) ∧
    ¬ IsMid a.c a.s (a.n - 2) (back1 τ.c τ.s) ∧ ¬ IsMid a.c a.s (a.n - 2) (front1 τ.c τ.s) ∧
    (NoChain σ τ → ¬ (Conn G (back1 τ.c τ.s) (front1 τ.c τ.s) ∧
      ¬ Conn (flip G (endCell a)) (back1 τ.c τ.s) (front1 τ.c τ.s)))
def FarChainCA (G : Finset Edge) (a : StripSpec) : StripSpec → List StripSpec → Prop
  | _, [] => True
  | σ, τ :: L => FarLinkCA G a σ τ ∧ FarChainCA G a τ L
section transfer
variable {V : Finset Pt} {G : Finset Edge} (hG : Deg2 V G) (hT : NoTypeIII V G)
  {a : StripSpec} (ha : ValidStrip V G a) (hae : a.n % 2 = 0) (ha2 : 2 ≤ a.n)
  (hT' : NoTypeIII V (applyS G a))
include hG hT ha hae ha2 hT'
end transfer
end ULHC


