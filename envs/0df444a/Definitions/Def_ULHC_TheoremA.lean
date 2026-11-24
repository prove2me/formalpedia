-- Prove2me | Definitions.Def_ULHC_TheoremA
-- name    : ULHC_TheoremA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:22:41.214478+00:00
-- url     : https://prove2.me/theorems/d97ac7ae-6aab-4f66-a499-977f8e490c30
-- title:
--   Theorem A
-- statement:
--   Definitions and structural lemmas for Theorem A, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean

import Definitions.Def_ULHC_Phase2
set_option autoImplicit true
namespace ULHC
open Finset Classical
structure StripSpec where
  c : Pt
  s : Side
  n : ℕ
def applyS (F : Finset Edge) (σ : StripSpec) : Finset Edge := flipCol F σ.c σ.s σ.n
def applySeq (F : Finset Edge) : List StripSpec → Finset Edge
  | [] => F
  | σ :: L => applySeq (applyS F σ) L
def ValidStrip (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : Prop :=
  1 ≤ σ.n ∧ StripPat F σ.c σ.s σ.n ∧ (∀ j < σ.n, IsCell V (cellJ σ.c σ.s j)) ∧
    ¬ Conn F (back1 σ.c σ.s) (front1 σ.c σ.s)
def ValidSeq (V : Finset Pt) : Finset Edge → List StripSpec → Prop
  | _, [] => False
  | F, [σ] => ValidStrip V F σ ∧ σ.n % 2 = 1
  | F, σ :: τ :: L => ValidStrip V F σ ∧ σ.n % 2 = 0 ∧ NoTypeIII V F ∧
      ValidSeq V (applyS F σ) (τ :: L)
section thmA
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
end thmA
def ValidChain (V : Finset Pt) : Finset Edge → List (List StripSpec) → Prop
  | _, [] => True
  | F, L :: Ls => ValidSeq V F L ∧ ValidChain V (applySeq F L) Ls
def applyChain (F : Finset Edge) : List (List StripSpec) → Finset Edge
  | [] => F
  | L :: Ls => applyChain (applySeq F L) Ls
end ULHC


