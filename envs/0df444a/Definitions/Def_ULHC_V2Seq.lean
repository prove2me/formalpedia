-- Prove2me | Definitions.Def_ULHC_V2Seq
-- name    : ULHC_V2Seq
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:29:07.480472+00:00
-- url     : https://prove2.me/theorems/58f6e8ab-242e-4559-a7d6-6c547df69583
-- title:
--   V2 Seq
-- statement:
--   Definitions and structural lemmas for V2 Seq, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean

import Definitions.Def_ULHC_Dual
set_option autoImplicit true
namespace ULHC
open Finset Classical
def endCell (σ : StripSpec) : Pt := cellJ σ.c σ.s (σ.n - 1)
def OnChain (V : Finset Pt) (F : Finset Edge) : Option Pt → Pt → Prop
  | none, _ => True
  | some u, c => c ∈ chainCells V F u
def ValidSeqA (V : Finset Pt) : Option Pt → Finset Edge → List StripSpec → Prop
  | _, _, [] => False
  | a, F, [σ] => ValidStrip V F σ ∧ σ.n % 2 = 1 ∧ OnChain V F a σ.c
  | a, F, σ :: τ :: L => ValidStrip V F σ ∧ σ.n % 2 = 0 ∧ NoTypeIII V F ∧ OnChain V F a σ.c ∧
      ValidSeqA V (some (endCell σ)) (applyS F σ) (τ :: L)
section thmA2
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
def AnchorOK (V : Finset Pt) (F : Finset Edge) : Option Pt → Prop
  | none => True
  | some u => (∃ e, e ∈ EB V F u) ∧
      (¬ NoTypeIII V F → ∃ d ∈ chainCells V F u, ¬ NotTypeIII V F d)
end thmA2
end ULHC


