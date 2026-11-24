-- Prove2me | Definitions.Def_ULHC_Algorithm
-- name    : ULHC_Algorithm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:03:26.556919+00:00
-- url     : https://prove2.me/theorems/4d33e76d-b485-4ba6-8506-64815d2e8c52
-- title:
--   Algorithm
-- statement:
--   Definitions and structural lemmas for Algorithm, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean

import Definitions.Def_ULHC_LinkGraph
import Theorems.Thm_ULHC_APair_flip
import Theorems.Thm_ULHC_Good_step

set_option autoImplicit true
namespace ULHC
open Finset
def cellList (V : Finset Pt) : List Pt :=
  (((V.filter (IsCell V)).map toLex.toEmbedding).sort (· ≤ ·)).map ofLex
def sidesL : List Side := [.b, .t, .l, .r]
def t3B (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) : Bool :=
  decide (back d tf ∈ G) && decide (front d tf ∈ G) && decide (lat1 d tf ∉ G) &&
    decide (lat2 d tf ∉ G) && !connB V G (back1 d tf) (front1 d tf)
def findT3 (V : Finset Pt) (G : Finset Edge) : Option (Pt × Side) :=
  ((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).find? fun p => t3B V G p.1 p.2
def step (V : Finset Pt) (G : Finset Edge) : Option (Finset Edge) :=
  match findT3 V G with
  | some (d, _) => some (flip G d)
  | none =>
    match findPath V G with
    | some (a, _) => some (applyS G a)
    | none => none
def run (V : Finset Pt) : ℕ → Finset Edge → Bool
  | 0, G => cncomp V G == 1
  | k + 1, G =>
    if cncomp V G == 1 then true
    else match step V G with
      | some G' => run V k G'
      | none => false
def Bd (V : Finset Pt) : ℕ := 3 * (4 * V.card + V.card * (4 * V.card))
def Dm (V : Finset Pt) : ℕ := Bd V * V.card
def fuel (V : Finset Pt) : ℕ := (V.card + 1) * (2 * Dm V + 4) + 2
def ulhc (V : Finset Pt) : Bool :=
  match twoFactor V with
  | some F => run V (fuel V) F
  | none => false
end ULHC


