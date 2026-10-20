-- Prove2me | Definitions.Def_AngelDevil_KingGuard
-- name    : AngelDevil_KingGuard
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:19:58.203225+00:00
-- url     : https://prove2.me/theorems/95cbe8ff-d08e-4598-b095-32791652ed58
-- title:
--   Finite line guards and a box invariant for king capture
-- statement:
--   A finite line-guard strategy tree records five possible preparation burns and all king displacements. Four oriented copies guard a square box. The interface also specifies the corner preparation list, the finite board, and the burned-set projection. These are auxiliary definitions for formalizing the published chess-king capture argument, with radius 100 and 56 preparatory selections.
-- source:
--   Martin Kutz, The Angel Problem, Positional Games, and Digraph Roots (2004), Chapter 1, Section 1.1, pp. 2-3, Figures 1-3. https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf. Finite strategy certificate for Figure 2; index 4 represents five burns. The box constants implement the same argument with generous margins.

import Definitions.Def_AngelDevil_Game
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod

namespace AngelDevil

def kingOffset (i : Fin 3) : Int := (i.val : Int) - 1

def guardSquare (x : Int) (i : Fin 11) : Int := x + (i.val : Int) - 5

def KingGuard : Nat → Int → Finset Int → Prop
  | 0, x, B => ∃ i : Fin 11, ∀ j : Fin 3,
      x + kingOffset j ∈ insert (guardSquare x i) B
  | n+1, x, B => ∃ i : Fin 11, ∀ j : Fin 3,
      KingGuard n (x + kingOffset j) (insert (guardSquare x i) B)

def kingNormal (s : Fin 4) (p : Point) : Int :=
  if s = 0 then p.1 else if s = 1 then p.2 else if s = 2 then -p.1 else -p.2

def kingTangent (s : Fin 4) (p : Point) : Int :=
  if s = 0 ∨ s = 2 then p.2 else p.1

def kingWallPoint (s : Fin 4) (x : Int) : Point :=
  if s = 0 then (100,x) else if s = 1 then (x,100)
  else if s = 2 then (-100,x) else (x,-100)

@[irreducible] def kingBoard : Finset Point := Finset.univ.image
  (fun p : Fin 201 × Fin 201 => ((p.1.val : Int)-100, (p.2.val : Int)-100))

def kingLineBurns (s : Fin 4) (B : Finset Point) : Finset Int :=
  (B.filter fun p => kingNormal s p = 100).image (kingTangent s)

def kingCorners : List Point := (List.finRange 4).flatMap fun s =>
  (List.range 7).flatMap fun (k : Nat) => [kingWallPoint s (-100+(k:Int)), kingWallPoint s (100-(k:Int))]

def KingLineReady (s : Fin 4) (p : Point) (B : Finset Point) : Prop :=
  ∃ n : Nat, n ≤ 4 ∧ (n:Int)+1 ≤ 100-kingNormal s p ∧
    KingGuard n (kingTangent s p) (kingLineBurns s B)

def KingBoxReady (p : Point) (B : Finset Point) : Prop :=
  (∀ z ∈ kingCorners, z ∈ B) ∧
  (∀ s : Fin 4, kingNormal s p < 100) ∧
  ∀ s : Fin 4, KingLineReady s p B

def kingBurned (s : State) : Finset Point := (s.burned.filterMap id).toFinset

end AngelDevil


