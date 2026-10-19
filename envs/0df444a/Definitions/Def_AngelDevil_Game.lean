-- Prove2me | Definitions.Def_AngelDevil_Game
-- name    : AngelDevil_Game
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T12:47:14.248414+00:00
-- url     : https://prove2.me/theorems/90fbf190-12a8-4c28-b928-2e095a71ed60
-- title:
--   Angel and Devil: infinite-board game and strategies
-- statement:
--   Integer lattice game with Devil-first rounds, passing, history-dependent strategies, legal survival, Nice Devil restrictions, unbounded escape, and confinement of every finite safe prefix. Conventions follow Sections 1-2, Definitions 2.2, 2.3, 2.5 and equation (2).
-- source:
--   Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. Sections 1-2, manuscript pp. 1-3.

import Std

/-! The convention is Mathe's paper: Devil moves first, may pass, and may
eat any square (including the occupied square); only subsequent landing on
an eaten square loses. Zero-length Angel moves are allowed by Definition 2.5.
Histories are stored oldest first. Strategies are total also off legal play.
-/
namespace AngelDevil

abbrev Point := Int × Int
def origin : Point := (0, 0)

def Jump (p : Nat) (u v : Point) : Prop :=
  -(p : Int) ≤ v.1 - u.1 ∧ v.1 - u.1 ≤ (p : Int) ∧
  -(p : Int) ≤ v.2 - u.2 ∧ v.2 - u.2 ≤ (p : Int)

def InBox (N : Nat) (v : Point) : Prop := Jump N origin v

def Journey (p : Nat) (h : List Point) : Prop :=
  h.head? = some origin ∧
  ∀ (i : Nat) (u v : Point), h[i]? = some u → h[i+1]? = some v → Jump p u v

abbrev DevilStrategy := List Point → Option Point
abbrev AngelStrategy := List Point → List (Option Point) → Point

structure State where
  visited : List Point
  burned : List (Option Point)

def initial : State := ⟨[origin], []⟩
def current (s : State) : Point := s.visited.getLastD origin
def step (A : AngelStrategy) (D : DevilStrategy) (s : State) : State :=
  let burned := s.burned ++ [D s.visited]
  ⟨s.visited ++ [A s.visited burned], burned⟩

def play (A : AngelStrategy) (D : DevilStrategy) : Nat → State
  | 0 => initial
  | n+1 => step A D (play A D n)

def Survives (p : Nat) (A : AngelStrategy) (D : DevilStrategy) : Prop :=
  ∀ n, Jump p (current (play A D n)) (current (play A D (n+1))) ∧
    some (current (play A D (n+1))) ∉ (play A D (n+1)).burned

def AngelWins (p : Nat) : Prop := ∃ A, ∀ D, Survives p A D

/- Definition 2.2, as made explicit by equation (2): the origin and every
square reachable from a position before the last one are protected. -/
def Nice (p : Nat) (D : DevilStrategy) : Prop :=
  ∀ h, Journey p h → ∀ z, D h = some z →
    z ≠ origin ∧ ∀ v ∈ h.dropLast, ¬ Jump p v z

def Escapes (A : AngelStrategy) (D : DevilStrategy) : Prop :=
  ∀ N : Nat, ∃ n : Nat, ¬ InBox N (current (play A D n))

def NiceAngelWins (p : Nat) : Prop :=
  ∃ A, ∀ D, Nice p D → Survives p A D ∧ Escapes A D

def NiceCanConfine (p N : Nat) : Prop :=
  ∃ D, Nice p D ∧ ∀ A n,
    (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
    InBox N (current (play A D n))

end AngelDevil


