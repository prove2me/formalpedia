-- Prove2me | Definitions.Def_AngelDevil_FiniteHorizon
-- name    : AngelDevil_FiniteHorizon
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:36:05.422047+00:00
-- url     : https://prove2.me/theorems/9b05ab5a-6341-49a0-8b72-335a6682a388
-- title:
--   Finite-horizon safety and bounded Angel moves
-- statement:
--   Safety for n rounds requires every one of the first n jumps to be legal and to avoid all squares selected so far. Finite-horizon winning means one Angel strategy is safe for that horizon against every Devil. Strategy inputs are visited and burned histories. Legal displacements are encoded by pairs of integers from 0 through 2p, translated by minus p in each coordinate. The encoding retains legal choices and replaces illegal choices by staying put.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript pp. 1-2: determinacy observation and Claim 2.1; auxiliary formalization definitions.

import Definitions.Def_AngelDevil_Game

namespace AngelDevil

def SafeFor (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat) : Prop :=
  ∀ m, m < n →
    Jump p (current (play A D m)) (current (play A D (m+1))) ∧
    some (current (play A D (m+1))) ∉ (play A D (m+1)).burned

def FiniteAngelWins (p n : Nat) : Prop := ∃ A, ∀ D, SafeFor p A D n

abbrev Observation := List Point × List (Option Point)
abbrev BoundedMove (p : Nat) := Fin (2*p+1) × Fin (2*p+1)

def decodeMove (p : Nat) (h : List Point) (d : BoundedMove p) : Point :=
  ((h.getLastD origin).1 + (d.1.val : Int) - (p : Int),
   (h.getLastD origin).2 + (d.2.val : Int) - (p : Int))

def boundedAngel (p : Nat) (f : Observation → BoundedMove p) : AngelStrategy :=
  fun h b => decodeMove p h (f (h, b))

/- Invalid off-path choices are replaced by staying put. Legal choices are
encoded exactly, so this changes no safe finite play. -/
noncomputable def encodeAngel (p : Nat) (A : AngelStrategy) :
    Observation → BoundedMove p := by
  classical
  intro o
  let v := A o.1 o.2
  let u := o.1.getLastD origin
  exact if hv : Jump p u v then
    (⟨(v.1-u.1+(p : Int)).toNat, by unfold Jump at hv; omega⟩,
     ⟨(v.2-u.2+(p : Int)).toNat, by unfold Jump at hv; omega⟩)
  else (⟨p, by omega⟩, ⟨p, by omega⟩)

end AngelDevil


