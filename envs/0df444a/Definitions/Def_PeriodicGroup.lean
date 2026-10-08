-- Prove2me | Definitions.Def_PeriodicGroup
-- name    : PeriodicGroup
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:24.447917+00:00
-- url     : https://prove2.me/theorems/3d4e339a-3e31-447f-a732-517da6d27450
-- statement:
--   A root for index size n is an ordered pair of distinct indices (row, col) in Fin n, and a generator is a pair of a root and a ring element. The commutator bracket(x,y) is x y x⁻¹ y⁻¹. Writing letter(p,a) for the free-group generator attached to (p,a), the Steinberg group Steinberg(n,R) of a ring R is the quotient of the free group on all such generators by the normal closure of three families of relations: additivity, letter(p,a+b) = letter(p,a)·letter(p,b); commutation, bracket(letter(p,a), letter(q,b)) = 1 whenever p.col ≠ q.row and p.row ≠ q.col (this includes q = p); and multiplication, for pairwise distinct i, j, k, bracket(letter((i,j),a), letter((j,k),b)) = letter((i,k), a·b). A group G is Periodic if every element g has some positive integer m with g^m = 1; no uniform bound on m is required. MainStatement is a defined proposition (not an established theorem) asserting that there exist a ring R, in a type of the lowest universe, with an algebra structure over ZMod 2 such that Steinberg(12,R) is simultaneously infinite, finitely presented, and periodic. BurnsideStatement is the defined proposition that some group, in the lowest universe, is infinite, finitely presented, and periodic.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PeriodicGroup.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PeriodicGroup.lean; bytes 16..1564
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u

namespace SourceBurnside

structure Root (n : ℕ) where
  row : Fin n
  col : Fin n
  ne : row ≠ col
  deriving DecidableEq

abbrev Generator (n : ℕ) (R : Type u) := Root n × R

def bracket {G : Type u} [Group G] (x y : G) : G := x * y * x⁻¹ * y⁻¹

def letter {n : ℕ} {R : Type u} (p : Root n) (a : R) :
    FreeGroup (Generator n R) := FreeGroup.of (p, a)

inductive SteinbergRel (n : ℕ) (R : Type u) [Ring R] :
    FreeGroup (Generator n R) → Prop
  | add (p : Root n) (a b : R) :
      SteinbergRel n R (letter p (a + b) * (letter p a * letter p b)⁻¹)
  | commute (p q : Root n) (h₁ : p.col ≠ q.row) (h₂ : p.row ≠ q.col) (a b : R) :
      SteinbergRel n R (bracket (letter p a) (letter q b))
  | mul (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      SteinbergRel n R
        (bracket (letter ⟨i, j, hij⟩ a) (letter ⟨j, k, hjk⟩ b) *
          (letter ⟨i, k, hik⟩ (a * b))⁻¹)

def Steinberg (n : ℕ) (R : Type u) [Ring R] :=
  PresentedGroup {r | SteinbergRel n R r}
  deriving Group

def Periodic (G : Type u) [Group G] : Prop := ∀ g : G, ∃ m : ℕ, 0 < m ∧ g ^ m = 1

def MainStatement : Prop :=
  ∃ (R : Type) (_ : Ring R) (_ : Algebra (ZMod 2) R),
    Infinite (Steinberg 12 R) ∧ Group.IsFinitelyPresented (Steinberg 12 R) ∧
      Periodic (Steinberg 12 R)

def BurnsideStatement : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.IsFinitelyPresented G ∧ Periodic G

end SourceBurnside

namespace SourceBurnside



end SourceBurnside
end OAI


