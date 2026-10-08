-- Prove2me | Definitions.Def_OneWayLiveness
-- name    : OneWayLiveness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.402324+00:00
-- url     : https://prove2.me/theorems/c86579a6-8571-4181-8cbc-502166dbe61e
-- statement:
--   This block sets up one-way liveness as a language of words over binary relations and the one-way automata that might recognize it. For a type H, BRel(H) is a binary relation on H, given as a proposition holds(x,y). Relations form a monoid under relational composition, (a·b)(x,z) iff some y has a(x,y) and b(y,z), with equality as the identity. A word w (a list of relations) is live if its ordered product relates some pair x,y, meaning there is a path through the relations in order. For h a natural number, the alphabet is the set of relations on Fin h, and OWL(h) is the set of live words over that alphabet. For automata, a tape symbol is a left endmarker, a letter, or a right endmarker, and scanned(w,i) gives the symbol at position i of w framed by both endmarkers, so positions run over Fin(|w|+2). Moves are left, stay or right, with the corresponding changes in head position (left decreases by one, right increases by one). A configuration is a head position paired with a state. A deterministic machine DMachine with s states has an initial state, an accepting set, and a partial transition function from state and scanned symbol to an optional state and move. A nondeterministic machine NMachine with n states has the same data but its transition gives a set of state and move pairs. In both, the machine may never move left on the left endmarker or right on the right endmarker. A step changes configuration by applying an allowed transition to the scanned symbol and moving the head accordingly. A finite run is a chain of steps from one configuration to another. With the Boolean flag positive set to true it must have at least one step (transitive closure), and with false it may have length zero (reflexive-transitive closure). A machine accepts w if, starting at the left endmarker in the initial state, some finite run under the chosen convention reaches an accepting state. NoLeft says a nondeterministic machine has no transition moving left. Recognizes(positive,L) says that acceptance of every word w is equivalent to membership of w in L, for both machine types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OneWayLiveness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OneWayLiveness.lean; bytes 16..3802
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace OneWayLiveness

@[ext] structure BRel (H : Type*) where
  holds : H → H → Prop

namespace BRel
variable {H : Type*}
instance : One (BRel H) := ⟨⟨Eq⟩⟩
instance : Mul (BRel H) := ⟨fun a b => ⟨fun x z => ∃ y, a.holds x y ∧ b.holds y z⟩⟩
instance : Monoid (BRel H) where
  mul_assoc a b c := by
    ext x z
    change (∃ y, (∃ w, a.holds x w ∧ b.holds w y) ∧ c.holds y z) ↔
      ∃ w, a.holds x w ∧ ∃ y, b.holds w y ∧ c.holds y z
    aesop
  one_mul a := by ext x z; change (∃ y, x = y ∧ a.holds y z) ↔ a.holds x z; simp
  mul_one a := by ext x z; change (∃ y, a.holds x y ∧ y = z) ↔ a.holds x z; simp

/-- Nonemptiness is the existence of a path through the word's ordered product. -/
def live (w : List (BRel H)) : Prop := ∃ x y, w.prod.holds x y
end BRel

abbrev Alphabet (h : ℕ) := BRel (Fin h)
def OWL (h : ℕ) : Set (List (Alphabet h)) := {w | BRel.live w}

inductive Symbol (Alpha : Type*) where
  | left : Symbol Alpha
  | letter : Alpha → Symbol Alpha
  | right : Symbol Alpha

inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.Rel : Move → ℕ → ℕ → Prop
  | .left, i, j => j + 1 = i
  | .stay, i, j => j = i
  | .right, i, j => j = i + 1

/-- The finite word including both endmarkers. -/
def scanned {Alpha : Type*} (w : List Alpha) (i : Fin (w.length + 2)) : Symbol Alpha :=
  if h0 : i.val = 0 then .left
  else if hi : i.val < w.length + 1 then .letter (w[i.val - 1]'(by omega))
  else .right

abbrev Configuration {Alpha : Type*} (w : List Alpha) (n : ℕ) := Fin (w.length + 2) × Fin n

structure DMachine (Alpha : Type*) (s : ℕ) where
  initial : Fin s
  accepting : Set (Fin s)
  transition : Fin s → Symbol Alpha → Option (Fin s × Move)
  left_boundary : ∀ q q', transition q .left ≠ some (q', .left)
  right_boundary : ∀ q q', transition q .right ≠ some (q', .right)

structure NMachine (Alpha : Type*) (n : ℕ) where
  initial : Fin n
  accepting : Set (Fin n)
  transition : Fin n → Symbol Alpha → Set (Fin n × Move)
  left_boundary : ∀ q q', (q', .left) ∉ transition q .left
  right_boundary : ∀ q q', (q', .right) ∉ transition q .right

def DMachine.Step {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s) (w : List Alpha)
    (c c' : Configuration w s) : Prop :=
  ∃ d, M.transition c.2 (scanned w c.1) = some (c'.2, d) ∧ d.Rel c.1.val c'.1.val

def NMachine.Step {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) (w : List Alpha)
    (c c' : Configuration w n) : Prop :=
  ∃ d, (c'.2, d) ∈ M.transition c.2 (scanned w c.1) ∧ d.Rel c.1.val c'.1.val

/-- The positive convention explicitly excludes a length-zero computation. -/
def FiniteRun {C : Type*} (positive : Bool) (step : C → C → Prop) (c c' : C) : Prop :=
  if positive then Relation.TransGen step c c' else Relation.ReflTransGen step c c'

def DMachine.Accepts {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting

def NMachine.Accepts {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (w : List Alpha) : Prop :=
  ∃ c, FiniteRun positive (M.Step w) (⟨0, by omega⟩, M.initial) c ∧ c.2 ∈ M.accepting

def NMachine.NoLeft {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n) : Prop :=
  ∀ q a q', (q', Move.left) ∉ M.transition q a

def NMachine.Recognizes {Alpha : Type*} {n : ℕ} (M : NMachine Alpha n)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L

def DMachine.Recognizes {Alpha : Type*} {s : ℕ} (M : DMachine Alpha s)
    (positive : Bool) (L : Set (List Alpha)) : Prop := ∀ w, M.Accepts positive w ↔ w ∈ L



end OneWayLiveness
end OAI


