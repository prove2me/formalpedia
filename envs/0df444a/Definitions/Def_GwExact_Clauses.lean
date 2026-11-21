-- Prove2me | Definitions.Def_GwExact_Clauses
-- name    : GwExact_Clauses
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:20:02.463125+00:00
-- url     : https://prove2.me/theorems/7c668b33-cd96-4f22-a7b2-9283bec3b28a
-- title:
--   Clauses
-- statement:
--   Definitions and structural lemmas for Clauses, from arhancanli and contributors's pinned Exact Gallai–van der Waerden numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Clauses.lean

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GwExact
def bit (v : Nat) : Nat := Nat.shiftLeft 1 v
def monoMask (R c a d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => Nat.lor (monoMask R c a d j) (bit (Nat.add (Nat.mul (Nat.add a (Nat.mul j d)) R) c))
def rep (R : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => Nat.lor (rep R i) (bit (Nat.mul i R))
def descCls (n R l code : Nat) : Option Cls :=
  let kind := Nat.land code 7
  let f1 := Nat.land (Nat.shiftRight code 3) 255
  let f2 := Nat.land (Nat.shiftRight code 11) 255
  let f3 := Nat.land (Nat.shiftRight code 19) 255
  let f4 := Nat.land (Nat.shiftRight code 27) 255
  let f5 := Nat.land (Nat.shiftRight code 35) 255
  cond (Nat.beq kind 0)
    (some ⟨Nat.shiftLeft (Nat.sub (bit R) 1) (Nat.mul f1 R), 0⟩)
  (cond (Nat.beq kind 1)
    (cond (Nat.blt f2 f3 && Nat.blt f3 R)
      (some ⟨0, Nat.lor (bit (Nat.add (Nat.mul f1 R) f2)) (bit (Nat.add (Nat.mul f1 R) f3))⟩) none)
  (cond (Nat.beq kind 2)
    (cond (Nat.ble 1 f2 && Nat.blt (Nat.add f1 (Nat.mul (Nat.sub l 1) f2)) n && Nat.blt f3 R)
      (some ⟨0, monoMask R f3 f1 f2 l⟩) none)
  (cond (Nat.beq kind 3)
    (cond (Nat.ble 1 f2 && Nat.blt (Nat.add f1 (Nat.mul 2 f2)) n && Nat.blt f3 R && Nat.blt f4 R &&
        Nat.blt f5 R && !Nat.beq f3 f4 && !Nat.beq f3 f5 && !Nat.beq f4 f5)
      (some ⟨0, Nat.lor (Nat.lor (bit (Nat.add (Nat.mul f1 R) f3))
        (bit (Nat.add (Nat.mul (Nat.add f1 f2) R) f4)))
        (bit (Nat.add (Nat.mul (Nat.add f1 (Nat.mul 2 f2)) R) f5))⟩) none)
  (cond (Nat.beq kind 4)
    (cond (Nat.blt 0 R) (some ⟨1, 0⟩) none)
  (cond (Nat.beq kind 5)
    (cond (Nat.ble 1 f2 && Nat.blt f2 R)
      (some ⟨Nat.shiftLeft (rep R f1) (Nat.sub f2 1), bit (Nat.add (Nat.mul f1 R) f2)⟩) none)
  none)))))
def gwSrc (n R l : Nat) (db : Trie) (h : Nat) : Option Cls :=
  cond (Nat.beq (Nat.land h 1) 1) (db.find (Nat.shiftRight h 1)) (descCls n R l (Nat.shiftRight h 1))
def checkGw (n R l : Nat) (steps : List Nat) : Bool :=
  run (gwSrc n R l) 44 17592186044415 .leaf 0 steps
structure GoodPos (n R l : Nat) (col : Nat → Nat) : Prop where
  lt : ∀ i, col i < R
  zero : col 0 = 0
  pred : ∀ i, 1 ≤ col i → ∃ j < i, col j + 1 = col i
  mono : ∀ a d, 1 ≤ d → a + (l - 1) * d < n → ∃ j < l, col (a + j * d) ≠ col a
  rb : ∀ a d, 1 ≤ d → a + 2 * d < n →
    ¬ (col a ≠ col (a + d) ∧ col a ≠ col (a + 2 * d) ∧ col (a + d) ≠ col (a + 2 * d))
def asg (R : Nat) (col : Nat → Nat) (v : Nat) : Bool := decide (col (v / R) = v % R)
end GwExact


