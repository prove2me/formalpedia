-- Prove2me | Definitions.Def_GwExact_Check
-- name    : GwExact_Check
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:18:29.29025+00:00
-- url     : https://prove2.me/theorems/56486955-e7ba-4659-8d2e-1c73ad9de2f6
-- title:
--   Check
-- statement:
--   Definitions and structural lemmas for Check, from arhancanli and contributors's pinned Exact Gallai–van der Waerden numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Check.lean

module
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GwExact
structure Cls where
  p : Nat
  n : Nat
def Cls.Holds (σ : Nat → Bool) (c : Cls) : Prop :=
  ∃ v, (c.p.testBit v = true ∧ σ v = true) ∨ (c.n.testBit v = true ∧ σ v = false)
inductive Trie where
  | leaf : Trie
  | node : Trie → Option Cls → Trie → Trie
def Trie.find : Trie → Nat → Option Cls
  | .leaf, _ => none
  | .node l v r, k =>
    cond (Nat.beq k 0) v
      (cond (Nat.beq (Nat.land k 1) 1) (Trie.find l (Nat.shiftRight k 1))
        (Trie.find r (Nat.sub (Nat.shiftRight k 1) 1)))
def Trie.left : Trie → Trie
  | .leaf => .leaf
  | .node l _ _ => l
def Trie.val : Trie → Option Cls
  | .leaf => none
  | .node _ v _ => v
def Trie.right : Trie → Trie
  | .leaf => .leaf
  | .node _ _ r => r
def Trie.ins : Nat → Trie → Nat → Cls → Trie
  | 0, t, _, _ => t
  | f + 1, t, k, c =>
    cond (Nat.beq k 0) (.node t.left (some c) t.right)
      (cond (Nat.beq (Nat.land k 1) 1) (.node (Trie.ins f t.left (Nat.shiftRight k 1) c) t.val t.right)
        (.node t.left t.val (Trie.ins f t.right (Nat.sub (Nat.shiftRight k 1) 1) c)))
def readLits : Nat → Nat → Nat → Nat → Cls × Nat
  | 0, code, p, n => (⟨p, n⟩, code)
  | c + 1, code, p, n =>
    cond (Nat.beq (Nat.land code 1) 1)
      (readLits c (Nat.shiftRight code 10)
        (Nat.lor p (Nat.shiftLeft 1 (Nat.shiftRight (Nat.land code 1023) 1))) n)
      (readLits c (Nat.shiftRight code 10) p
        (Nat.lor n (Nat.shiftLeft 1 (Nat.shiftRight (Nat.land code 1023) 1))))
def rup (src : Nat → Option Cls) (w wm : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | c + 1, code, t, f =>
    match src (Nat.land code wm) with
    | none => false
    | some cl =>
      let rp := Nat.xor cl.p (Nat.land cl.p f)
      let rn := Nat.xor cl.n (Nat.land cl.n t)
      cond (Nat.beq rp 0)
        (cond (Nat.beq rn 0) true
          (cond (Nat.beq (Nat.land rn (Nat.sub rn 1)) 0)
            (rup src w wm c (Nat.shiftRight code w) t (Nat.lor f rn)) false))
        (cond (Nat.beq rn 0 && Nat.beq (Nat.land rp (Nat.sub rp 1)) 0)
          (rup src w wm c (Nat.shiftRight code w) (Nat.lor t rp) f) false)
def run (src : Trie → Nat → Option Cls) (w wm : Nat) : Trie → Nat → List Nat → Bool
  | _, _, [] => false
  | db, i, s :: ss =>
    match readLits (Nat.land s 255) (Nat.shiftRight s 8) 0 0 with
    | (cl, rest) =>
      cond (rup (src db) w wm (Nat.land rest 255) (Nat.shiftRight rest 8) cl.n cl.p)
        (cond (Nat.beq cl.p 0 && Nat.beq cl.n 0) true
          (run src w wm (Trie.ins 32 db i cl) (Nat.add i 1) ss))
        false
def Good (σ : Nat → Bool) (db : Trie) : Prop :=
  ∀ k c, db.find k = some c → c.Holds σ
end GwExact


