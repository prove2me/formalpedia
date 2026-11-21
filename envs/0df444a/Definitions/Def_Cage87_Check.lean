-- Prove2me | Definitions.Def_Cage87_Check
-- name    : Cage87_Check
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T20:18:12.155179+00:00
-- url     : https://prove2.me/theorems/111cfbd9-f4d3-4611-a844-1089b33ca346
-- title:
--   Check
-- statement:
--   Definitions and structural lemmas for Check, from arhancanli and contributors's pinned 8-regular graph of girth 7 on 768 vertices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Check.lean

module
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Cage87
inductive Trie where
  | leaf : List Nat → Trie
  | node : Trie → Trie → Trie
def Trie.find : Trie → Nat → List Nat
  | .leaf l, _ => l
  | .node a b, v => cond (Nat.beq (Nat.mod v 2) 0) (a.find (Nat.div v 2)) (b.find (Nat.div v 2))
def nb (adj : Trie) (v : Nat) : List Nat := adj.find v
def maskOf : List Nat → Nat
  | [] => 0
  | x :: l => Nat.lor (Nat.shiftLeft 1 x) (maskOf l)
def branch (adj : Trie) (v x : Nat) : List Nat :=
  let ys := (nb adj x).filter (fun y => !(Nat.beq y v))
  x :: (ys ++ ys.flatMap (fun y => (nb adj y).filter (fun z => !(Nat.beq z x))))
def brMask (adj : Trie) (v x : Nat) : Nat := maskOf (branch adj v x)
def pwDisj : List Nat → Bool
  | [] => true
  | m :: ms => ms.all (fun m' => Nat.beq (Nat.land m m') 0) && pwDisj ms
def vertexOk (adj : Trie) (v : Nat) : Bool := pwDisj ((nb adj v).map (brMask adj v))
def verticesOk (adj : Trie) : Nat → Nat → Bool
  | _, 0 => true
  | lo, c + 1 => vertexOk adj lo && verticesOk adj (lo + 1) c
def nodupB : List Nat → Bool
  | [] => true
  | x :: l => !(l.contains x) && nodupB l
def wfV (adj : Trie) (n d v : Nat) : Bool :=
  Nat.beq (nb adj v).length d && nodupB (nb adj v) &&
    (nb adj v).all (fun x => Nat.blt x n && !(Nat.beq x v) && (nb adj x).contains v)
def wfOk (adj : Trie) (n d : Nat) : Bool := (List.range n).all (wfV adj n d)
end Cage87


