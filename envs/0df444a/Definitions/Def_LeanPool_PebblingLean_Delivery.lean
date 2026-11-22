-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Delivery
-- name    : LeanPool_PebblingLean_Delivery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:46:17.88257+00:00
-- url     : https://prove2.me/theorems/c7561967-1949-4118-805e-b616e904689e
-- title:
--   Delivery
-- statement:
--   Definitions and structural lemmas for Delivery, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
universe u
namespace Graph
variable {V : Type u} (G : Graph V)
inductive Walk : V → V → Type u where
  | nil (v : V) : Walk v v
  | cons {u v w : V} : G.Adj u v → Walk v w → Walk u w
namespace Walk
def length {u v : V} : G.Walk u v → ℕ
  | nil _ => 0
  | cons _ tail => tail.length + 1
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil _, tail => tail
  | cons h headTail, tail => cons h (append headTail tail)
def reverse {u v : V} : G.Walk u v → G.Walk v u
  | nil u => nil u
  | cons h tail => Graph.Walk.append G (reverse tail) (cons (G.symm h) (nil _))
end Walk
end Graph
namespace Pebbling
variable {V : Type u}
def single [DecidableEq V] (v : V) (k : ℕ) : Pebbling V :=
  fun x => if x = v then k else 0
def twoPoint [DecidableEq V] (u v : V) (ku kv : ℕ) : Pebbling V :=
  fun x => if x = u then ku else if x = v then kv else 0
end Pebbling
end PebblingLean


