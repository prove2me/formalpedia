-- Prove2me | Definitions.Def_CSeparatedNPComplete_Definitions
-- name    : CSeparatedNPComplete_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:45:36.220817+00:00
-- url     : https://prove2.me/theorems/6ca3931d-7e56-41c9-8905-ad271ac436b4
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Definitions.lean

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace CSeparatedNPComplete
abbrev Vec (n : Nat) := Fin n → Real
abbrev Gaussian (n : Nat) := Vec n × Vec n
def dot {n : Nat} (x y : Vec n) : Real := ∑ i, x i * y i
def sqVec {n : Nat} (x : Vec n) : Vec n := fun i => x i * x i
def isCASeparated {n : Nat} (c : Real) (a : Vec n) (g : Gaussian n)
    (l : List (Gaussian n)) : Prop :=
  match g with
  | (mu, sigma) =>
      match l with
      | [] => True
      | (mu2, sigma2) :: tail =>
          c * dot a sigma ≤ dot a (sqVec (fun i => mu i - mu2 i)) ∧
          c * dot a sigma2 ≤ dot a (sqVec (fun i => mu i - mu2 i)) ∧
          isCASeparated c a g tail
def cSeparates {n : Nat} (c : Real) (a : Vec n) (l : List (Gaussian n)) : Prop :=
  match l with
  | [] => True
  | g :: tail => isCASeparated c a g tail ∧ cSeparates c a tail
def vecSum {n : Nat} (v : Vec n) : Real := ∑ i, v i
def prefixSum {n : Nat} (k : Nat) (v : Vec n) : Real :=
  ∑ i ∈ Finset.univ.filter (fun i => i.1 < k), v i
def sortedDesc {n : Nat} (v : Vec n) : Prop :=
  ∀ i j, i ≤ j → v j ≤ v i
def majorized {n : Nat} (u v : Vec n) : Prop :=
  sortedDesc u ∧
  sortedDesc v ∧
  (∀ k, prefixSum k v ≤ prefixSum k u) ∧
  vecSum u = vecSum v
def convexOnPredicate (P : Real → Prop) (f : Real → Real) : Prop :=
  ∀ x y, P x → P y → ∀ t, 0 ≤ t → t ≤ 1 →
    P (t * x + (1 - t) * y) ∧
    f (t * x + (1 - t) * y) ≤ t * f x + (1 - t) * f y
end CSeparatedNPComplete


