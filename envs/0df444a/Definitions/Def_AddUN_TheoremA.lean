-- Prove2me | Definitions.Def_AddUN_TheoremA
-- name    : AddUN_TheoremA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:25:00.933011+00:00
-- url     : https://prove2.me/theorems/87a850c7-2b73-4207-bb3b-c0c9a183c960
-- title:
--   Theorem A
-- statement:
--   Definitions and structural lemmas for Theorem A, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/TheoremA.lean

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
namespace AddUN
def inner (U : Set (ℕ → Bool)) (n : ℕ) : Set (ℕ → Bool) :=
  {x | cylinderOn (Finset.range n) x ⊆ U}
variable {U : Set (ℕ → Bool)}
def layer (U : Set (ℕ → Bool)) (M : ℕ → ℕ) : ℕ → Set (ℕ → Bool)
  | 0 => inner U (M 0)
  | k + 1 => inner U (M (k + 1)) \ inner U (M k)
def spread (g : ℕ → ℕ) (k₀ k : ℕ) : ℕ := Nat.pair k (g (k + k₀))
def overwrite (h : ℕ → ℕ) (c u : ℕ → Bool) (i : ℕ) : Bool :=
  if h (Nat.unpair i).1 = i then c (Nat.unpair i).1 else u i
end AddUN


