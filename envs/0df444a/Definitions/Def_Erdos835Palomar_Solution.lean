-- Prove2me | Definitions.Def_Erdos835Palomar_Solution
-- name    : Erdos835Palomar_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:07:18.160104+00:00
-- url     : https://prove2.me/theorems/f51b985c-5f7a-48ba-a835-8a11bf2fe0bf
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Matt Stokes (stokes/erdos835-palomar; definitions and statements reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 835: chromatic number of Johnson graph J(2k, k) for composite k+1 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace Erdos835Palomar
@[simps -isSimp]
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual
@[inherit_doc] scoped notation "J(" n ", " k ")" => johnson n k
abbrev Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
end Erdos835Palomar


