-- Prove2me | Definitions.Def_RequestProject_Pseudorandom_Defs
-- name    : RequestProject_Pseudorandom_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:29:44.334554+00:00
-- url     : https://prove2.me/theorems/4560b642-709a-4c7e-91d7-af82226732a0
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Pseudorandom
open Finset
variable {V : Type*} [DecidableEq V]
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card
def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card
def IsMatching (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f
def weight (ω : Finset V → ℝ) (X : Finset (Finset V)) : ℝ := ∑ e ∈ X, ω e
end Pseudorandom


