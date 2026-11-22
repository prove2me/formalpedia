-- Prove2me | Definitions.Def_RequestProject_Pseudorandom_Bernstein
-- name    : RequestProject_Pseudorandom_Bernstein
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:30:15.592434+00:00
-- url     : https://prove2.me/theorems/ededd6ae-8216-431a-bb1d-21ec0223cd3d
-- title:
--   Bernstein
-- statement:
--   Definitions and structural lemmas for Bernstein, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/Bernstein.lean

module
public import Definitions.Def_RequestProject_Pseudorandom_FiniteProb
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Pseudorandom
open Finset
section Coord
variable {α : Type*}
def CoordGap {ι : Type*} [DecidableEq ι] (f : (ι → α) → ℝ) (c : ι → ℝ) : Prop :=
  ∀ i ω a b, |f (Function.update ω i a) - f (Function.update ω i b)| ≤ c i
def CoordRare {ι : Type*} [DecidableEq ι] (f : (ι → α) → ℝ) (R : ι → Finset α) : Prop :=
  ∀ i ω a b, a ∉ R i → b ∉ R i → f (Function.update ω i a) = f (Function.update ω i b)
end Coord
section Rec
variable {α : Type*} [Fintype α]
def rmean : {n : ℕ} → (Fin n → α → ℝ) → ((Fin n → α) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | _ + 1, P, f => ∑ a, P 0 a * rmean (fun i => P i.succ) (fun ω => f (Fin.cons a ω))
end Rec
section Tail
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
end Tail
end Pseudorandom


