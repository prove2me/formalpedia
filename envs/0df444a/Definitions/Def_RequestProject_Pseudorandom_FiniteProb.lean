-- Prove2me | Definitions.Def_RequestProject_Pseudorandom_FiniteProb
-- name    : RequestProject_Pseudorandom_FiniteProb
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:29:43.032802+00:00
-- url     : https://prove2.me/theorems/5a5a94ca-2b1a-4d5a-b100-93bf5bedda46
-- title:
--   Finite Prob
-- statement:
--   Definitions and structural lemmas for Finite Prob, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/RequestProject/Pseudorandom/FiniteProb.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Pseudorandom
open Finset
section Basic
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
def IsPMF (P : ι → α → ℝ) : Prop := (∀ i a, 0 ≤ P i a) ∧ ∀ i, ∑ a, P i a = 1
def pw (P : ι → α → ℝ) (ω : ι → α) : ℝ := ∏ i, P i (ω i)
def pE (P : ι → α → ℝ) (f : (ι → α) → ℝ) : ℝ := ∑ ω, pw P ω * f ω
open Classical in
/-- Probability of an event in the product space. -/
noncomputable def pProb (P : ι → α → ℝ) (S : (ι → α) → Prop) : ℝ :=
  pE P (fun ω => if S ω then 1 else 0)
variable {P : ι → α → ℝ}
end Basic
section Transport
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]
end Transport
end Pseudorandom


