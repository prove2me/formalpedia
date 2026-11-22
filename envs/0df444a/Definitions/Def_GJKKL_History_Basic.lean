-- Prove2me | Definitions.Def_GJKKL_History_Basic
-- name    : GJKKL_History_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:29:10.932142+00:00
-- url     : https://prove2.me/theorems/06c1883f-5715-49a1-9312-aeccf6166844
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Basic.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (α) in
/-- The histories of length `T`. -/
def hist : ℕ → Finset (List α)
  | 0 => {[]}
  | T + 1 => (univ ×ˢ hist T).image (fun p => p.1 :: p.2)
variable (α) in
/-- A history-dependent sub-probability transition law. -/
structure Kernel where
  /-- `K h a` is the probability of choosing `a` after the history `h`. -/
  K : List α → α → ℝ
  nonneg : ∀ h a, 0 ≤ K h a
  mass_le : ∀ h, ∑ a, K h a ≤ 1
variable (κ : Kernel α)
def weight : List α → ℝ
  | [] => 1
  | a :: h => weight h * κ.K h a
def expect (T : ℕ) (f : List α → ℝ) : ℝ := ∑ h ∈ hist α T, weight κ h * f h
open Classical in
/-- The probability of an event about the history at time `T`. -/
noncomputable def prob (T : ℕ) (P : List α → Prop) : ℝ :=
  expect κ T (fun h => if P h then 1 else 0)
end GJKKL.History


