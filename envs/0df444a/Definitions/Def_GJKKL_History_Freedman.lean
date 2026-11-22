-- Prove2me | Definitions.Def_GJKKL_History_Freedman
-- name    : GJKKL_History_Freedman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:31:38.446219+00:00
-- url     : https://prove2.me/theorems/3b0249b1-6390-42a8-9e19-ce08bd166af7
-- title:
--   Freedman
-- statement:
--   Definitions and structural lemmas for Freedman, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
def AliveBefore (G : List α → Prop) : List α → Prop
  | [] => True
  | a :: h => AliveBefore G h ∧ G h
variable (κ : Kernel α) (X : List α → ℝ) (G : List α → Prop)
def condAbsInc (h : List α) : ℝ := ∑ a, κ.K h a * |X (a :: h) - X h|
def accSum : List α → ℝ
  | [] => condAbsInc κ X []
  | a :: h => accSum h + condAbsInc κ X (a :: h)
open Classical in
/-- The process stopped at the first bad time. -/
noncomputable def stopped : List α → ℝ
  | [] => X []
  | a :: h => if AliveBefore G (a :: h) then X (a :: h) else stopped h
open Classical in
/-- The accumulated conditional absolute increments of the stopped process. -/
noncomputable def accInc : List α → ℝ
  | [] => 0
  | a :: h => if AliveBefore G (a :: h) then accInc h + condAbsInc κ X h else accInc h
end GJKKL.History


