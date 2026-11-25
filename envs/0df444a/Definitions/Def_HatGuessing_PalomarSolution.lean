-- Prove2me | Definitions.Def_HatGuessing_PalomarSolution
-- name    : HatGuessing_PalomarSolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:14:18.056744+00:00
-- url     : https://prove2.me/theorems/d5287c04-615d-4193-a379-e1a8384a0595
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/palomar/Solution.lean

import Definitions.Def_HatAffineFullTheorem_GeneralNoGo
set_option autoImplicit true
open scoped BigOperators
namespace OneSidedAffineHatGuessing
universe u v w
def Wins {K : Type u} {I : Type v} {J : Type w}
    (F : (J → K) → I → K)
    (G : (I → K) → J → K) : Prop :=
  ∀ x y,
    (∃ i, F y i = x i) ∨
    (∃ j, G x j = y j)
def Extends {K : Type u} {I : Type v} {J : Type w}
    (F : (J → K) → I → K) : Prop :=
  ∃ G : (I → K) → J → K, Wins F G
def AffineHalf {K : Type u} {I : Type v} {J : Type w}
    [Semiring K] [Fintype J]
    (F : (J → K) → I → K) : Prop :=
  ∃ A : I → J → K, ∃ b : I → K,
    ∀ y i, F y i = (∑ j, A i j * y j) + b i
def GeneralNoGoStatement : Prop :=
  ∀ (K : Type u) [Field K] [Fintype K] (m : ℕ),
    4 ≤ Fintype.card K →
    1 ≤ m →
    ∀ F : (Fin m → K) → Fin (Fintype.card K - 1) → K,
      AffineHalf F → ¬ Extends F
end OneSidedAffineHatGuessing


