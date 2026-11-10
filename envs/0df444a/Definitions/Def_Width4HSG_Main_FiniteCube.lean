-- Prove2me | Definitions.Def_Width4HSG_Main_FiniteCube
-- name    : Width4HSG_Main_FiniteCube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:16:33.189562+00:00
-- url     : https://prove2.me/theorems/a154c2ac-d2fe-418b-9583-e28b44c3862d
-- title:
--   Finite Boolean cubes, expectation, total variation and Hamming distance
-- statement:
--   Words are Boolean functions on finite coordinate sets. Uniform expectations are normalized finite sums; arbitrary laws are Mathlib probability mass functions. Total variation is one half of the sum of absolute mass differences; Hamming distance counts unequal coordinates. The generic average helper returns zero on an empty carrier; all Boolean cubes used as sample spaces are nonempty, including the cube with zero coordinates.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 15, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

abbrev Bits (n : ℕ) := Fin n → Bool

def indicator (b : Bool) : ℝ := if b then 1 else 0

def average {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

def expectation {α : Type} [Fintype α] (D : PMF α) (f : α → ℝ) : ℝ :=
  ∑ x, (D x).toReal * f x

def totalVariation {α : Type} [Fintype α] (D E : PMF α) : ℝ :=
  (∑ x, |(D x).toReal - (E x).toReal|) / 2

def hamming {α : Type} [Fintype α] (x y : α → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x i ≠ y i)).card

end Width4HSG.Main


