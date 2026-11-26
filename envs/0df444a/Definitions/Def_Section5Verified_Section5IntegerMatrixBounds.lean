-- Prove2me | Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
-- name    : Section5Verified_Section5IntegerMatrixBounds
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:49.067386+00:00
-- url     : https://prove2.me/theorems/0094ce44-6d70-4557-a4bb-872d7cef1186
-- title:
--   Section5IntegerMatrixBounds — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5IntegerMatrixBounds; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-! Explicit bit-growth bounds for the exact arithmetic in the power estimator. -/

structure Section5IntegerMatrix (n : ℕ) where
  re : Matrix (Fin n) (Fin n) ℤ
  im : Matrix (Fin n) (Fin n) ℤ

def Section5IntegerMatrix.mul {n : ℕ} (A B : Section5IntegerMatrix n) : Section5IntegerMatrix n :=
  ⟨A.re*B.re-A.im*B.im,A.re*B.im+A.im*B.re⟩

def Section5IntegerMatrix.one (n : ℕ) : Section5IntegerMatrix n := ⟨1,0⟩

def Section5IntegerMatrix.power {n : ℕ} (A : Section5IntegerMatrix n) : ℕ → Section5IntegerMatrix n
  | 0 => .one n
  | k+1 => (A.power k).mul A

def Section5IntegerMatrix.Bounded {n : ℕ} (A : Section5IntegerMatrix n) (B : ℤ) : Prop :=
  (∀ i j, |A.re i j| ≤ B) ∧ ∀ i j, |A.im i j| ≤ B







end


