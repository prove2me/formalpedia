-- Prove2me | Definitions.Def_HammingSumset729_Approximation_Strings
-- name    : HammingSumset729_Approximation_Strings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:12.278849+00:00
-- url     : https://prove2.me/theorems/19708ade-2dd1-44ba-a6df-cce0b00c61d5
-- title:
--   Strings, approximate periods, runs, trimming and rearrangement
-- statement:
--   Strings are finite lists. Substrings use a starting position and a length, including length zero; Hamming distance is used on equal-length strings. Runs count maximal nonempty constant blocks, with zero runs for the empty string. A positive period is bounded by string length. The column encoding reads residues modulo the period; run counts are summed before concatenating columns. The longest suffix and prefix satisfying the source run budget are computed from the data. The rearrangement uses two distinct fresh symbols outside the original alphabet. These are the common source concepts for the appendix lemmas.
-- source:
--   Nick Fischer, Yael Kirkpatrick, Vassilios Nakos, STOC 2027 submission #729 (October 2026), §2, printed p.3 (PDF p.5), and Appendix A, printed pp.23–24 (PDF pp.25–26). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/729.pdf

import Mathlib

set_option autoImplicit false

namespace HammingSumset729.Approximation

/-! Source §2 and Appendix A, printed pp.3,22–24 (PDF pp.5,24–26).
All substrings below use a starting position and a length, including length zero. -/
def substring {α : Type*} (s : List α) (start length : ℕ) : List α :=
  (s.drop start).take length

def distance {α : Type*} [DecidableEq α] (s t : List α) : ℕ :=
  ((s.zip t).filter fun ab => ab.1 ≠ ab.2).length

def shiftDistance {α : Type*} [DecidableEq α] (t p : List α) (i : ℕ) : ℕ :=
  distance (substring t i p.length) p

/-- Only used on valid shifts with `i + p.length ≤ t.length`. -/
def MultiplicativeApproximation {α : Type*} [DecidableEq α]
    (t p : List α) (ε : ℝ) (estimates : List ℚ) : Prop :=
  estimates.length = t.length - p.length + 1 ∧
  ∀ i : ℕ, i + p.length ≤ t.length →
    (1 - ε) * (shiftDistance t p i : ℝ) ≤ (estimates[i]?.getD 0 : ℝ) ∧
    (estimates[i]?.getD 0 : ℝ) ≤ (1 + ε) * (shiftDistance t p i : ℝ)

def runs {α : Type*} [DecidableEq α] : List α → ℕ
  | [] => 0
  | a :: rest => 1 + ((a :: rest).zip rest).countP (fun ab => ab.1 ≠ ab.2)

/-- Positive shift, bounded by the string length, including its full length. -/
def IsPeriod {α : Type*} [DecidableEq α] (s : List α) (x : ℝ) (period : ℕ) : Prop :=
  0 < period ∧ period ≤ s.length ∧
  (distance (s.drop period) (s.take (s.length - period)) : ℝ) ≤ x

def IsMinimalPeriod {α : Type*} [DecidableEq α]
    (s : List α) (x : ℝ) (period : ℕ) : Prop :=
  IsPeriod s x period ∧ ∀ q, IsPeriod s x q → period ≤ q

def column {α : Type*} (s : List α) (period residue : ℕ) : List α :=
  ((s.zipIdx).filter fun ai => ai.2 % period = residue).map Prod.fst

def columns {α : Type*} (s : List α) (period : ℕ) : List α :=
  (List.range period).flatMap (column s period)

def runsByPeriod {α : Type*} [DecidableEq α] (s : List α) (period : ℕ) : ℕ :=
  ((List.range period).map fun i => runs (column s period i)).sum

/-- Longest suffix/prefix are constructed, not arbitrary low-run witnesses. -/
def longestSuffixLength {α : Type*} [DecidableEq α] (s : List α) (period budget : ℕ) : ℕ :=
  ((List.range (s.length + 1)).filter fun len =>
    runsByPeriod (s.drop (s.length - len)) period ≤ budget).foldl max 0

def longestPrefixLength {α : Type*} [DecidableEq α] (s : List α) (period budget : ℕ) : ℕ :=
  ((List.range (s.length + 1)).filter fun len =>
    runsByPeriod (s.take len) period ≤ budget).foldl max 0

def trimmedLeft {α : Type*} [DecidableEq α] (t : List α) (m period k : ℕ) : List α :=
  let s := t.take m
  s.drop (s.length - longestSuffixLength s period (11 * k))

def trimmedRight {α : Type*} [DecidableEq α] (t : List α) (m period k : ℕ) : List α :=
  let s := (t.drop m).take m
  s.take (longestPrefixLength s period (11 * k))

/-- `Sum.inr false` is # and `Sum.inr true` is $, distinct from every input symbol. -/
def encodedText {α : Type*} (t : List α) (period : ℕ) : List (α ⊕ Bool) :=
  let s := t.map Sum.inl
  columns s period ++ columns (s.drop period ++ List.replicate period (Sum.inr false)) period

def encodedPattern {α : Type*} (p : List α) (textLength period : ℕ) : List (α ⊕ Bool) :=
  columns (p.map Sum.inl ++ List.replicate (textLength - p.length) (Sum.inr true)) period

end HammingSumset729.Approximation


