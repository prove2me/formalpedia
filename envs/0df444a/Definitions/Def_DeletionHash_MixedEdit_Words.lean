-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Words
-- name    : DeletionHash_MixedEdit_Words
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:15.87625+00:00
-- url     : https://prove2.me/theorems/eae0a3ee-ec34-4970-b4c0-c1d6a24dde20
-- title:
--   Finite words and valid substring windows
-- statement:
--   A word is a finite ordered list of letters from an alphabet $\alpha$. A fixed-length word of length $n$ is represented by its $n$ indexed letters; its ordered list is recovered without padding. A valid length-$j$ window begins at a nonnegative position $i$ satisfying $i+j\le |y|$ and is the half-open substring $y[i:i+j)$. The list of windows retains every valid start, in order. In particular, a word shorter than $j$ has no such windows. These operations supply the shared word representation for the channel and its spectra.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §1.1, words, printed p. 1 (PDF p. 3); §2.2, zero-based half-open windows, printed p. 6 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Mathlib

namespace DeletionHash.MixedEdit

universe u

/-- Length-n words, with their actual ordered list of letters. -/
abbrev Word (α : Type u) (n : ℕ) := Fin n → α

def letters {α : Type u} {n : ℕ} (x : Word α n) : List α := List.ofFn x

/-- Half-open window [i,i+j); callers explicitly require i+j ≤ length. -/
def window {α : Type u} (j : ℕ) (y : List α) (i : ℕ) : List α := (y.drop i).take j

/-- Invalid windows are excluded, including when the word is shorter than j. -/
def starts {α : Type u} (j : ℕ) (y : List α) : List ℕ :=
  List.range (if j ≤ y.length then y.length - j + 1 else 0)

def windows {α : Type u} (j : ℕ) (y : List α) : List (List α) :=
  (starts j y).map (window j y)

end DeletionHash.MixedEdit


