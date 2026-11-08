-- Prove2me | Definitions.Def_AffDisp4n_vecWord
-- name    : AffDisp4n_vecWord
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:32.091392+00:00
-- url     : https://prove2.me/theorems/4834627a-ae6e-402b-a469-aad30170448b
-- title:
--   Words of numbers, vectors, matrices and pairs
-- statement:
--   A vector over $\mathbb F_2$ is written as the word of its bits, a matrix as one word per row, a number in unary, and a set of pairs as its table of membership bits, one word per row. Lists of these words go on the machine's tape through the published `LowErrExt.encWords`, which follows each word by a separator. They are the machine inputs and outputs of the running-time clauses.
--
--   **Formalization Note** The paper fixes no encoding. It stores "$\Phi$ through the vector $b$ and the matrix $L$, and the set $P$ as a list of all pairs" (p.26). Every number written is a dimension or an index below one, so unary and binary differ by a polynomial.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), Lemma 2.2, p.17; Lemma 4.2, p.21; Theorem 4.1, p.21; proof p.26

import Mathlib

namespace AffDisp4n

/-- The **vector over `𝔽₂` as a word of its bits**, for the machine inputs and outputs of the running-time
clauses (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), Lemma 2.2, p.17; Lemma 4.2, p.21; Theorem 4.1, p.21: "in polynomial time"). Lists of such words go on
the machine's tape through the published `LowErrExt.encWords` (each word followed by a separator).

**Formalization Note** The paper fixes no encoding ("We store Φ through the vector b and the matrix L, and
the set P as a list of all pairs", p.26). The helpers below write the page's data. -/
def vecWord {k : ℕ} (v : Fin k → ZMod 2) : List Bool := List.ofFn fun i => decide (v i = 1)

/-- A natural number written in unary. Every number in the encodings below is a dimension or an index
below a dimension, and the matrices of those dimensions are written out in full, so unary and binary
differ by a polynomial. -/
def natWord (k : ℕ) : List Bool := List.replicate k true

/-- An element of `𝔽₂` as a bit. -/
def bitOf (c : ZMod 2) : Bool := decide (c = 1)

/-- A matrix over `𝔽₂`, one word per row. -/
def matWords {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 2)) : List (List Bool) :=
  List.ofFn fun i => vecWord (M i)

/-- A set of pairs of parameters as its `m × m` table of membership bits, one word per row. -/
def pairsWords {m : ℕ} (P : Finset (Sym2 (Fin m))) : List (List Bool) :=
  List.ofFn fun p : Fin m => List.ofFn fun r : Fin m => decide (s(p, r) ∈ P)

end AffDisp4n


