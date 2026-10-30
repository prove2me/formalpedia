-- Prove2me | Definitions.Def_OnlineCRS_Combine_encVec
-- name    : OnlineCRS_Combine_encVec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:21:48.030514+00:00
-- url     : https://prove2.me/theorems/bdd4b9e8-8b53-495c-88bc-b21364b2b4ee
-- title:
--   Encoding of a rational vector $x\in\mathbb Q^k$
-- statement:
--   A vector $x=(x_0,\dots,x_{k-1})\in\mathbb Q^k$ is encoded as the concatenation of the encodings of $x_0,\dots,x_{k-1}$, each followed by the separator $3$. It is the encoding of the input $x$ of the sampling algorithm of Definition 1.7.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`). Inputs are rational because an algorithm's input is finite.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

namespace OnlineCRS.Combine

/-- **Encoding of a rational vector `x ∈ ℚ^k`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4 (efficiency): the input `x` of the sampling algorithm.

`encVec x` lists `encRat (x j)` for `j = 0, …, k − 1`, each followed by the separator `3`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. Rational coordinates: an algorithm's input is finite. -/
def encVec {k : ℕ} (x : Fin k → ℚ) : List Sym :=
  (List.finRange k).flatMap fun j => encRat (x j) ++ [3]

end OnlineCRS.Combine


