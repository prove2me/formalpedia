-- Prove2me | Definitions.Def_HighDimProb_RandomMatrices_hammingDist
-- name    : HighDimProb_RandomMatrices_hammingDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:50.375985+00:00
-- url     : https://prove2.me/theorems/d74c4ebb-4584-43dd-a822-25eea695af46
-- title:
--   Hamming distance on the Hamming cube
-- statement:
--   This is **Definition 4.2.14** (Hamming cube): the metric error-correcting codes (Theorem
--   4.3.5) are stated against.
--
--   The Hamming cube $\{0,1\}^n$ consists of binary strings of length $n$, here represented as
--   functions $\mathrm{Fin}\ n \to \mathrm{Bool}$. The **Hamming distance** between two strings
--   $x, y \in \{0,1\}^n$ is the number of coordinates where they disagree:
--
--   $$
--   d_H(x, y) \;:=\; \#\{\, i : x(i) \ne y(i) \,\}.
--   $$
--
--   **Formalization Note** Cardinality of the mismatch set is computed as a `Finset.card` over
--   `Fin n` (always finite, so no junk-value convention is involved).
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 4.2.14, p. 85 (PDF p. 93)

import Mathlib

namespace HighDimProb.RandomMatrices

/-- **Definition 4.2.14** (Hamming cube), Vershynin, *High-Dimensional Probability* (2018),
p. 85: the Hamming distance between two binary strings `x, y ∈ {0,1}ⁿ` is the number of bits
where they disagree. Binary strings of length `n` are represented as `Fin n → Bool`. -/
def hammingDist {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

end HighDimProb.RandomMatrices


