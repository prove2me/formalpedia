-- Prove2me | Definitions.Def_QuantumLTF_Membership_centerPhaseGate
-- name    : QuantumLTF_Membership_centerPhaseGate
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-14T20:37:32.227638+00:00
-- url     : https://prove2.me/theorems/babe430c-d704-4dbd-aadc-fe5987647947
-- title:
--   Explicit single-qubit phases for the centered-grid QFT
-- statement:
--   Write the centered grid point represented by an integer $j$ as $\hat j=j/2^b-1/2+2^{-b-1}$. Expanding $2^b\hat j\hat k$ separates it into the ordinary Fourier term $jk/2^b$ plus one affine function of $j$ and one of $k$. Since the binary value of $j$ is a weighted sum of its bits, each affine phase factors as a tensor product of diagonal one-qubit gates.
--
--   `centerPhaseGate(b,i)` is the explicit diagonal gate on bit $i$; the index-independent phase is divided equally among the $b$ wires. These gates make Lemma 3.3 a concrete matrix identity rather than an existential factorization.
--
--   **Formalization Note** The definition is used only for $i\in\operatorname{Fin}(b)$, so the apparent division by $b$ is never evaluated when $b=0$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Lemma 3.3 and Eqs. (44)–(48), p. 27 (PDF p. 28); explicit expansion of the phases in the proof

import Mathlib

namespace QuantumLTF.Membership

/-- The explicit one-qubit diagonal phase on wire `i` which converts the ordinary QFT into
the QFT on the centered grid. The constant phase is shared evenly among the `b` wires. -/
noncomputable def centerPhaseGate (b : ℕ) (i : Fin b) : Matrix Bool Bool ℂ :=
  let N : ℝ := (2 : ℝ) ^ b
  let c : ℝ := -(1 / 2) + 1 / (2 * N)
  let weight : ℝ := (2 : ℝ) ^ (b - 1 - i.1)
  let shared : ℝ := N * c ^ 2 / (2 * b)
  Matrix.of fun y z =>
    if y = z then
      Complex.exp (2 * Real.pi * Complex.I *
        ((if z then c * weight else 0) + shared))
    else 0

end QuantumLTF.Membership


