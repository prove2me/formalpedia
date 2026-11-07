-- Prove2me | Definitions.Def_TwoFoldOPI_shiftOp
-- name    : TwoFoldOPI_shiftOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:24.741519+00:00
-- url     : https://prove2.me/theorems/35730dc4-7477-49ee-9c4f-44d904b803b4
-- title:
--   The shift $X^c$
-- statement:
--   For $c\in\mathbb F_q^M$, $X^c$ is the permutation unitary on $\mathbb C^{\mathbb F_q^M}$ with
--   $$X^c|x\rangle=|x+c\rangle .$$
--   It shifts the error state of the quantum decoding problem by the hidden codeword.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5, Notation, p. 20

import Mathlib

namespace TwoFoldOPI

/-- **The shift `X^c`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5, Notation, p.20: "For c ∈ F_q^M, X^c denotes the unitary |x⟩ ↦ |x + c⟩."

The matrix entry in row `x'`, column `x` is `1` if `x' = x + c` and `0` otherwise. -/
def shiftOp {K : Type*} [AddGroup K] [DecidableEq K] {M : ℕ} (c : Fin M → K) :
    Matrix (Fin M → K) (Fin M → K) ℂ :=
  Matrix.of fun x' x => if x' = x + c then 1 else 0

end TwoFoldOPI


