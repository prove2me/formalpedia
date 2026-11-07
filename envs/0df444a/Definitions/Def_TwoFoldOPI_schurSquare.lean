-- Prove2me | Definitions.Def_TwoFoldOPI_schurSquare
-- name    : TwoFoldOPI_schurSquare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:23.746616+00:00
-- url     : https://prove2.me/theorems/ab74f8fd-b3a3-4d5a-869b-871620bf64b9
-- title:
--   The Schur square $C^{*2}$
-- statement:
--   For a linear code $C\subseteq\mathbb F_q^M$, the Schur square is the linear span of all coordinate-wise products of two codewords:
--   $$C^{*2}=\operatorname{span}\{u\odot v: u,v\in C\},\qquad (u\odot v)_i=u_iv_i .$$
--   In the mission it is taken of the dual code $C^\perp$: the quadratic unknown of the relinearization in Lemma 7.3 lives in $(C^\perp)^{*2}$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.23, p. 26

import Mathlib

namespace TwoFoldOPI

/-- **The Schur square `C^{∗2}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.23, p.26: "For codes C_1, …, C_k ⊆ F_q^M, let C_1 ∗ ⋯ ∗ C_k ⊆ F_q^M
denote the linear subspace spanned by the coordinate-wise products c_1 ⊙ ⋯ ⊙ c_k with c_j ∈ C_j
for every j. When C_1 = ⋯ = C_k = C, we write C^{∗k}; we call C^{∗2} the Schur square of C".

**Formalization Note.** The coordinate-wise product `u ⊙ v` is the pointwise product `u * v` of
functions `Fin M → K`. -/
def schurSquare {K : Type*} [Field K] {M : ℕ} (C : Submodule K (Fin M → K)) :
    Submodule K (Fin M → K) :=
  Submodule.span K {x | ∃ u ∈ C, ∃ v ∈ C, x = u * v}

end TwoFoldOPI


