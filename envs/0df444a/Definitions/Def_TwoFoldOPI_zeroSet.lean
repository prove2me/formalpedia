-- Prove2me | Definitions.Def_TwoFoldOPI_zeroSet
-- name    : TwoFoldOPI_zeroSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:19.791875+00:00
-- url     : https://prove2.me/theorems/6ccb996b-c934-4fd0-a4bd-c07522ee3be8
-- title:
--   The zero set $Z(v)$
-- statement:
--   For a vector $v\in\mathbb F_q^M$, its zero set is
--   $$Z(v)=\{i\in[M]: v_i=0\}.$$
--   It indexes the coordinates at which the shortened Schur square is taken in the failure bound of Lemma 7.3 and Theorem 7.4.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.18, p. 25

import Mathlib

namespace TwoFoldOPI

/-- **The zero set `Z(v)`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.18, p.25: "For a vector v ∈ F_q^M, let Z(v) ⊆ [M] be the set of indices
i with v_i = 0." -/
def zeroSet {K : Type*} [Zero K] [DecidableEq K] {M : ℕ} (v : Fin M → K) : Finset (Fin M) :=
  Finset.univ.filter fun i => v i = 0

end TwoFoldOPI


